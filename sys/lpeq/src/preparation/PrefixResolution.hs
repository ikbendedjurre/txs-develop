{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  PrefixResolution
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module PrefixResolution (
resolvePrefixes,
resolveProcPrefixes
) where

import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified ProcId
import qualified Subst
import qualified ProcDef
import qualified ChanId
import qualified VarId
import qualified Constant
import BehExprDefs
import ProcIdFactory
import UntilFixedPoint
import ProcDepTree

resolvePrefixes :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
resolvePrefixes bexpr = do
    procDepTree <- getProcDepTree bexpr
    let orderedProcs = getProcsOrderedByMaxDepth procDepTree
    Monad.mapM_ resolveProcPrefixes orderedProcs
    return bexpr
-- resolvePrefixes

resolveProcPrefixes :: ProcId.ProcId -> IOC.IOC ()
resolveProcPrefixes pid = do
    IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("resolveProcPrefixes " ++ (Text.unpack (ProcId.name pid))) ]
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          let (wrong, done) = partitionChoices body
          let f = \(w, d) -> let combined = [ combineChoices pid cidDecls vidDecls c1 c2 | c1 <- Set.toList w, c2 <- Set.toList (Set.union w d) ] in
                               (Set.union w (Set.fromList (Either.lefts combined)), Set.union d (Set.fromList (Either.rights combined)))
          let (_, done') = untilFixedPoint f (wrong, done)
          registerProc pid (ProcDef.ProcDef cidDecls vidDecls (choice done'))
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
-- resolveProcPrefixes

partitionChoices :: TxsDefs.BExpr -> (Set.Set TxsDefs.BExpr, Set.Set TxsDefs.BExpr)
partitionChoices currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Choice bexprs) ->
          let mapped = map partitionChoices (Set.toList bexprs) in
            (Set.unions (map fst mapped), Set.unions (map snd mapped))
      _ -> if hasWrongPrefix currentBExpr
           then (Set.singleton currentBExpr, Set.empty)
           else (Set.empty, Set.singleton currentBExpr)
-- partitionChoices

-- Wrong:
--  - (Hide =>) Guard => ProcInst
-- Done:
--  - (Hide =>) ActionPref => ProcInst
--  - (Hide =>) Guard => Parallel/...
hasWrongPrefix :: TxsDefs.BExpr -> Bool
hasWrongPrefix currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide _cidSet bexpr) -> checkInnerExpr bexpr
      _ -> checkInnerExpr currentBExpr
  where
    checkInnerExpr :: TxsDefs.BExpr -> Bool
    checkInnerExpr innerExpr =
        case innerExpr of
          (TxsDefs.view -> ActionPref _actOffer bexpr) ->
              case bexpr of
                (TxsDefs.view -> ProcInst {}) -> False
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
          (TxsDefs.view -> Guard _g bexpr) ->
              case bexpr of
                (TxsDefs.view -> ProcInst {}) -> True
                (TxsDefs.view -> Parallel {}) -> False
                (TxsDefs.view -> Enable {}) -> False
                (TxsDefs.view -> Disable {}) -> False
                (TxsDefs.view -> Interrupt {}) -> False
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
          _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
    -- checkInnerExpr
-- hasWrongPrefix

combineChoices :: ProcId.ProcId -> [ChanId.ChanId] -> [VarId.VarId] -> TxsDefs.BExpr -> TxsDefs.BExpr -> Either TxsDefs.BExpr TxsDefs.BExpr
combineChoices pid _ [] _ _ = error ("Process without program counter found (\"" ++ show pid ++ "\")!")
combineChoices pid cidDecls (seqPC:vidDecls) wrongChoice otherChoice =
    let (wcBExpr, wcHiddenChanSet) = removeHide wrongChoice in
    let (ocBExpr, ocHiddenChanSet) = removeHide otherChoice in
      applyHide (Set.union wcHiddenChanSet ocHiddenChanSet) (combineNonHideChoices wcBExpr ocBExpr)
  where
    removeHide :: TxsDefs.BExpr -> (TxsDefs.BExpr, Set.Set ChanId.ChanId)
    removeHide (TxsDefs.view -> Hide cidSet bexpr) = (bexpr, cidSet)
    removeHide bexpr = (bexpr, Set.empty)
    
    applyHide :: Set.Set ChanId.ChanId -> Either TxsDefs.BExpr TxsDefs.BExpr -> Either TxsDefs.BExpr TxsDefs.BExpr
    applyHide hiddenChanSet (Left bexpr) =
        if Set.null hiddenChanSet
        then Left bexpr
        else Left (hide hiddenChanSet bexpr)
    applyHide hiddenChanSet (Right bexpr) =
        if Set.null hiddenChanSet
        then Right bexpr
        else Right (hide hiddenChanSet bexpr)
    -- applyHide
    
    combineNonHideChoices :: TxsDefs.BExpr -> TxsDefs.BExpr -> Either TxsDefs.BExpr TxsDefs.BExpr
    combineNonHideChoices wcBExpr ocBExpr =
        case wcBExpr of
          (TxsDefs.view -> Guard wcGuard wcProcInst) ->
              case wcProcInst of
                (TxsDefs.view -> ProcInst _wcPid _wcCids wcVExprs) ->
                    let wcSubst = Subst.subst (Map.fromList (zip (seqPC:vidDecls) wcVExprs)) Map.empty in
                      case wcSubst ocBExpr of
                        (TxsDefs.view -> ActionPref ocActOffer ocProcInst) ->
                            let ocActOffer' = ocActOffer { TxsDefs.constraint = ValExpr.cstrAnd (Set.fromList [wcGuard, TxsDefs.constraint ocActOffer]) } in
                              Right (actionPref ocActOffer' ocProcInst)
                        (TxsDefs.view -> Guard ocGuard ocGuardedBExpr) ->
                            let ocGuard' = ValExpr.cstrAnd (Set.fromList [wcGuard, ocGuard]) in
                              Left (guard ocGuard' ocGuardedBExpr)
                        -- Through substitution, a Guard may have disappeared (because it is always true) or
                        -- replaced by Stop (because it is always false):
                        ocOther -> if isStop ocOther
                                   then Left (guard wcGuard (procInst pid cidDecls (ValExpr.cstrConst (Constant.Cint (-1)):map ValExpr.cstrVar vidDecls)))
                                   else Left (guard wcGuard ocOther)
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow wrongChoice ++ "\"; " ++ show wrongChoice ++ ")!")
          _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow wrongChoice ++ "\"; " ++ show wrongChoice ++ ")!")
    -- combineNonHideChoices
-- combineChoices
