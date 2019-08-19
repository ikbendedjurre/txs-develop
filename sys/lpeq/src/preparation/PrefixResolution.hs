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
resolveProcPrefixesInBody,
resolveProcPrefixes
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified Subst
import qualified ProcId
import qualified ProcDef
import qualified ChanId
import qualified VarId
import BehExprDefs
import ProcIdFactory
-- import ValFactory
import UntilFixedPoint
import ProcDepTree
import BranchUtils

data BranchVerdict = BVStop | BVDone | BVWrongPrefix deriving (Eq, Ord, Show)

resolvePrefixes :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
resolvePrefixes bexpr = do
    procDepTree <- getProcDepTree bexpr
    let orderedProcs = getProcsOrderedByMaxDepth procDepTree
    Monad.mapM_ resolveProcPrefixes orderedProcs
    return bexpr
-- resolvePrefixes

resolveProcPrefixes :: ProcId.ProcId -> IOC.IOC ()
resolveProcPrefixes pid = do
    -- IOC.putInfo [ "resolveProcPrefixes " ++ TxsShow.fshow pid ]
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          -- let stopValues = Map.singleton pc (cstrInt (-1))
          body' <- resolveProcPrefixesInBody pid cidDecls vidDecls body
          registerProc pid (ProcDef.ProcDef cidDecls vidDecls body')
      -- Just _ -> error ("Process does not have a program counter (\"" ++ show pid ++ "\")!")
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
-- resolveProcPrefixes

resolveProcPrefixesInBody :: ProcId.ProcId -> [ChanId.ChanId] -> [VarId.VarId] -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
resolveProcPrefixesInBody pid cidDecls vidDecls body = do
    let branchesWithVerdicts = Set.map addBranchVerdict (getBranches body)
    let f cs = let combined = [ combineChoices pid cidDecls vidDecls c1 c2 | (c1, v1) <- Set.toList cs, (c2, _) <- Set.toList cs, v1 == BVWrongPrefix ] in
                 (Set.union cs (Set.fromList combined))
    let branchesWithVerdicts' = Set.filter ((BVDone ==) . snd) (untilFixedPoint f branchesWithVerdicts)
    return (choice (Set.map fst branchesWithVerdicts'))
-- resolveProcPrefixesInBody

-- Stop:
--  - (Hide =>) (Guard =>) Stop
-- Wrong:
--  - (Hide =>) Guard => ProcInst
-- Done:
--  - (Hide =>) ActionPref => ProcInst
--  - (Hide =>) Guard => Parallel/...
addBranchVerdict :: TxsDefs.BExpr -> (TxsDefs.BExpr, BranchVerdict)
addBranchVerdict currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide _cidSet bexpr) -> (currentBExpr, getInnerExprVerdict bexpr)
      _ -> (currentBExpr, getInnerExprVerdict currentBExpr)
  where
    getInnerExprVerdict :: TxsDefs.BExpr -> BranchVerdict
    getInnerExprVerdict innerExpr =
        if isStop innerExpr
        then BVStop
        else case innerExpr of
               (TxsDefs.view -> ActionPref _actOffer bexpr) ->
                   case bexpr of
                     (TxsDefs.view -> ProcInst {}) -> BVDone
                     _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
               (TxsDefs.view -> Guard _g bexpr) ->
                   case bexpr of
                     (TxsDefs.view -> ProcInst {}) -> BVWrongPrefix
                     (TxsDefs.view -> Parallel {}) -> BVDone
                     (TxsDefs.view -> Enable {}) -> BVDone
                     (TxsDefs.view -> Disable {}) -> BVDone
                     (TxsDefs.view -> Interrupt {}) -> BVDone
                     _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
               _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
    -- getInnerExprVerdict
-- addBranchVerdict

combineChoices :: ProcId.ProcId -> [ChanId.ChanId] -> [VarId.VarId] -> TxsDefs.BExpr -> TxsDefs.BExpr -> (TxsDefs.BExpr, BranchVerdict)
combineChoices _pid _cidDecls vidDecls wrongChoice otherChoice =
    let (wcBExpr, wcHiddenChanSet) = removeHide wrongChoice in
    let (ocBExpr, ocHiddenChanSet) = removeHide otherChoice in
    let hiddenChanSet = Set.union wcHiddenChanSet ocHiddenChanSet in
      addBranchVerdict (applyHide hiddenChanSet (combineNonHideChoices wcBExpr ocBExpr))
  where
    combineNonHideChoices :: TxsDefs.BExpr -> TxsDefs.BExpr -> TxsDefs.BExpr
    combineNonHideChoices wcBExpr ocBExpr =
        -- A wrong choice looks like Guard => ProcInst; first, we break the expression down:
        case wcBExpr of
          (TxsDefs.view -> Guard wcGuard wcProcInst) ->
              case wcProcInst of
                (TxsDefs.view -> ProcInst _wcPid _wcCids wcVExprs) ->
                    -- The wrong choice will come before the other choice, so
                    -- we apply the ParamEqs of the wrong choice to the other choice:
                    let ocBExpr' = Subst.subst (Map.fromList (zip vidDecls wcVExprs)) Map.empty ocBExpr in
                      
                      -- We break the other choice down:
                      case ocBExpr' of
                        -- ActionPref => ProcInst
                        (TxsDefs.view -> ActionPref ocActOffer ocProcInst) ->
                            let newConstraint = ValExpr.cstrAnd (Set.fromList [wcGuard, TxsDefs.constraint ocActOffer]) in
                            let ocActOffer' = ocActOffer { TxsDefs.constraint = newConstraint } in
                              actionPref ocActOffer' ocProcInst
                        -- Guard => Parallel/...:
                        (TxsDefs.view -> Guard ocGuard ocGuardedBExpr) ->
                            let ocGuard' = ValExpr.cstrAnd (Set.fromList [wcGuard, ocGuard]) in
                              guard ocGuard' ocGuardedBExpr
                        -- Through the substitution from before, the Guard of the other choice may have disappeared (because it is always true/false).
                        -- We must not forget to add the Guard from the wrong choice in such cases:
                        _ -> guard wcGuard ocBExpr'
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow wrongChoice ++ "\"; " ++ show wrongChoice ++ ")!")
          _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow wrongChoice ++ "\"; " ++ show wrongChoice ++ ")!")
    -- combineNonHideChoices
-- combineChoices















