{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEContextIds
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module LPEContextIds (
getModelIds,
getProcessIds,
getSummandIds,
getValExprIds
) where

--import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified StdTDefs (stdTDefs)
import qualified CstrId
import qualified CstrDef
import qualified FuncId
import qualified SortOf
import qualified ChanId
import qualified FuncDef
import qualified VarId
import qualified Id
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           ValExprVisitor
import           LPETypeDefs

stdIds :: Set.Set TxsDefs.Ident
stdIds = Set.fromList (map fst StdTDefs.stdTDefs)

-- Because Set.unions does not work on sets of sets for some reason?
setUnions :: (Foldable f, Ord a) => f (Set.Set a) -> Set.Set a
setUnions = foldl Set.union Set.empty

getModelIds :: LPEModel -> Set.Set TxsDefs.Ident
getModelIds (tdefs, _, process) =
    untilFixpoint (getProcessIds process)
  where
    untilFixpoint :: Set.Set TxsDefs.Ident -> Set.Set TxsDefs.Ident
    untilFixpoint currentIds =
      let nextIds = getNextIds currentIds Set.\\ stdIds in
        if nextIds == currentIds
        then currentIds
        else untilFixpoint nextIds
    -- untilFixpoint
    
    getNextIds :: Set.Set TxsDefs.Ident -> Set.Set TxsDefs.Ident
    getNextIds currentIds =
        let recursiveIds = setUnions (Set.map getRecursiveIds currentIds) in
          Set.union currentIds recursiveIds
    -- getNextIds
    
    getRecursiveIds :: TxsDefs.Ident -> Set.Set TxsDefs.Ident
    getRecursiveIds (TxsDefs.IdCstr cid) =
        let allCidCstrs = Map.filterWithKey (\k _ -> CstrId.cstrsort k == CstrId.cstrsort cid) (TxsDefs.cstrDefs tdefs) in
        let allCstrIds = Set.unions (map getCstrIds (Map.keys allCidCstrs)) in
        let allAccessorIds = Set.unions (Map.elems (Map.mapWithKey getAccessorIdsFromCstrDef allCidCstrs)) in
          Set.union allCstrIds allAccessorIds
    getRecursiveIds (TxsDefs.IdFunc fid) =
        case TxsDefs.funcDefs tdefs Map.!? fid of
          Just (FuncDef.FuncDef params body) -> Set.union (getVarsIds params) (getValExprIds body)
          Nothing -> Set.empty
    getRecursiveIds _ = Set.empty
-- getModelIds

-- Gathers all ids that are used in the given LPE process:
getProcessIds :: LPEProcess -> Set.Set TxsDefs.Ident
getProcessIds (_, channels, initParamEqs, summands) =
    Set.unions [
      getChansIds channels,
      getParamEqsIds initParamEqs,
      setUnions (Set.map getSummandIds summands)
    ] Set.\\ stdIds
-- getProcessIds

-- Gathers all ids that are used in the given summand:
getSummandIds :: LPESummand -> Set.Set TxsDefs.Ident
getSummandIds (LPESummand channelVars channelOffers guard paramEqs) =
    Set.unions [
      getVarsIds channelVars,
      getChansIds (map fst channelOffers),
      Set.unions (map (getVarsIds . snd) channelOffers),
      getValExprIds guard,
      getParamEqsIds paramEqs
    ] Set.\\ stdIds
-- getSummandIds

getParamEqsIds :: LPEParamEqs -> Set.Set TxsDefs.Ident
getParamEqsIds =
    Set.unions . Map.elems . Map.mapWithKey getParamEqIds
  where
    getParamEqIds :: VarId.VarId -> TxsDefs.VExpr -> Set.Set TxsDefs.Ident
    getParamEqIds var expr = Set.union (getVarIds var) (getValExprIds expr)
-- getParamEqsIds

-- Gathers all ids that are used in the given data expression:
getValExprIds :: TxsDefs.VExpr -> Set.Set TxsDefs.Ident
getValExprIds = customData . visitValExpr searchVisitor
  where
    searchVisitor :: [ValExprVisitorOutput (Set.Set TxsDefs.Ident)] -> TxsDefs.VExpr -> ValExprVisitorOutput (Set.Set TxsDefs.Ident)
    searchVisitor subExps expr =
        let idsInSubExps = Set.unions (map customData subExps) in
        let ids = case expr of
                    (view -> Vconst (Cbool _))        -> idsInSubExps
                    (view -> Vconst (Cint _))         -> idsInSubExps
                    (view -> Vconst (Cstring _))      -> idsInSubExps
                    (view -> Vconst (Cregex _))       -> idsInSubExps
                    (view -> Vconst (Ccstr cid _))    -> Set.union (getCstrIds cid) idsInSubExps
                    (view -> Vconst (Cany sid))       -> Set.insert (TxsDefs.IdSort sid) idsInSubExps
                    (view -> Vvar vid)                -> Set.insert (TxsDefs.IdVar vid) idsInSubExps
                    (view -> Vfunc fid _)             -> Set.insert (TxsDefs.IdFunc fid) idsInSubExps
                    (view -> Vcstr cid _)             -> Set.union (getCstrIds cid) idsInSubExps
                    (view -> Viscstr cid _)           -> Set.union (getCstrIds cid) idsInSubExps
                    (view -> Vaccess cid n p _)       -> Set.unions [getCstrIds cid, getAccessorIds cid n p, idsInSubExps]
                    (view -> Vite {})                 -> idsInSubExps
                    (view -> Vdivide _ _)             -> idsInSubExps
                    (view -> Vmodulo _ _)             -> idsInSubExps
                    (view -> Vgez _)                  -> idsInSubExps
                    (view -> Vsum _)                  -> idsInSubExps
                    (view -> Vproduct _)              -> idsInSubExps
                    (view -> Vequal _ _)              -> idsInSubExps
                    (view -> Vand _)                  -> idsInSubExps
                    (view -> Vnot _)                  -> idsInSubExps
                    (view -> Vlength _)               -> idsInSubExps
                    (view -> Vat _ _)                 -> idsInSubExps
                    (view -> Vconcat _)               -> idsInSubExps
                    (view -> Vstrinre _ _)            -> idsInSubExps
                    (view -> Vpredef _ fid _)         -> Set.insert (TxsDefs.IdFunc fid) idsInSubExps
                    _                                 -> error ("GetValExprIds.searchVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 (ids Set.\\ stdIds)
    -- searchVisitor
-- getValExprIds

getCstrIds :: CstrId.CstrId -> Set.Set TxsDefs.Ident
getCstrIds cid =
    Set.fromList (TxsDefs.IdCstr cid : TxsDefs.IdSort (CstrId.cstrsort cid) : map TxsDefs.IdSort (CstrId.cstrargs cid))
-- getCstrIds

getAccessorIdsFromCstrDef :: CstrId.CstrId -> CstrDef.CstrDef -> Set.Set TxsDefs.Ident
getAccessorIdsFromCstrDef cid (CstrDef.CstrDef _recognizer accessors) =
    Set.unions (map (\(acc, p) -> getAccessorIds cid (FuncId.name acc) p) (zip accessors [0..]))
-- getAccessorIdsFromCstrDef

getAccessorIds :: CstrId.CstrId -> Text.Text -> Int -> Set.Set TxsDefs.Ident
getAccessorIds cid n p =
    let accSort = CstrId.cstrargs cid !! p in
      Set.fromList [TxsDefs.IdFunc (FuncId.FuncId n (Id.Id 0) [CstrId.cstrsort cid] accSort), TxsDefs.IdSort accSort]
-- createAccessorIds

getChansIds :: [ChanId.ChanId] -> Set.Set TxsDefs.Ident
getChansIds = Set.unions . map getChanIds

getChanIds :: ChanId.ChanId -> Set.Set TxsDefs.Ident
getChanIds chan = Set.fromList (TxsDefs.IdChan chan : map TxsDefs.IdSort (ChanId.chansorts chan))

getVarsIds :: [VarId.VarId] -> Set.Set TxsDefs.Ident
getVarsIds = Set.unions . map getVarIds

getVarIds :: VarId.VarId -> Set.Set TxsDefs.Ident
getVarIds var = Set.fromList [TxsDefs.IdVar var, TxsDefs.IdSort (SortOf.sortOf var)]


