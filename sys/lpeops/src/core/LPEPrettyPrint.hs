{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEPrettyPrint
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
module LPEPrettyPrint (
showSubst,
showLPE,
showLPESummand,
showLPEParamEqs,
showValExpr,
showAbbrevLPE,
showAbbrevLPESummand,
showAbbrevValExpr
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified CstrId
import qualified FuncId
import qualified ProcId
import qualified SortId
import qualified CstrDef
import qualified FuncDef
import qualified ProcDef
--import qualified BehExprDefs
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           LPETypes
import           LPEContexts
import           ValExprVisitor
import           ValFactory
import           LPEChanMap
--import           Debug.Trace

mapGet :: LPEContext -> TxsDefs.Ident -> String
mapGet m k =
    --trace ("mapGet(" ++ (show k) ++ ")") (
    case m Map.!? k of
      Just s -> s
      Nothing -> "<<<could not find " ++ Text.unpack (TxsDefs.name k) ++ "; did you mean " ++ List.intercalate "\n" (map (Text.unpack . TxsDefs.name) (Map.keys m)) ++ "?>>>"
      --Maybe.fromMaybe (error ("Could not find " ++ show k ++ " in map; found " ++ List.intercalate "\n" (map (Text.unpack . TxsDefs.name) (Map.keys m)) ++ "!")) (m Map.!? k)
    --)
-- mapGet

type VExprFromSortIdFunc = SortId.SortId -> Maybe TxsDefs.VExpr

showSubst :: Map.Map VarId.VarId TxsDefs.VExpr -> String
showSubst subst = "[" ++ List.intercalate ", " (map (\(p, v) -> Text.unpack (VarId.name p) ++ " := " ++ showValExpr v) (Map.toList subst)) ++ "]"

orderListByList :: Ord t => [t] -> [t] -> [t]
orderListByList orderedList unorderedList = List.intersect orderedList unorderedList ++ (unorderedList List.\\ orderedList)

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing LPEs:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPE :: LPE -> String
showLPE lpe = showLPEInContext (getLPEContext lpe) lpe

showAbbrevLPE :: LPE -> String
showAbbrevLPE lpe = showLPEInContext (getAbbrevLPEContext lpe) lpe

showLPEInContext :: LPEContext -> LPE -> String
showLPEInContext f lpe =
    let tdefs = lpeContext lpe in
    let g = Just . sort2defaultValue tdefs in
    let (orderedChans, orderedParams) = getOrderedChansAndParams tdefs in
      "-- " ++ Text.unpack (lpeName lpe) ++ " --\n" ++
      showTypeDefs f (Map.toList (TxsDefs.cstrDefs tdefs)) ++
      showFuncDefs f g (TxsDefs.funcDefs tdefs) ++
      showChanDefs f orderedChans ++
      "PROCDEF LPE[" ++ List.intercalate "; " (map (showChanDecl f) orderedChans) ++ "]" ++
      "(" ++ List.intercalate "; " (map (showParamDecl f g (lpeInitEqs lpe)) orderedParams) ++ ") ::=\n        " ++
      List.intercalate "\n     ## " (map (showLPESummandInContext f g orderedChans orderedParams (lpeChanMap lpe)) (Set.toList (lpeSummands lpe))) ++
      "\nENDDEF\n" ++
      "MODELDEF Model ::=\n" ++
      showChanSyncs "CHAN IN" (Set.toList (lpeInChans lpe)) ++
      showChanSyncs "CHAN OUT" (Set.toList (lpeOutChans lpe)) ++
      "    BEHAVIOUR LPE[" ++ List.intercalate ", " (map (showChanId f) orderedChans) ++ "]" ++
      "(" ++ List.intercalate ", " (map (showValExprInContext f g) (paramEqsLookup orderedParams (lpeInitEqs lpe))) ++ ")" ++
      "\nENDDEF\n"
  where
    getOrderedChansAndParams :: TxsDefs.TxsDefs -> ([ChanId.ChanId], [VarId.VarId])
    getOrderedChansAndParams tdefs =
        let orderedChansDefault = Set.toList (lpeChanParams lpe) in
        let orderedParamsDefault = Map.keys (lpeInitEqs lpe) in
          case [def | (pid, def) <- Map.toList (TxsDefs.procDefs tdefs), ProcId.name pid == lpeName lpe] of
            (ProcDef.ProcDef chans params _):_ -> (orderListByList chans orderedChansDefault, orderListByList params orderedParamsDefault)
            _ -> (orderedChansDefault, orderedParamsDefault)
    -- getOrderedChansAndParams
    
    showChanSyncs :: String -> [ChanId.ChanId] -> String
    showChanSyncs caption [] = "    " ++ caption ++ "\n"
    showChanSyncs caption cids = "    " ++ caption ++ " " ++ List.intercalate ", " (map showChanSync cids) ++ "\n"
    
    showChanSync :: ChanId.ChanId -> String
    showChanSync cid = showChanId f cid
-- showLPEInContext

showChanDefs :: LPEContext -> [ChanId.ChanId] -> String
showChanDefs _ [] = ""
showChanDefs f cids =
    "CHANDEF ChanDefs\n" ++ -- From tests, it does not seem to matter what name is used here.
    "    ::= " ++ List.intercalate "\n      ; " (map (showChanDecl f) cids) ++ "\n" ++
    "ENDDEF\n"
-- showChanDefs

showChanDecl :: LPEContext -> ChanId.ChanId -> String
showChanDecl f chanId =
    if null (ChanId.chansorts chanId)
    then showChanId f chanId
    else showChanId f chanId ++ " :: " ++ List.intercalate " # " (map (showSortId f) (ChanId.chansorts chanId))
-- showChanDecl

showTypeDefs :: LPEContext -> [(CstrId.CstrId, CstrDef.CstrDef)] -> String
showTypeDefs f cstrdefs =
    let cstrSortIds = Set.fromList (concatMap extractCstrSortIds (Map.keys f)) in
      concatMap showCstrSortId (Set.toList cstrSortIds)
  where
    extractCstrSortIds :: TxsDefs.Ident -> [SortId.SortId]
    extractCstrSortIds (TxsDefs.IdCstr cid) = [CstrId.cstrsort cid]
    extractCstrSortIds _ = []
    
    showCstrSortId :: SortId.SortId -> String
    showCstrSortId cstrSortId =
        let cstrs = [ (c, d) | (c, d) <- cstrdefs, CstrId.cstrsort c == cstrSortId ] in
          case cstrs of
            [] -> "TYPEDEF " ++ mapGet f (TxsDefs.IdSort cstrSortId) ++ " ENDDEF" -- Implicit type, not allowed in TorXakis but whatever
            _ -> "TYPEDEF " ++ mapGet f (TxsDefs.IdSort cstrSortId) ++ " ::= " ++ List.intercalate " | " (map showCstrDef cstrs) ++ " ENDDEF\n"
    -- showCstrSortId
    
    showCstrDef :: (CstrId.CstrId, CstrDef.CstrDef) -> String
    showCstrDef (cid, CstrDef.CstrDef _ accs) =
        case accs of
          [] -> mapGet f (TxsDefs.IdCstr cid)
          _ -> mapGet f (TxsDefs.IdCstr cid) ++ " { " ++ List.intercalate "; " (map (showAccessor cid) accs) ++ " }"
    --showCstrDef
    
    showAccessor :: CstrId.CstrId -> FuncId.FuncId -> String
    showAccessor cid acc = showAccessorId f cid (FuncId.name acc) ++ " :: " ++ showSortId f (FuncId.funcsort acc)
-- showTypeDefs

showFuncDefs :: LPEContext -> VExprFromSortIdFunc -> Map.Map FuncId.FuncId (FuncDef.FuncDef VarId.VarId) -> String
showFuncDefs f g funcdefs =
    let funcIds = Set.fromList (concatMap extractFuncIds (Map.keys f)) in
      concatMap showFuncDef (Set.toList funcIds)
  where
    extractFuncIds :: TxsDefs.Ident -> [FuncId.FuncId]
    extractFuncIds (TxsDefs.IdFunc fid) = [fid]
    extractFuncIds _ = []
    
    showFuncDef :: FuncId.FuncId -> String
    showFuncDef fid =
        case funcdefs Map.!? fid of
          Just (FuncDef.FuncDef params body) ->
            "FUNCDEF " ++ showFuncId f fid ++ "(" ++ List.intercalate "; " (map (showParamDecl f g Map.empty) params) ++ ") :: " ++ showSortId f (FuncId.funcsort fid) ++ " ::= " ++ showValExprInContext f g body ++ " ENDDEF\n"
          Nothing -> ""
-- showFuncDefs

showParamDecl :: LPEContext -> VExprFromSortIdFunc -> LPEParamEqs -> VarId.VarId -> String
showParamDecl f _g _paramEqs paramId = showVarId f paramId ++ " :: " ++ showSortId f (VarId.varsort paramId)

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing LPE summands:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPESummand :: LPEChanMap -> LPESummand -> String
showLPESummand chanMap summand = showLPESummandInContext (getLPESummandContext chanMap summand) (\_ -> Nothing) [] (Map.keys (lpeSmdEqs summand)) chanMap summand

showAbbrevLPESummand :: LPEChanMap -> LPESummand -> String
showAbbrevLPESummand chanMap summand = showLPESummandInContext (getAbbrevLPESummandContext chanMap summand) (\_ -> Nothing) [] (Map.keys (lpeSmdEqs summand)) chanMap summand

showLPESummandInContext :: LPEContext -> VExprFromSortIdFunc -> [ChanId.ChanId] -> [VarId.VarId] -> LPEChanMap -> LPESummand -> String
showLPESummandInContext f g orderedChans orderedParams chanMap summand =
    let (varsPerChan, hiddenVars) = getActOfferDataFromChanMap chanMap (lpeSmdChan summand) (lpeSmdVars summand) in
      (if null hiddenVars then "" else "HIDE [ HiddenChannel ] IN ") ++
      List.intercalate " | " (map showOffer varsPerChan) ++
      (if null hiddenVars then " " else " | HiddenChannel " ++ showOfferVars hiddenVars) ++
      "[[ " ++ showValExprInContext f g (lpeSmdGuard summand) ++ " ]] >-> " ++
      "LPE" ++ showChanRefs orderedChans ++
      "(" ++ showLPEParamEqsInContext f g orderedParams (lpeSmdEqs summand) ++ ")" ++
      (if null hiddenVars then "" else " NI")
  where
    showOffer :: (ChanId.ChanId, [VarId.VarId]) -> String
    showOffer (cid, vids) = showChanId f cid ++ showOfferVars vids
    
    showOfferVars :: [VarId.VarId] -> String
    showOfferVars vars = concatMap (\v -> "? " ++ showVarId f v ++ " :: " ++ showSortId f (VarId.varsort v) ++ " ") vars
    
    showChanRefs :: [ChanId.ChanId] -> String
    showChanRefs [] = ""
    showChanRefs cids = "[" ++ List.intercalate ", " (map (showChanId f) cids) ++ "]"
-- showLPESummandInContext

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing parameter assignments:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPEParamEqs :: LPEContext -> LPEParamEqs -> String
showLPEParamEqs f eqs = showLPEParamEqsInContext f (\_ -> Nothing) (Map.keys eqs) eqs

showLPEParamEqsInContext :: LPEContext -> VExprFromSortIdFunc -> [VarId.VarId] -> LPEParamEqs -> String
showLPEParamEqsInContext f g orderedParams eqs =
    List.intercalate ", " (map getFromEqs orderedParams)
  where
    getFromEqs :: VarId.VarId -> String
    getFromEqs v = case eqs Map.!? v of
                     Just e -> showValExprInContext f g e
                     Nothing -> "<<<could not find expression for parameter named " ++ Text.unpack (VarId.name v) ++ "!>>>"
-- showLPEParamEqsInContext

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Show value expressions (aka data expressions):
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showValExpr :: TxsDefs.VExpr -> String
showValExpr expr = showValExprInContext (getValExprContext expr) (\_ -> Nothing) expr

showAbbrevValExpr :: TxsDefs.VExpr -> String
showAbbrevValExpr expr = showValExprInContext (getAbbrevValExprContext expr) (\_ -> Nothing) expr

showValExprInContext :: LPEContext -> VExprFromSortIdFunc -> TxsDefs.VExpr -> String
showValExprInContext f g = customData . visitValExpr showVisitor
  where
    showVisitor :: [ValExprVisitorOutput String] -> TxsDefs.VExpr -> ValExprVisitorOutput String
    showVisitor subExps expr =
        let pars = map customData subExps in
        let str = case expr of
                    (view -> Vconst (Cbool val))      -> show val
                    (view -> Vconst (Cint val))       -> show val
                    (view -> Vconst (Cstring val))    -> show val
                    (view -> Vconst (Cregex val))     -> "REGEX('" ++ Text.unpack val ++ "')"
                    (view -> Vconst (Ccstr cid _))    -> mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vconst (Cany sid))       -> case g sid of
                                                           Just x -> showValExprInContext f g x
                                                           Nothing -> "ANY " ++ showSortId f sid
                    (view -> Vvar vid)                -> showVarId f vid
                    (view -> Vfunc fid _)             -> showFuncId f fid ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Vcstr cid _)             -> mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ List.intercalate ", " pars ++ ")"
                    (view -> Viscstr cid _)           -> "is" ++ mapGet f (TxsDefs.IdCstr cid) ++ "(" ++ head pars ++ ")"
                    (view -> Vaccess cid n _ _)       -> showAccessorId f cid n ++ "(" ++ head pars ++ ")"
                    (view -> Vite _ _t _e)            ->
                      -- case (_t, _e) of
                        -- ((view -> Vconst (Cbool True)), (view -> Vconst (Cbool False))) -> head pars
                        -- ((view -> Vconst (Cbool False)), (view -> Vconst (Cbool True))) -> "not(" ++ head pars ++ ")"
                        -- ((view -> Vconst (Cbool True)), _) -> "(" ++ head pars ++ " \\/ " ++ pars !! 2 ++ ")"
                        -- ((view -> Vconst (Cbool False)), _) -> "(not(" ++ head pars ++ ") /\\ " ++ pars !! 2 ++ ")"
                        -- (_, (view -> Vconst (Cbool True))) -> "(not(" ++ head pars ++ ") \\/ " ++ pars !! 1 ++ ")"
                        -- (_, (view -> Vconst (Cbool False))) -> "(" ++ head pars ++ " /\\ " ++ pars !! 1 ++ ")"
                        -- (_, _) ->
                          "IF " ++ head pars ++ " THEN " ++ pars !! 1 ++ " ELSE " ++ pars !! 2 ++ " FI"
                    (view -> Vdivide _ _)             -> "(" ++ head pars ++ "/" ++ pars !! 1 ++ ")"
                    (view -> Vmodulo _ _)             -> "(" ++ head pars ++ "%" ++ pars !! 1 ++ ")"
                    (view -> Vgez _)                  -> "(" ++ head pars ++ ">=0)"
                    (view -> Vsum _)                  -> "(" ++ List.intercalate "+" (map (showMultElem "*") subExps) ++ ")"
                    (view -> Vproduct _)              -> "(" ++ List.intercalate "*" (map (showMultElem "^") subExps) ++ ")"
                    (view -> Vequal _ _)              -> "(" ++ head pars ++ "==" ++ pars !! 1 ++ ")"
                    (view -> Vand _)                  -> "(" ++ List.intercalate " /\\ " pars ++ ")"
                    (view -> Vnot _)                  -> "not(" ++ head pars ++ ")"
                    (view -> Vlength _)               -> "length(" ++ head pars ++ ")"
                    (view -> Vat _ _)                 -> "at(" ++ head pars ++ ", " ++ pars !! 1 ++ ")"
                    (view -> Vconcat _)               -> List.intercalate ":" pars
                    (view -> Vstrinre _ _)            -> "strinre(" ++ head pars ++ ", " ++ pars !! 1 ++ ")"
                    (view -> Vpredef _ fid _)         -> showFuncId f fid ++ "(" ++ List.intercalate ", " pars ++ ")"
                    _                                 -> error ("ShowValExprInContext.showVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 str
    -- showVisitor
    
    showMultElem :: String -> ValExprVisitorOutput String -> String
    showMultElem op subExp =
        let mult = multiplicity subExp in
          "(" ++ customData subExp ++ if mult /= 1 then op ++ "(" ++ show mult ++ "))" else ")"
-- showValExprInContext

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Show miscellaneous:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showSortId :: LPEContext -> SortId.SortId -> String
showSortId f sid = Maybe.fromMaybe (Text.unpack (SortId.name sid)) (f Map.!? TxsDefs.IdSort sid)

showChanId :: LPEContext -> ChanId.ChanId -> String
showChanId f = mapGet f . TxsDefs.IdChan

showVarId :: LPEContext -> VarId.VarId -> String
showVarId f = mapGet f . TxsDefs.IdVar

showFuncId :: LPEContext -> FuncId.FuncId -> String
showFuncId f fid = Maybe.fromMaybe (Text.unpack (FuncId.name fid)) (f Map.!? TxsDefs.IdFunc fid)

showAccessorId :: LPEContext -> CstrId.CstrId -> Text.Text -> String
showAccessorId f cid n =
    case [ s | (TxsDefs.IdFunc fid, s) <- Map.toList f, FuncId.funcargs fid == [CstrId.cstrsort cid], FuncId.name fid == n ] of
      x:_ -> x
      [] -> error ("ShowValExprInContext.showVisitor has not been given a name for accessor \"" ++ Text.unpack n ++ "\"!")
-- showAccId





