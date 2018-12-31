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
showLPEModel,
showLPEProcess,
showLPESummand,
showLPEParamEqs,
showValExpr,
showAbbrevLPEModel,
showAbbrevLPEProcess,
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
import           Constant hiding (sort)
import           ValExpr hiding (subst)
import           LPETypeDefs
import           LPEContexts
import           ValExprVisitor
import           ValFactory
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

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing LPE models:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPEModel :: LPEModel -> String
showLPEModel model = showLPEModelInContext (getModelContext model) model

showAbbrevLPEModel :: LPEModel -> String
showAbbrevLPEModel model = showLPEModelInContext (getAbbrevModelContext model) model

showLPEModelInContext :: LPEContext -> LPEModel -> String
showLPEModelInContext f (tdefs, TxsDefs.ModelDef insyncs outsyncs _splsyncs _bexpr, process@(n, chanIds, initParamEqs, _)) =
    let g = Just . sort2defaultValue tdefs in
    let orderedParams = getOrderedParams in
      showTypeDefs f (Map.toList (TxsDefs.cstrDefs tdefs)) ++
      showFuncDefs f g (TxsDefs.funcDefs tdefs) ++
      showChanDefs f chanIds ++
      showLPEProcessInContext f g showParamDecl process orderedParams ++
      "MODELDEF Model ::=\n" ++ showChanSyncs "CHAN IN" insyncs ++ showChanSyncs "CHAN OUT" outsyncs ++
      "    BEHAVIOUR LPE[" ++ List.intercalate ", " (map (showChanId f) chanIds) ++ "]" ++
      "(" ++ List.intercalate ", " (map (showValExprInContext f g) (paramEqsLookup orderedParams initParamEqs)) ++ ")" ++
      "\nENDDEF\n"
  where
    getOrderedParams :: [VarId.VarId]
    getOrderedParams =
      case [def | (pid, def) <- Map.toList (TxsDefs.procDefs tdefs), ProcId.name pid == n] of
        (ProcDef.ProcDef _ params _):_ -> List.intersect params (Map.keys initParamEqs)
        _ -> Map.keys initParamEqs
    -- getOrderedParams
    
    showChanSyncs :: String -> [Set.Set ChanId.ChanId] -> String
    showChanSyncs caption [] = "    " ++ caption ++ "\n"
    showChanSyncs caption syncs = "    " ++ caption ++ " " ++ List.intercalate ", " (map showChanSync syncs) ++ "\n"
    
    showChanSync :: Set.Set ChanId.ChanId -> String
    showChanSync cids = List.intercalate " | " (map (showChanId f) (Set.toList cids))
-- showLPEModelInContext

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

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing LPE processes:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPEProcess :: LPEProcess -> String
showLPEProcess lpe@(_, _, initParamEqs, _) = showLPEProcessInContext (getProcessContext lpe) (\_ -> Nothing) showInitializedParamDecl lpe (Map.keys initParamEqs)

showAbbrevLPEProcess :: LPEProcess -> String
showAbbrevLPEProcess lpe@(_, _, initParamEqs, _) = showLPEProcessInContext (getAbbrevProcessContext lpe) (\_ -> Nothing) showInitializedParamDecl lpe (Map.keys initParamEqs)

showLPEProcessInContext :: LPEContext -> VExprFromSortIdFunc -> (LPEContext -> VExprFromSortIdFunc -> LPEParamEqs -> VarId.VarId -> String) -> LPEProcess -> [VarId.VarId] -> String
showLPEProcessInContext f g h (_, chanIds, initParamEqs, summands) orderedParams =
    "PROCDEF LPE[" ++ List.intercalate "; " (map (showChanDecl f) chanIds) ++ "]" ++
    "(" ++ List.intercalate "; " (map (h f g initParamEqs) orderedParams) ++ ") ::=\n        " ++
    List.intercalate "\n     ## " (map (showLPESummandInContext f g chanIds orderedParams) (Set.toList summands)) ++
    "\nENDDEF\n"
-- showLPEProcessInContext

showParamDecl :: LPEContext -> VExprFromSortIdFunc -> LPEParamEqs -> VarId.VarId -> String
showParamDecl f _g _paramEqs paramId = showVarId f paramId ++ " :: " ++ showSortId f (VarId.varsort paramId)

showInitializedParamDecl :: LPEContext -> VExprFromSortIdFunc -> LPEParamEqs -> VarId.VarId -> String
showInitializedParamDecl f g paramEqs paramId =
    showParamDecl f g paramEqs paramId ++
    case paramEqs Map.!? paramId of
      Just e -> showValExprInContext f g e
      Nothing -> "<<<could not find initParam named " ++ Text.unpack (VarId.name paramId) ++ "!>>>"
-- showInitializedParamDecl

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Showing LPE summands:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

showLPESummand :: LPESummand -> String
showLPESummand summand@(LPESummand _ _ _ eqs) = showLPESummandInContext (getSummandContext summand) (\_ -> Nothing) [] (Map.keys eqs) summand

showAbbrevLPESummand :: LPESummand -> String
showAbbrevLPESummand summand@(LPESummand _ _ _ eqs) = showLPESummandInContext (getAbbrevSummandContext summand) (\_ -> Nothing) [] (Map.keys eqs) summand

showLPESummandInContext :: LPEContext -> VExprFromSortIdFunc -> [ChanId.ChanId] -> [VarId.VarId] -> LPESummand -> String
showLPESummandInContext f g chanIds orderedParams (LPESummand channelVars channelOffers guard paramEqs) =
    let usedChannelVars = concatMap snd channelOffers in
    let hiddenChannelVars = Set.toList (Set.fromList channelVars Set.\\ Set.fromList usedChannelVars) in
      showChannelOffers channelOffers ++
      showHiddenVars hiddenChannelVars ++
      "[[ " ++ showValExprInContext f g guard ++ " ]] >-> LPE" ++ showChanRefs chanIds ++ "(" ++ showLPEParamEqsInContext f g orderedParams paramEqs ++ ")"
  where
    showChannelOffers :: LPEChannelOffers -> String
    showChannelOffers [] = ""
    showChannelOffers offers = List.intercalate " | " (map showChannelOffer offers) ++ " "
    
    showChannelOffer :: LPEChannelOffer -> String
    showChannelOffer (chanId, vars) = showChanId f chanId ++ concatMap (\v -> " ? " ++ showVarId f v ++ " :: " ++ showSortId f (VarId.varsort v)) vars
    
    showChanRefs :: [ChanId.ChanId] -> String
    showChanRefs [] = ""
    showChanRefs cids = "[" ++ List.intercalate ", " (map (showChanId f) cids) ++ "]"
    
    showHiddenVars :: [VarId.VarId] -> String
    showHiddenVars [] = ""
    showHiddenVars hiddenVars = "(" ++ List.intercalate ", " (map (showVarId f) hiddenVars) ++ ") "
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
                    (view -> Vite{})                  -> "IF " ++ head pars ++ " THEN " ++ pars !! 1 ++ " ELSE " ++ pars !! 2 ++ " FI"
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





