{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Scopes
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module Scopes (
Scope(..),
empty,
cloneScope,
applyToChan,
applyToChans,
applyToChanSet,
applyToVar,
applyToVars,
applyToVarSet,
applyToVExpr,
applyToVExprs,
applyToChanOffer,
applyToActOffer
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ValExpr
import qualified VarId
import qualified ChanId
import qualified Subst
import ChanFactory
import VarFactory

data Scope = Scope { chanMap :: Map.Map ChanId.ChanId ChanId.ChanId
                   , varMap :: Map.Map VarId.VarId VarId.VarId
                   } deriving (Eq, Ord, Show)
-- Scope

empty :: Scope
empty = Scope { chanMap = Map.empty, varMap = Map.empty }

cloneScope :: Scope -> IOC.IOC Scope
cloneScope s = do
    chanMap' <- mapValuesM createFreshChanFromChan (chanMap s)
    varMap' <- mapValuesM createFreshVarFromVar (varMap s)
    return (Scope { chanMap = chanMap', varMap = varMap' })
-- cloneScope

mapValuesM :: (Ord a, Monad m) => (b -> m c) -> Map.Map a b -> m (Map.Map a c)
mapValuesM f mp = Map.fromList <$> Monad.mapM applyToEntry (Map.toList mp)
  where
    applyToEntry (k, v) = do
      v' <- f v
      return (k, v')
-- mapValuesM

applyToChan :: Scope -> ChanId.ChanId -> ChanId.ChanId
applyToChan scope cid = chanMap scope Map.! cid

applyToChans :: Scope -> [ChanId.ChanId] -> [ChanId.ChanId]
applyToChans scope = map (applyToChan scope)

applyToChanSet :: Scope -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
applyToChanSet scope = Set.map (applyToChan scope)

applyToVar :: Scope -> VarId.VarId -> VarId.VarId
applyToVar scope cid = varMap scope Map.! cid

applyToVars :: Scope -> [VarId.VarId] -> [VarId.VarId]
applyToVars scope = map (applyToVar scope)

applyToVarSet :: Scope -> Set.Set VarId.VarId -> Set.Set VarId.VarId
applyToVarSet scope = Set.map (applyToVar scope)

applyToVExpr :: Scope -> TxsDefs.VExpr -> TxsDefs.VExpr
applyToVExpr scope = Subst.subst (Map.map ValExpr.cstrVar (varMap scope)) Map.empty

applyToVExprs :: Scope -> [TxsDefs.VExpr] -> [TxsDefs.VExpr]
applyToVExprs scope = map (applyToVExpr scope)

applyToChanOffer :: Scope -> TxsDefs.ChanOffer -> TxsDefs.ChanOffer
applyToChanOffer _scope chanOffer = chanOffer

applyToActOffer :: Scope -> TxsDefs.ActOffer -> TxsDefs.ActOffer
applyToActOffer _scope actOffer = actOffer
























