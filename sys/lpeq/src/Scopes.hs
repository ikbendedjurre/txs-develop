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
fromChans,
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
applyToActOffer,
addActOffer,
addOffer,
addChanOffers,
addChanOffer
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

fromChans :: [ChanId.ChanId] -> Scope
fromChans cids = empty { chanMap = Map.fromList (zip cids cids) }

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
applyToChan _ cid | cid == TxsDefs.chanIdExit = cid
applyToChan _ cid | cid == TxsDefs.chanIdIstep = cid
applyToChan scope cid | otherwise =
    case chanMap scope Map.!? cid of
      Just c -> c
      Nothing -> error ("Could not find channel " ++ show cid ++ " in " ++ show (chanMap scope))
-- applyToChan

applyToChans :: Scope -> [ChanId.ChanId] -> [ChanId.ChanId]
applyToChans scope = map (applyToChan scope)

applyToChanSet :: Scope -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
applyToChanSet scope = Set.map (applyToChan scope)

applyToVar :: Scope -> VarId.VarId -> VarId.VarId
applyToVar scope vid =
    case varMap scope Map.!? vid of
      Just v -> v
      Nothing -> error ("Could not find variable " ++ show vid ++ " in " ++ show (varMap scope))
-- applyToVar

applyToVars :: Scope -> [VarId.VarId] -> [VarId.VarId]
applyToVars scope = map (applyToVar scope)

applyToVarSet :: Scope -> Set.Set VarId.VarId -> Set.Set VarId.VarId
applyToVarSet scope = Set.map (applyToVar scope)

applyToVExpr :: Scope -> TxsDefs.VExpr -> TxsDefs.VExpr
applyToVExpr scope = Subst.subst (Map.map ValExpr.cstrVar (varMap scope)) Map.empty

applyToVExprs :: Scope -> [TxsDefs.VExpr] -> [TxsDefs.VExpr]
applyToVExprs scope = map (applyToVExpr scope)

applyToActOffer :: Scope -> TxsDefs.ActOffer -> TxsDefs.ActOffer
applyToActOffer scope actOffer =
    actOffer { TxsDefs.offers = Set.map (applyToOffer scope) (TxsDefs.offers actOffer)
             , TxsDefs.constraint = applyToVExpr scope (TxsDefs.constraint actOffer)
             }
-- applyToActOffer

applyToOffer :: Scope -> TxsDefs.Offer -> TxsDefs.Offer
applyToOffer scope offer =
    TxsDefs.Offer { TxsDefs.chanid = applyToChan scope (TxsDefs.chanid offer)
                  , TxsDefs.chanoffers = map (applyToChanOffer scope) (TxsDefs.chanoffers offer)
                  }
-- applyToOffer

applyToChanOffer :: Scope -> TxsDefs.ChanOffer -> TxsDefs.ChanOffer
applyToChanOffer _scope chanOffer = chanOffer

addActOffer :: Scope -> TxsDefs.ActOffer -> Scope
addActOffer scope actOffer = foldl addOffer scope (TxsDefs.offers actOffer)

addOffer :: Scope -> TxsDefs.Offer -> Scope
addOffer scope offer = addChanOffers scope (TxsDefs.chanoffers offer)

addChanOffers :: Foldable t => Scope -> t TxsDefs.ChanOffer -> Scope
addChanOffers scope chanOffers = foldl addChanOffer scope chanOffers

addChanOffer :: Scope -> TxsDefs.ChanOffer -> Scope
addChanOffer scope (TxsDefs.Quest v) = scope { varMap = Map.insert v v (varMap scope) }
addChanOffer scope _ = scope

