{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ValFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ValFactory (
sort2defaultValue,
sort2defaultConst
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified ValExpr
import qualified SortId
import qualified Constant
import qualified CstrId

sort2defaultValue :: TxsDefs.TxsDefs -> SortId.SortId -> TxsDefs.VExpr
sort2defaultValue tdefs sortId = ValExpr.cstrConst (sort2defaultConst tdefs sortId)

sort2defaultConst :: TxsDefs.TxsDefs -> SortId.SortId -> Constant.Constant
sort2defaultConst tdefs sortId
    | sortId == SortId.sortIdBool =
        Constant.Cbool False
    | sortId == SortId.sortIdInt =
        Constant.Cint 0
    | sortId == SortId.sortIdString =
        Constant.Cstring (Text.pack "")
    | sortId == SortId.sortIdRegex =
        Constant.Cstring (Text.pack "")
    | otherwise =
        -- Use any non-recursive constructor of this sort to express a value of this sort:
        case [ cstrId | cstrId <- Map.keys (TxsDefs.cstrDefs tdefs), CstrId.cstrsort cstrId == sortId, isNonRecursiveCstr tdefs (Set.singleton cstrId) cstrId ] of
          -- Do the same for the parameters:
          (cstrId:_) -> Constant.Ccstr cstrId (map (sort2defaultConst tdefs) (CstrId.cstrargs cstrId))
          [] -> error ("Failed to generate a default value for " ++ show sortId ++ " (available={" ++ List.intercalate ", " (map show (Map.keys (TxsDefs.cstrDefs tdefs))) ++ "})!")
-- sort2defaultConst

-- Determines if the specified constructor is non-recursive, meaning that
-- all of its arguments are of sorts that are non-recursive.
isNonRecursiveCstr :: TxsDefs.TxsDefs -> Set.Set CstrId.CstrId -> CstrId.CstrId -> Bool
isNonRecursiveCstr tdefs beenHere cstrId =
    if Set.member cstrId beenHere
    then True
    else List.all (isNonRecursiveSort tdefs (Set.insert cstrId beenHere)) (CstrId.cstrargs cstrId)
-- isNonRecursiveCstr

-- Checks if the specified sort is non-recursive, meaning that
--  - The sort is a primitive sort (bool, int, string, regex); or
--  - The sort is a constructor sort with at least one non-recursive constructor.
isNonRecursiveSort :: TxsDefs.TxsDefs -> Set.Set CstrId.CstrId -> SortId.SortId -> Bool
isNonRecursiveSort tdefs beenHere sortId
    | sortId == SortId.sortIdBool = True
    | sortId == SortId.sortIdInt = True
    | sortId == SortId.sortIdString = True
    | sortId == SortId.sortIdRegex = True
    | otherwise =
        -- Obtain a list of all constructors that result in the specified sort:
        let sortCstrs = [ cstrId | cstrId <- Map.keys (TxsDefs.cstrDefs tdefs), CstrId.cstrsort cstrId == sortId ] in
            List.any (isNonRecursiveCstr tdefs beenHere) sortCstrs
-- isNonRecursiveSort



