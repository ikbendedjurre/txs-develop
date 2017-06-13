{-
TorXakis - Model Based Testing
Copyright (c) 2015-2016 TNO and Radboud University
See license.txt
-}


-- ----------------------------------------------------------------------------------------- --

module EnvServer

-- ----------------------------------------------------------------------------------------- --
--
-- TorXakis Server Environment (Internal State) Data Type Definitions
--
-- ----------------------------------------------------------------------------------------- --
-- export

( IOS             -- type IOS a = StateT EnvS IOC a
                  -- torxakis server main state monad transformer
, EnvS     (..)   -- torxakis server state
, envsNone        -- torxakis server initial state
, TxsModus (..)   -- torxakis server modus
, isNoned         -- isXX :: TxsModus -> Bool
, isIdled         -- check whether torxakis modus is XX
, isInited        --
, isTested        --
, isSimuled       --
, isStepped       --
, isGtNoned       -- isGtXX :: TxsModus -> Bool
, isGtIdled       -- check whether torxakis modus is greater (further) than XX
, isGtInited      --
, getParams       -- :: [String] -> IOS [(String,String)]
, setParams       -- :: [(String,String)] -> IOS [(String,String)]
)

-- ----------------------------------------------------------------------------------------- --
-- import

where

import System.IO
import Control.Monad.State
import Control.Concurrent

import qualified Data.Map  as Map

-- import from local
import ParamServer

-- import from coreenv
import qualified EnvCore    as IOC

-- import from defs
import qualified TxsDefs   as TxsDefs
import qualified TxsDDefs  as TxsDDefs
import qualified TxsShow   as TxsShow



-- ----------------------------------------------------------------------------------------- --
-- IOS :  torxakis server main state monad transformer


type IOS a  =  StateT EnvS IOC.IOC a


-- ----------------------------------------------------------------------------------------- --
-- torxakis server state type definitions


data EnvS   =  EnvS { host    :: String                    -- host of server client
                    , portnr  :: Integer                   -- portnr of server client
                    , servhs  :: Handle                    -- server socket handle
                    , modus   :: TxsModus                  -- current modus of TXS operation
                    , uid     :: Int                       -- last used unique id number
                    , tdefs   :: TxsDefs.TxsDefs           -- TorXakis definitions from file
                    , locvars :: [TxsDefs.VarId]           -- local free variables
                    , locvals :: TxsDefs.VEnv              -- local value environment
                    , tow     :: ( Maybe (Chan TxsDDefs.SAction)   -- connections to world
                                 , Maybe ThreadId        
                                 , [TxsDDefs.ConnHandle]
                                 )
                    , frow    :: ( Maybe (Chan TxsDDefs.SAction)   -- connections from world
                                 , [ThreadId]
                                 , [TxsDDefs.ConnHandle]
                                 )
                    , params  :: Params                    -- TorXakis parameters with checks
                    }


envsNone    :: EnvS
envsNone    =  EnvS { host      = ""
                    , portnr    = 0
                    , servhs    = stderr
                    , modus     = Noned
                    , uid       = 1000
                    , tdefs     = TxsDefs.empty
                    , locvars   = []
                    , locvals   = Map.empty
                    , tow       = ( Nothing, Nothing, [] )
                    , frow      = ( Nothing, [],      [] )
                    , params    = initParams
                    }


-- ----------------------------------------------------------------------------------------- --
-- Txs Modus


data  TxsModus  =  Noned
                 | Idled
                 | Inited
                 | Tested  TxsDefs.TxsDef   -- CnectDef
                 | Simuled TxsDefs.TxsDef   -- CnectDef
                 | Stepped

isNoned, isIdled, isInited        :: TxsModus -> Bool
isTested, isSimuled, isStepped    :: TxsModus -> Bool
isGtNoned, isGtIdled, isGtInited  :: TxsModus -> Bool

isNoned Noned             =  True
isNoned _                 =  False
isIdled Idled             =  True
isIdled _                 =  False
isInited Inited           =  True
isInited _                =  False
isTested  (Tested _)      =  True
isTested  _               =  False
isSimuled (Simuled _)     =  True
isSimuled _               =  False
isStepped Stepped         =  True
isStepped _               =  False

isGtNoned  m              =  not (isNoned m)
isGtIdled  m              =  isGtNoned m && not (isIdled m)
isGtInited m              =  isGtIdled m && not (isInited m)


-- ----------------------------------------------------------------------------------------- --
-- Params :  getParams, setParams


getParams :: [String] -> IOS [(String,String)]
getParams prms  =  do
     case prms of
       [] -> do parammap <- gets params
                return $ map (\(nm,(val,_))->(nm,val)) (Map.toList parammap)
       _  -> do params <- mapM getParam prms
                return $ concat params

getParam :: String -> IOS [(String,String)]
getParam prm  =  do
     params <- gets params
     case Map.lookup prm params of
       Nothing          -> return []
       Just (val,check) -> return [(prm,val)]


setParams :: [(String,String)] -> IOS [(String,String)]
setParams parvals  =  do
     params <- mapM setParam parvals
     return $ concat params

setParam :: (String,String) -> IOS [(String,String)]
setParam (prm,val)  =  do
     params <- gets params
     case Map.lookup prm params of
       Nothing           -> return []
       Just (val',check) -> if  check val
                              then do params' <- return $ Map.insert prm (val,check) params
                                      modify $ \env -> env { params = params' }
                                      return $ [(prm,val)]
                              else return []


-- ----------------------------------------------------------------------------------------- --
-- Msg :  (Error) Messages

{-

data Msg     =   TXS_SERV_SYSTEM_ERROR     { s :: String }
               | TXS_SERV_MODEL_ERROR      { s :: String }
               | TXS_SERV_USER_ERROR       { s :: String }
               | TXS_SERV_RUNTIME_ERROR    { s :: String }
               | TXS_SERV_SYSTEM_WARNING   { s :: String }
               | TXS_SERV_MODEL_WARNING    { s :: String }
               | TXS_SERV_USER_WARNING     { s :: String }
               | TXS_SERV_RUNTIME_WARNING  { s :: String }
               | TXS_SERV_SYSTEM_INFO      { s :: String }
               | TXS_SERV_MODEL_INFO       { s :: String }
               | TXS_SERV_USER_INFO        { s :: String }
               | TXS_SERV_RUNTIME_INFO     { s :: String }
               | TXS_SERV_RESPONSE         { s :: String }
               | TXS_SERV_OK               { s :: String }
               | TXS_SERV_NOK              { s :: String }
               | TXS_SERV_ANY              { s :: String }
     deriving (Eq,Ord,Read,Show)

instance TxsShow.PShow Msg
  where
     pshow msg  =  s msg


-- | Add messages to IOS Monad.
putMsgs :: [Msg] -> IOS ()
putMsgs mess  =  do
     msgs' <- gets msgs
     modify $ \env -> env { msgs = msgs' ++ mess }


-- | Take messages from Monad, and reset message list .
takeMsgs :: IOS [String]
takeMsgs  =  do
     msgs' <- gets msgs
     modify $ \env -> env { msgs = [] }
     return $ map TxsShow.pshow msgs'

-}


-- ----------------------------------------------------------------------------------------- --
-- 
-- ----------------------------------------------------------------------------------------- --
