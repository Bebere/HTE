-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.SurfaceTypes
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.THIH.SurfaceTypes where

import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.BasicTypes

import Control.Applicative((<$>))
import Data.List (union)
----------------------------------
-- Surface Representation of Types 
-- (User's input)
----------------------------------
type SVarBind     = Id --(Id,Maybe Kind)
data SPred        = SIsIn Id [SType] 
                  deriving (Eq,Show)     
data SType        = SVar Id
                  | SCon Id
                  | SApp SType SType --HM restriction 
                  deriving (Eq,Show)  
data SQual t      = [SPred] :==> t
                  deriving (Eq,Show)                
data SScheme      = SForall [SVarBind] 
                    (SQual SType)             
                  deriving (Eq,Show) 
                           
type Unkinded e = e SScheme                           

data STypeSynonym = STypeSynonym Id [SVarBind] SType 
                  deriving (Eq,Show)
data SDataType    = SDataType Id [SVarBind] [(Id,SType)]                    
                  deriving (Eq,Show)
data STypeClass   = STypeClass [SPred] Id [SVarBind] [(Id,SScheme)]
                  deriving (Eq,Show)
data SInstance    = SInstance [SPred] Id [SType] 
                  deriving (Eq,Show)

data SModule      = SModule 
                    [STypeSynonym] [SDataType] 
                    [STypeClass] [SInstance]
                    (Unkinded Program)
                    deriving (Eq,Show)

class ApplyS a where
  applyS :: [(Id, SType)] -> a -> a 
instance ApplyS SType where  
  applyS  s  v@(SVar n) 
   | Just t <- lookup n s   = t 
   | True                   = v           
  applyS _ v@(SCon _)       = v              
  applyS s (SApp t1 t2)     = 
   SApp (applyS s t1) (applyS s t2)
instance ApplyS SPred where
  applyS s (SIsIn i ts) = SIsIn i (map (applyS s) ts) 

instance ApplyS SScheme where
  applyS s (SForall ks (ps :==> t)) = SForall ks ((map (applyS s) ps) :==> applyS s t)


class TVS a where
  tvS :: a -> [Id]
  
instance TVS a => TVS [a] where  
  tvS ts = foldl union [] (tvS <$> ts)

instance TVS SType where  
  tvS  (SVar i)     = [i]
  tvS  (SCon i)     = [] 
  tvS  (SApp t1 t2) = union (tvS t1) (tvS t2) 
  
instance TVS  SPred where
  tvS (SIsIn i ts) =   tvS ts

instance  (TVS t) =>   TVS  (SQual t) where
  tvS (ps :==> t) = union (tvS ps) (tvS t)