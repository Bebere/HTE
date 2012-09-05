-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.BasicTypes
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.THIH.BasicTypes where

type Id = String
data Kind         = Star 
                  | Constraint 
                  | Kfun Kind Kind
                 deriving (Eq,Show)

splitKinds :: Kind -> [Kind]
splitKinds Star         = []
splitKinds Constraint   = [] 
splitKinds (Kfun k1 k2) = k1 : (splitKinds k2)