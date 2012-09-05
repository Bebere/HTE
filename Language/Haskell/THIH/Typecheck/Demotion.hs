-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Demotion
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Typecheck.Demotion where
import Language.Haskell.THIH.Typecheck.Types
import Control.Applicative
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Typecheck.Internals
import Debug.Trace
import Data.List(isPrefixOf)

toLookup :: [Assump] -> [(Id,Scheme)]
toLookup = map (\( ('t':i) :>: sc) -> (i,sc))

demoteConEnv :: ConEnv -> [Assump]
demoteConEnv = map demoteCN   

demoteClassEnv :: ClassEnv -> [Assump]
demoteClassEnv ce =  [ ("t" ++ i) :>: (toScheme $ 
                       foldl1 (-->) (((\(Tyvar i k)-> demoteKind k)  <$> tys) 
                                     ++ [constraint]))
                     |(i,(tys,_,_)) <- cls ce]

demoteCN :: (Id, Kind) -> Assump  
demoteCN (i,k) =  ("t" ++ i) :>: ( toScheme $ demoteKind k)

demoteKind :: Kind -> Type  
demoteKind (Star) =   star
demoteKind (Constraint) = constraint
demoteKind (Kfun k1 k2) = (demoteKind k1) --> (demoteKind k2)
  