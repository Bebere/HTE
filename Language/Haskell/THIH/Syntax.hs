-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Syntax
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveTraversable,DeriveFoldable,DeriveFunctor #-}
module Language.Haskell.THIH.Syntax where
import Language.Haskell.THIH.BasicTypes
import Data.Foldable
import Data.Traversable
-----------------------------------
-- Abstract Syntax Tree
-----------------------------------                        
data Literal      = LitInt  Integer
                  | LitChar Char
                  | LitRat  Rational
                  | LitStr  String
                  deriving (Show,Eq)
data Pat          = PVar Id
                  | PWildcard
                  | PAs  Id Pat
                  | PLit Literal
                  | PNpk Id Integer
                  | PCon Id [Pat]
                  | PLazy Pat
                  deriving (Show,Eq)
data Expr scheme  = Var   Id
                  | Lit   Literal
--                | Const Assump -- modelled like Variables
                  | Ap    (Expr scheme) (Expr scheme)
                  | Let   (BindGroup scheme) (Expr scheme)
                  | Lam   (Alt scheme)
--                | If    Expr Expr Expr -- treated as a syntactic sugar
                  | Case  (Expr scheme) [(Pat,Expr scheme)]                 
                  deriving (Functor,Foldable,Traversable,Show,Eq)
data Alt  scheme      = Alt [Pat] (Expr scheme)  
                      deriving (Functor,Foldable,Traversable,Show,Eq)           
data Expl scheme      = Expl Id  scheme [Alt scheme]   
                      deriving (Functor,Foldable,Traversable,Show,Eq)
data Impl scheme      = Impl Id  [Alt scheme]            
                      deriving (Functor,Foldable,Traversable,Show,Eq)
data BindGroup scheme = BindGroup [Expl scheme] [[Impl scheme]]
                      deriving (Functor,Foldable,Traversable,Show,Eq)
data Program scheme   = Program [BindGroup scheme]
                      deriving (Functor,Foldable,Traversable,Show,Eq)



