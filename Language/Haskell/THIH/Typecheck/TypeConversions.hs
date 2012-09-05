-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.TypeConversions
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Typecheck.TypeConversions where

import Language.Haskell.THIH.SurfaceTypes
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.Typecheck.Internals
import Language.Haskell.THIH.BasicTypes

import Debug.Trace
import Control.Applicative ((<$>))

cPred :: ConEnv -> SPred -> Pred
cPred cn (SIsIn i sts) = IsIn i (cType cn <$> sts)

cType ::ConEnv -> SType -> Type
cType cn (SCon i)| Just k <- lookup i cn = TCon i k 
                 | True = Prelude.error "Data Constructor doesn't exist!"
cType cn (SApp t1 t2) = TAp  (cType cn t1) (cType cn t2)   
cType _ (SVar i) = (TVar (Tyvar i Star)) -- why star?  

cScheme :: ConEnv -> [Kind] -> SScheme -> Scheme 
cScheme cn ks scc@(SForall tys (ps :==> t)) = let
  t'   = cType cn t
  ps'  = cPred cn <$> ps
  vars = zip tys [0.. (length tys)-1]
  t''  = foldl (\tt (n,i) -> 
                 apply (Tyvar n Star +-> TGen i ) tt) t' vars
  ps'' = foldl (\tt (n,i) -> 
                 apply (Tyvar n Star +-> TGen i ) tt) ps' vars
  in  Forall ks (ps'' :=> t'')
     
cDataType :: ConEnv -> SDataType -> DataType
cDataType cn sd@(SDataType i vars cns) = let 
  Just sc = lookup i cn
  ks = splitKinds sc
  as = [ icn :>: (quantifySType cn vars ks st)
      | (icn,st) <- cns ] 
  in DataType i sc as
     where
       quantifySType :: ConEnv -> [Id] -> [Kind] -> SType -> Scheme
       quantifySType cn is ks st = let
         t  = cType cn st
         vars = zip is [0..length is - 1]
         t' = foldl (\tt (n,i) -> 
                      apply (Tyvar n Star +-> TGen i ) tt) t vars
         in Forall ks ([] :=> t')

cTypeClass :: ConEnv -> [(Id,[Kind])] -> STypeClass -> TypeClass
cTypeClass cn mcn (STypeClass sups i vars cns) = let
  Just sc = lookup i cn 
  ks = splitKinds sc
  as = [ icn :>:  cScheme cn mks' ssc'   
       | (icn,ssc@(SForall mvars (mps:==>mt))) <- cns
       , let
         Just mks = lookup icn mcn
         -- add class predicate and global tyvar
         ssc' =   
           SForall (vars++mvars) 
                (([SIsIn i (SVar <$> vars)]++ mps) :==> mt)
         mks' = ks ++ mks ]
    in   
       TypeClass (cPred cn <$> sups) i (zipWith Tyvar vars ks) as

cTypeSynonym :: ConEnv -> STypeSynonym -> TypeSynonym
cTypeSynonym  = Prelude.undefined





