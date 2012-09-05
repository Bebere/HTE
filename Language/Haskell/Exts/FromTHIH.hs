-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Exts.FromTHIH
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.Exts.FromTHIH where

import Language.Haskell.THIH.Typecheck.Types as TH
import Language.Haskell.THIH.BasicTypes as TH
import Language.Haskell.Exts.Syntax as HSE 
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Desugaring hiding (error)
 
import Data.List(partition)
import Data.Maybe(fromJust)
import Control.Applicative ((<$>))


cScheme2Type :: Scheme -> HSE.Type
cScheme2Type (Forall ks  (ps :=> t)) = 
  TyForall (Just [ KindedVar (Ident $ "t" ++ (show i)) (cKind2Kind k)    
                 | (k,i) <- (zip ks [0..(length ks) -1])])
           (map cPred2Asst ps) (cType2Type t)   

cType2Type :: TH.Type -> HSE.Type
cType2Type (TVar (Tyvar i k)) = TyVar $ Ident i 
cType2Type (TCon "->"       _) = TyCon $ Special FunCon
cType2Type (TCon "[]"       _) = TyCon $ Special ListCon
cType2Type (TCon "(,)"      _) = TyCon $ Special $ TupleCon Boxed 2 
cType2Type (TCon "(,,)"     _) = TyCon $ Special $ TupleCon Boxed 3
cType2Type (TCon "(,,,)"    _) = TyCon $ Special $ TupleCon Boxed 4
cType2Type (TCon "(,,,,)"   _) = TyCon $ Special $ TupleCon Boxed 5
cType2Type (TCon "(,,,,,)"  _) = TyCon $ Special $ TupleCon Boxed 6
cType2Type (TCon "(,,,,,,)" _) = TyCon $ Special $ TupleCon Boxed 7
cType2Type (TCon i          _) = TyCon (UnQual $ Ident $ i )
cType2Type (TAp  (TAp (TCon "->" _) t1) t2 ) = 
  TyInfix (cType2Type t1) (Special FunCon) (cType2Type t2)
cType2Type (TAp (TCon "[]" _) t1       ) = TyList (cType2Type t1)
cType2Type (TAp t1 t2       ) = TyApp (cType2Type t1) (cType2Type t2)
cType2Type (TGen n          ) = TyVar (Ident $ "t" ++ (show n))
 
cPred2Asst :: Pred -> Asst 
cPred2Asst (IsIn i t) = ClassA (UnQual $ Ident i) (map cType2Type t)
 
cKind2Kind :: TH.Kind -> HSE.Kind 
cKind2Kind Star = KindStar
cKind2Kind (Kfun k1 k2) = KindFn (cKind2Kind k1) (cKind2Kind k2)

cAssump :: Assump -> (String,HSE.Type)
cAssump ( i :>: s) = (i, cScheme2Type s)