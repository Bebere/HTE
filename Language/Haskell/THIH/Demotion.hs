-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Demotion
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Demotion where

import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.SurfaceTypes
import Control.Applicative
import Debug.Trace


infixr 5 ==>
(==>) :: Expr e -> Expr e -> Expr e
t1 ==> t2 = Ap (Ap (Var "==>") t1) t2

infixr 4 <+>
(<+>) :: Expr e -> Expr e -> Expr e
t1 <+> t2 = Ap (Ap (Var "<+>") t1) t2

infixr 4 <:>
(<:>) ::  Expr e -> Expr e  -> Expr e
t1 <:> t2 = Ap (Ap (Var "<:>") t1) t2

infixr 4 <&>
(<&>) :: Expr e -> Expr e -> Expr e
t1 <&> t2 = Ap (Ap (Var "<&>") t1) t2

demoteCTX :: [SPred] -> Expr e
demoteCTX []    = Var  "constraint"
demoteCTX [asst] = demoteAsst asst
demoteCTX assts@(_:_) 
  = foldl1 (<&>) (demoteAsst <$> assts)              

demoteAsst :: SPred -> Expr e
demoteAsst (SIsIn id ts) = foldl Ap   
                               (Var $ "t"++id) 
                               (demoteSType <$> ts)

demoteSType :: SType -> Expr e
demoteSType (SVar i) = Var i 
demoteSType (SCon i) = Var $ "t"++i
demoteSType (SApp t1 t2) = Ap (demoteSType t1) (demoteSType t2)

demoteQSType :: SQual SType -> Expr e 
demoteQSType (preds :==> t) =
  (demoteCTX preds) ==> (demoteSType t)

demoteSSchemeP :: SScheme -> Expr e
demoteSSchemeP sc@(SForall vars qt) =  
  Lam (Alt [PCon ("Prod"++ (show $ length vars )) (PVar <$> vars)] 
       (demoteQSType qt)
      ) 

demoteSSchemeL :: SScheme -> Expr e
demoteSSchemeL sc@(SForall [] qt) =  
       (demoteQSType qt)
demoteSSchemeL sc@(SForall vars qt) =  
  Lam (Alt (PVar <$> vars) 
       (demoteQSType qt)
      ) 

demoteSTypeSynonym :: STypeSynonym -> Impl e
demoteSTypeSynonym (STypeSynonym n [] t) =
  Impl ("t"++n) [Alt [] (demoteSType t)]
demoteSTypeSynonym (STypeSynonym n vars t) =
  Impl ("t"++n) [Alt [] (Lam (Alt (PVar <$> vars) (demoteSType t))) ] 

demoteSDataType :: SDataType -> Impl e
demoteSDataType (SDataType i [] its) =
  Impl ("t"++i) [Alt [] 
          (foldl1 (<+>) 
           ((demoteSType . snd) <$> its))]
  
demoteSDataType (SDataType i vars its) =
  Impl ("t"++i) [Alt [] 
                 (Lam (Alt  (PVar <$> vars)  
                       ( foldl1 (<+>) 
                         ((demoteSType . snd) <$> its)
                       )))]

demoteSTypeClass :: STypeClass -> Impl e 
demoteSTypeClass (STypeClass sps i vars ms) =
  Impl ("t"++i) [Alt []
          (Lam (Alt 
                (PVar <$> vars) 
                (foldl1 (<:>) 
                  ( ((demoteSSchemeP . snd) <$> ms) ++ [demoteCTX sps] 
                  )
                 )
               )
          )]
  
demoteSModule :: SModule -> Program e
demoteSModule (SModule syns dta cls _ _ ) =  
  let 
    eSs = demoteSTypeSynonym <$> syns
    eDs = demoteSDataType <$> dta
    eCs = demoteSTypeClass <$> cls
  in  
   Program [BindGroup [] [eSs ++ eDs ++ eCs]] 