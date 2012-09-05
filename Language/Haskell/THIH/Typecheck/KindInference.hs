-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.KindInference
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.THIH.Typecheck.KindInference where

import Control.Applicative((<$>))
import Data.Traversable(traverse)
import Data.Functor.Identity
import Debug.Trace
import Data.List(isPrefixOf)

import Language.Haskell.THIH.Typecheck.Typecheck
import Language.Haskell.THIH.Typecheck.Demotion
import Language.Haskell.THIH.Demotion
import Language.Haskell.THIH.SurfaceTypes
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Typecheck.TypeConversions
import Language.Haskell.THIH.Typecheck.Internals

-----------------------------------------------------
-- Kind Inference
-----------------------------------------------------
  

kiTopModule :: ConEnv -> SModule -> ConEnv
kiTopModule cn m@(SModule syns sds scls _ _ ) =  
  let 
     prog   = demoteSModule m
     ascn   = demoteConEnv cn
     -- ascl   = demoteClassEnv ce
     assmps = 
       tiProgram kIClassEnv 
       (kIAssump++ascn
        -- ++ascl
       ) prog 
     lkp    = toLookup assmps               
  in 
   [ (i,promoteScheme sc ) | STypeSynonym i _ _ <- syns
                           , let Just sc = lookup i lkp] 
   ++
   [ (i,promoteScheme sc ) | SDataType i _ _ <- sds
                           , let Just sc = lookup i lkp]
   ++
   [ (i,promoteScheme sc) | STypeClass _ i _ _ <- scls
                          , let Just sc =  lookup i lkp]
   ++  cn

          
-- kiTypeSynonym = undefined   since there is no free tyvars on rhs  
-- there is no need to a separate kind inference for data constructors 


-- kiDataType = undefined   since there is no existensials (no tyvars)   
-- there is no need to a separate kind inference for data constructors 


kiTypeClass :: ConEnv -> STypeClass -> [(Id,[Kind])]
kiTypeClass cn (STypeClass sups i vars cns) =  let 
  Just sc = lookup i cn 
  ks = splitKinds sc
  in [ (icn , kcn)
       | (icn,ssc) <- cns
       , let
         -- consider  class scoped variables as data constructors     
         t'  = applyS [(v,SCon v)|v <- vars] ssc 
         -- extend the env with constraints of the fake data const.
         cn' = (zip vars ks ) ++cn
         kcn = kiScheme cn' t'] 
{-
kiInstance :: ConEnv -> SInstance -> [Kind]
kiInstance= undefined

cInstance :: ConEnv -> [Kind] -> SInstance -> Instance
cInstance = undefined-}


mkInstance :: ConEnv -> SInstance -> Instance
mkInstance cn (SInstance sps n sts) = let
--   Just sc = lookup i cn 
   ctx  = demoteCTX sps
   ascn = demoteConEnv cn  
   ts   = demoteSType <$> sts          
   vars = tvS (sps :==> (SIsIn n sts)) 
   ex   = (foldl Ap (Var $ "t" ++ n) ts) <&> ctx
   dsc  = Lam (Alt (PVar <$> vars) ex)  
   prog = Program [BindGroup [] [[Impl "tf" $ [Alt [] dsc]]]]
   ["tf":>:sc]  = tiProgram kIClassEnv 
                 (kIAssump ++ ascn) 
                 prog
   ks = promoteType  <$> fetchScheme sc
   
   ps' = cPred cn <$> sps
   ts' = cType cn <$> sts
   subs = zip  ((\v-> Tyvar v Star) <$>  vars) 
          (zipWith (\v k -> TVar $ Tyvar v k) vars ks)
   ps'' = apply subs ps' 
   ts'' = apply subs ts'
   in Instance ( ps''  :=> IsIn n (ts'')) 
 

kiScheme :: ConEnv -> SScheme -> [Kind]
kiScheme cn scc@(SForall tys (ps :==> t)) = 
   let  
    dsc  = demoteSSchemeL scc
    ascn = demoteConEnv  cn
    prog = Program [BindGroup [] [[Impl "tf" $ [Alt [] dsc]]]]
    ["tf":>:sc]  =  
      tiProgram kIClassEnv 
      (kIAssump ++ ascn) 
      prog
   in  
      promoteType  <$> fetchScheme sc
     
mkScheme :: ConEnv -> SScheme -> Scheme 
mkScheme cn ssc = cScheme cn (kiScheme cn ssc) ssc

mkProgram :: ConEnv -> Unkinded Program -> Kinded Program
mkProgram cn up = 
  runIdentity $ 
  traverse (return . (mkScheme cn)) up
  
mkModule :: ConEnv -> SModule -> Module    
mkModule cn m@(SModule syns sds scls is up) = let
  cn'   = kiTopModule   cn  m
  syns' = cTypeSynonym  cn' <$> syns
  sds'  = cDataType     cn' <$> sds
  scls' = (\c-> cTypeClass cn' (kiTypeClass cn' c) c)
          <$> scls
  is'   = --(\i-> cInstance cn' (kiInstance cn' i) i) 
    mkInstance cn'      
    <$> is  
  up'   = mkProgram cn' up
  in  
   Module syns' sds' scls' is' up' 


---------------------------------------------
-- Promoting types
---------------------------------------------
promoteScheme :: Scheme -> Kind
promoteScheme sc = promoteType  $ freshInstStar sc

promoteType :: Type -> Kind
promoteType (TAp (TAp (TCon "->" _) t1) t2) 
  = Kfun (promoteType t1) (promoteType t2)
promoteType (TCon "Star" _) = Star
promoteType (TCon "Constraint" _) = Constraint
 
----------------------------------------------
-- Extracting Kinds from the result types
----------------------------------------------



fetchScheme :: Scheme -> [Type]    
fetchScheme sc = fetch $  freshInstStar sc               

freshInstStar :: Scheme -> Type
freshInstStar (Forall ks ([] :=> t)) =  inst ((\_ -> star) <$> ks) t

fetch :: Type -> [Type]    
fetch (TCon "Star" _) = []
fetch (TAp (TAp (TCon "->" _) x) y) =  x : fetch y
fetch t = Prelude.error $ "Type in a wrong format1 "++ (show t)
{-
fetch :: Type -> [Type]    
fetch (TCon "Star" _) = []
fetch (TAp (TAp (TCon "->" _) x) (TCon "Star" _)) = fetchProducts x  
fetch t = Prelude.error $ "Type in a wrong format1 "++ (show t)

fetchProducts :: Type -> [Type]
fetchProducts t@(TCon c _)  
  | isPrefixOf "Prod" c = []
  | True = Prelude.error $ "Type in a wrong format2 "++ (show t)
fetchProducts (TAp t1 t2) = (fetchProducts t1) ++  [t2]
fetchProducts t = Prelude.error $ "Type in a wrong format "++ (show t)
-}
 