-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Combinators
-- Copyright   :  (c) Shayan Najd , Mark P. Jones
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.THIH.Typecheck.Combinators 
       (module Syn,module Pr,module Tys,module BTys,
        ap,evar,elit,econst,elet,toBg,pNil
       ,pCons, eNil,eCons ,ecase ,eif,elambda,eguarded
       ,efail,esign,eCompFrom,eCompGuard,eCompLet,eListRet)  
       where
import Language.Haskell.THIH.BasicTypes as BTys
import Language.Haskell.THIH.Syntax as Syn
import Language.Haskell.THIH.Typecheck.Types as Tys
import Language.Haskell.THIH.Typecheck.Library.Prelude as Pr
import Language.Haskell.THIH.Typecheck.Internals 
import Control.Applicative

gd (i :>: _) = i

ap              = foldl1 Ap
evar v          = (Var v)
elit l          = (Lit l)
econst :: Id -> Expr e
econst c        = Var c
elet e f        = foldr Let f (map toBg e)

toBg           :: [(Id, Maybe e, [Alt e])] -> BindGroup e
toBg g          = BindGroup 
                  [Expl v  t  alts | (v, Just t, alts) <- g ]
                  (filter (not . null) [[Impl v alts  | (v,Nothing,alts) <- g]])

pNil            = PCon (gd nilCfun) []
pCons x y       = PCon (gd consCfun) [x,y]

eNil            = econst (gd nilCfun)
eCons x y       = ap [ econst (gd consCfun), x, y ]

{-
ecase           = Case
elambda         = Lam
eif             = If
-}

ecase d as      = elet [[ ("_case",
                           Nothing,
                           [(Alt [p] e) | (p,e) <- as]) ]]
                       (ap [evar "_case", d])
eif c t f       = ecase c [(PCon (gd trueCfun) [], t)
                          ,(PCon (gd falseCfun) [], f)]
elambda alt     = elet [[ ("_lambda",
                           Nothing,
                           [alt]) ]]
                             (evar "_lambda")
eguarded        = foldr (\(c,t) e -> eif c t e) efail
efail           =  Var "FAIL"
esign e t       = elet [[ ("_val", Just t, [(Alt [] e)]) ]] (evar "_val")

eCompFrom p e c = ap [ econst (gd mbindMfun), e, elambda (Alt [p] c) ]
eCompGuard e c  = eif e c eNil
eCompLet bgs c  = elet bgs c             

eListRet e      = eCons e eNil



