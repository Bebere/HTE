-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Typecheck
-- Copyright   :  (c) Shayan Najd, Mark P. Jones
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Typecheck.Typecheck where

import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.Typecheck.Internals

import Debug.Trace
import Data.List ((\\),intersect,union)

type Infer e t =  ClassEnv -> [Assump] -> e -> TI ([Pred], t) 

tiLit            :: Literal -> TI ([Pred],Type)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInt _)  = do v <- newTVar Star
                       return ([IsIn "Num" [v]], v)
tiLit (LitStr _)  = return ([], tString)
tiLit (LitRat _)  = do v <- newTVar Star
                       return ([IsIn "Fractional" [v]], v)                      
--------------------------------
tiPat ::  [Assump] -> Pat -> TI ([Pred], [Assump], Type)
tiPat  as (PVar i) = do v <- newTVar Star
                        return ([], [i :>: toScheme v], v)
tiPat  as PWildcard   = do v <- newTVar Star
                           return ([], [], v)
tiPat  as (PAs i pat) = do (ps, as, t) <- tiPat  as pat
                           return (ps, (i:>:toScheme t):as, t)
tiPat  as (PLit l) = do (ps, t) <- tiLit l
                        return (ps, [], t)
tiPat  as (PNpk i k)  = do t <- newTVar Star
                           return ([IsIn "Integral" [t]], [i:>:toScheme t], t)
tiPat  as (PCon i pats)
   = do sc <- find i as
        (ps,as,ts) <- tiPats  as pats
        t'         <- newTVar Star
        (qs :=> t) <- freshInst sc
        unify  t (foldr (-->) t' ts)
        return (ps++qs, as, t')
tiPat  as (PLazy pat) = tiPat  as pat
--------------------------------
tiPats     ::  [Assump] -> [Pat] -> TI ([Pred], [Assump], [Type])
tiPats  as pats = do psasts <- mapM (tiPat  as) pats
                     let ps = concat [ ps' | (ps',_,_) <- psasts ]
                         as = concat [ as' | (_,as',_) <- psasts ]
                         ts = [ t | (_,_,t) <- psasts ]
                     return (ps, as, ts)
--------------------------------
tiExpr                       ::  Infer (Kinded Expr) Type
tiExpr  ce as (Var i)          = do sc         <- find i as
                                    (ps :=> t) <- freshInst sc
                                    return (ps, t)
--tiExpr  ce as (Const (i:>:sc)) = do (ps :=> t) <- freshInst sc
--                                      return (ps, t)
tiExpr  ce as (Lit l)          = do (ps,t) <- tiLit l
                                    return (ps, t)
tiExpr  ce as (Ap e f)         = do (ps,te) <- tiExpr  ce as e
                                    (qs,tf) <- tiExpr  ce as f
                                    t       <- newTVar Star
                                    unify  (tf --> t) te
                                    return (ps++qs, t)
tiExpr  ce as (Let bg e)       = do (ps, as') <- tiBindGroup  ce as bg
                                    (qs, t)   <- tiExpr  ce (as' ++ as) e
                                    return (ps ++ qs, t)

tiExpr  ce as (Lam alt)
  = tiAlt  ce as alt

tiExpr  ce as (Case e branches)
  = do (ps, t) <- tiExpr  ce as e
       v       <- newTVar Star
       let tiBr (pat, f)
            = do (ps, as',t') <- tiPat  as pat
                 unify   t t'
                 (qs, t'')   <- tiExpr  ce (as'++as) f
                 unify   v t''
                 return (ps++qs)
       pss <- mapM tiBr branches
       return (ps++concat pss, v)
{-    
tiExpr  ce as (If e e1 e2)
  = do (ps,t)   <- tiExpr  ce as e
       unify   t tBool
       (ps1,t1) <- tiExpr  ce as e1
       (ps2,t2) <- tiExpr  ce as e2
       unify   t1 t2
       return (ps++ps1++ps2, t1)-}
--------------------------------
tiAlt                ::   Infer (Kinded Alt) Type
tiAlt  ce as (Alt pats e) = do (ps, as', ts) <- tiPats  as pats
                               (qs,t)  <- tiExpr  ce (as'++as) e
                               return (ps++qs, foldr (-->) t ts)
--------------------------------
tiAlts             ::    ClassEnv -> [Assump] -> [Kinded Alt] -> 
                      Type -> TI [Pred]
tiAlts  ce as alts t = do psts <- mapM (tiAlt  ce as) alts
                          mapM (unify  t) (map snd psts)
                          return (concat (map fst psts))
--------------------------------
tiExpl ::    ClassEnv -> [Assump] -> Kinded Expl -> TI [Pred]
tiExpl  ce as (Expl i sc alts)
        = do (qs :=> t) <- freshInst sc
             ps         <- tiAlts  ce as alts t
             s          <- getSubst
             let qs'     = apply s qs
                 t'      = apply s t
                 fs      = tv (apply s as)
                 gs      = tv t' \\ fs
                 sc'     = quantify  gs (qs':=>t')
                 ps'     = filter (not . entail  ce qs') (apply s ps)
             (ds,rs)    <- split  ce fs gs ps'
             if sc /= sc' then
                 fail "signature too general"
               else if not (null rs) then
                 fail "context too weak"
               else
                 return ds
--------------------------------                 
tiImpls         ::  Infer [Kinded Impl] [Assump]
tiImpls  ce as bs 
  = do ts <- mapM (\_ -> newTVar Star) bs
       let is    = map (\(Impl x _) -> x) bs
           scs   = map toScheme ts
           as'   = zipWith (:>:) is scs ++ as
           altss = map (\(Impl _ x) -> x) bs
       pss <- sequence (zipWith (tiAlts  ce as') altss ts)
       s   <- getSubst
       let ps'     = apply s (concat pss)
           ts'     = apply s ts
           fs      = tv (apply s as)
           vss     = map tv ts'
           gs      = foldr1 union vss \\ fs
       (ds,rs) <- split  ce fs (foldr1 intersect vss) ps'
       if restricted bs then
         let gs'  = gs \\ tv rs
             scs' = map (quantify  gs' . ([]:=>)) ts'
         in return (ds++rs, zipWith (:>:) is scs')
         else
         let scs' = map (quantify  gs . (rs:=>)) ts'
         in return (ds, zipWith (:>:) is scs')
         where                        
           restricted   ::   [Kinded Impl] -> Bool
           restricted bs = False -- any simple bs
           --where simple (i,alts) = any (null . fst) alts
--------------------------------
tiBindGroup ::  Infer (Kinded BindGroup) [Assump]
tiBindGroup  ce as (BindGroup es iss) =
  do let as' = [ v:>:sc | Expl v sc alts <- es ]
     (ps, as'') <- tiSeq tiImpls  ce (as'++as) iss
     qss        <- mapM (tiExpl  ce (as''++as'++as)) es
     return (ps++concat qss, as''++as')
--------------------------------
tiSeq                  :: Infer bg [Assump] -> Infer [bg] [Assump]
tiSeq ti  ce as []       = return ([],[])
tiSeq ti  ce as (bs:bss) = do (ps,as')  <- ti  ce as bs
                              (qs,as'') <- tiSeq ti  ce (as'++as) bss
                              return (ps++qs, as''++as')
--------------------------------                                
tiProgram ::   
   ClassEnv -> [Assump] -> (Kinded Program) -> [Assump]
tiProgram  ce as  (Program bgs) = runTI $
                      do (ps, as') <- tiSeq tiBindGroup  ce as bgs
                         s         <- getSubst
                         let rs     = reduce  ce (apply s ps)
                         s'        <- defaultSubst  ce [] rs
                         return (apply (s'@@s) as')
--------------------------------
tiBindGroup'  ce as bs = do (ps,as') <- tiBindGroup  ce as bs
                            trim (tv (as'++as))
                            return (ps,as')
--------------------------------
tiProgram' ::    
                ClassEnv -> [Assump] -> (Kinded Program) -> [Assump]
tiProgram'   ce as (Program bgs) = runTI $
  do (ps, as') <- tiSeq tiBindGroup'  ce as bgs
     s         <- getSubst
     let rs     = reduce  ce (apply s ps)
     s'        <- defaultSubst  ce [] rs
     return (apply (s'@@s) as')