-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Internals
-- Copyright   :  (c) Shayan Najd, Mark P. Jones
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Typecheck.Internals where

import Language.Haskell.THIH.Typecheck.Types 
import Language.Haskell.THIH.BasicTypes

import Data.List ((\\),union,partition,intersect,nub)
import Control.Monad (foldM,msum)
import Debug.Trace

--------------------------------------- 
-- Types
---------------------------------------                        
class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]
instance Types Type where
  apply s (TVar u)  = case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply s t         = t
  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv t         = []
instance Types a => Types [a] where
  apply s = map (apply s)
  tv      = nub . concat . map tv
instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t
instance Types Pred where
  apply s (IsIn i ts) = IsIn i (apply s ts)
  tv (IsIn i ts)      = tv ts
instance Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (i :>: sc)      = tv sc
instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt)      = tv qt  


class SubsTCon a where
  subsTCon :: [(Id,Type)] -> a -> a

instance SubsTCon  Type where  
  subsTCon s x@(TVar (Tyvar i _)) 
    | Just t <- lookup i s = t 
    | True                 = x                         
  subsTCon s x@(TCon i _)                             
    | Just t <- lookup i s = t 
    | True                 = x
  subsTCon s (TAp t1 t2)    = TAp (subsTCon s t1) (subsTCon s t2)            
  subsTCon s x              = x

instance SubsTCon Pred where
  subsTCon s (IsIn i ps) = IsIn i (map (subsTCon s) ps)
                                                  
instance SubsTCon Scheme where
  subsTCon s (Forall ks (ps :=> t)) = Forall ks 
                                      ((map (subsTCon s) ps)
                                       :=> (subsTCon s t))

----------------------------------------------
-- Instantiate  
----------------------------------------------
class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst ts t         = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)
-----------------------------------      
-- Unify
----------------------------------- 
class Unify t where
  mgu :: Monad m =>  t -> t -> m Subst
instance Unify Type where
  mgu (TAp l r) (TAp l' r') = do 
    s1 <- mgu  l l'
    s2 <- mgu  (apply s1 r) (apply s1 r')
    return (s2 @@ s1)
  mgu (TVar u) t        = varBind  u t
  mgu t (TVar u)        = varBind  u t
  mgu (TCon tc1 k1) (TCon tc2 k2)
             | (tc1,k1)==(tc2,k2) = return nullSubst
  mgu t1 t2             = fail $ "types " ++ (show t1) ++ " and "
                                    ++ (show t2) ++ " do not unify" 
    
instance (Unify t, Types t) => Unify [t] where
  mgu (x:xs) (y:ys) = do s1 <- mgu  x y
                         s2 <- mgu  (apply s1 xs) (apply s1 ys)
                         return (s2 @@ s1)
  mgu []     []     = return nullSubst
  mgu _      _      = fail "lists do not unify"
instance Unify Pred where
   mgu  = lift $ mgu 
-----------------------------------
-- Matching
----------------------------------- 
class Match t where
  match :: Monad m =>  t -> t -> m Subst
instance Match Type where
  match  (TAp l r) (TAp l' r') = do sl <- match  l l'
                                    sr <- match  r r'
                                    merge sl sr
  match  (TVar u)   t | kind  u == kind  t = return (u +-> t)
  match  (TCon tc1 k1) (TCon tc2 k2)
           | (tc1,k1)==(tc2,k2)= return nullSubst
  match  t1 t2                 = fail "types do not match"
instance Match t => Match [t] where
   match  ts ts' = do ss <- sequence (zipWith (match ) ts ts')
                      foldM merge nullSubst ss
instance Match Pred where
   match  = lift $ match                         
-----------------------------------      
-- HasKind
-----------------------------------      
class HasKind t where
  kind ::  t -> Kind
instance HasKind Tyvar where
  kind (Tyvar v k) = k                        
instance HasKind Type where
  kind  (TCon v k)  = k
  kind  (TVar u)  = kind  u
  kind  (TAp t x) = case (kind  t) of
    (Kfun _ k) -> k
    _ -> error $ "Kinds do not match!" 
-----------------------------------
-- ClassEnv
-----------------------------------
type EnvTransformer = ClassEnv -> Maybe ClassEnv 

mkInst      :: Instantiate a => [Kind] -> a -> a
mkInst ks = inst ts 
 where ts   = zipWith (\v k -> TVar (Tyvar v k)) vars ks
       vars = [ [c] | c <-['a'..'z'] ] ++
              [ c : show n | n <-[0::Int ..], c<-['a'..'z'] ]
 
predHead            :: Pred -> Id
predHead (IsIn i ts) = i  
  
sig       :: ClassEnv -> Id -> [Tyvar]
sig ce i   = case classes ce i of Just (vs, is, its) -> vs

super     :: ClassEnv -> Id -> [Pred]
super ce i = case classes ce i of Just (vs, is, its) -> is

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case classes ce i of Just (vs, is, its) -> its

defined :: Maybe a -> Bool
defined (Just x) = True
defined Nothing  = False

modify       :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce{classes = \j -> if i==j then Just c
                                           else classes ce j
                  ,cls = (i, c) : (cls ce)}
                
infixr 5 <:>
(<:>)       :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do ce' <- f ce
                  g ce'
addClass      :: Id -> [Tyvar] -> [Pred] -> EnvTransformer
addClass i vs ps ce
 | defined (classes ce i)              = fail "class already defined"
 | any (not . defined . classes ce . predHead) ps = fail "superclass not defined"
 | otherwise                           = return (modify ce i (vs, ps, []))

addInst                        :: [Pred] -> Pred -> EnvTransformer
addInst  ps p@(IsIn i _) ce
 | not (defined (classes ce i)) = fail "no class for instance"
 | any (overlap  p) qs           = fail "overlapping instance"
 | otherwise                    = return (modify ce i c)
   where its = insts ce i
         qs  = [ q | (_ :=> q) <- its ]
         c   = (sig ce i, super ce i, (ps:=>p) : its)                

overlap       ::  Pred -> Pred -> Bool
overlap  p q    = defined (mgu  p q)

bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i ts)
 = p : concat (map (bySuper ce) supers)
   where supers = apply s (super ce i)
         s      = zip (sig ce i) ts

byInst                   :: ClassEnv -> Pred -> Maybe [Pred]
byInst  ce p@(IsIn i t)    = msum [ tryInst it | it <- insts ce i ]
 where tryInst (ps :=> h) = do u <- match  h p
                               Just (map (apply u) ps)

entail        ::  ClassEnv -> [Pred] -> Pred -> Bool
entail  ce ps p = any (p `elem`) (map (bySuper ce) ps) ||
                 case byInst  ce p of
                   Nothing -> False
                   Just qs -> all (entail  ce ps) qs

simplify   :: ([Pred] -> Pred -> Bool) -> [Pred] -> [Pred]
simplify ent = loop []
 where loop rs []                      = rs
       loop rs (p:ps) | ent (rs++ps) p = loop rs ps
                      | otherwise      = loop (p:rs) ps

reduce      ::  ClassEnv -> [Pred] -> [Pred]
reduce  ce    = simplify (scEntail ce) . elimTauts  ce

elimTauts   ::  ClassEnv -> [Pred] -> [Pred]
elimTauts  ce ps = [ p | p <- ps, not (entail  ce [] p) ]

scEntail        :: ClassEnv -> [Pred] -> Pred -> Bool
scEntail ce ps p = any (p `elem`) (map (bySuper ce) ps)              

type Ambiguity = (Tyvar, [Pred])
ambiguities         :: ClassEnv -> [Tyvar] -> [Pred] -> [Ambiguity]
ambiguities  ce vs ps = [ (v, filter (elem v . tv) ps) | v <- tv ps \\ vs ]

numClasses :: [Id]
numClasses  = ["Num", "Integral", "Floating", "Fractional",
               "Real", "RealFloat", "RealFrac"]

stdClasses :: [Id]
stdClasses  = ["Eq", "Ord", "Show", "Read", "Bounded", "Enum", "Ix",
               "Functor", "Monad", "MonadPlus"] ++ numClasses

candidates           ::  ClassEnv -> Ambiguity -> [Type]
candidates  ce (v, qs) = [ t' | let is = [ i | IsIn i t <- qs ]
                                    ts = [ t | IsIn i t <- qs ]
                                      ,all ([TVar v]==) ts,
                                       any (`elem` numClasses) is,
                                       all (`elem` stdClasses) is,
                                       t' <- defaults ce,
                                       all (entail  ce []) 
                                       [ IsIn i [t'] | i <- is ] ]
                           
withDefaults :: Monad m => ([Ambiguity] -> [Type] -> a)
                  ->  ClassEnv -> [Tyvar] -> [Pred] -> m a
withDefaults f  ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     =  return (f vps (map head tss))
      where vps = ambiguities  ce vs ps
            tss = map (candidates  ce) vps

defaultedPreds :: Monad m =>  ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds  = withDefaults (\vps ts -> concat (map snd vps))

defaultSubst   :: Monad m =>  ClassEnv -> [Tyvar] -> [Pred] -> m Subst
defaultSubst    = withDefaults (\vps ts -> zip (map fst vps) ts)
 
split :: Monad m =>  ClassEnv -> [Tyvar] -> [Tyvar] -> [Pred]
                      -> m ([Pred], [Pred])
split  ce fs gs ps = do let ps' = reduce  ce ps
                            (ds, rs) = partition (all (`elem` fs) . tv) ps'
                        rs' <- defaultedPreds  ce (fs++gs) rs
                        return (ds, rs \\ rs')

instances  :: [Inst] -> EnvTransformer
instances   =   
              foldr1 (<:>) . map (\(ps:=>p) -> addInst  ps p)                    
--------------------------------------- 
-- Scheme
---------------------------------------  
quantify      ::  [Tyvar] -> Qual Type -> Scheme
quantify  vs qt = Forall ks (apply s qt)
 where vs' = [ v | v <- tv qt, v `elem` vs ]
       ks  = map (kind ) vs'
       s   = zip vs' (map TGen [0..])
--------------------------------------- 
-- Subst
---------------------------------------  
type Subst  = [(Tyvar, Type)]  
nullSubst  :: Subst
nullSubst   = []

(+->)      :: Tyvar -> Type -> Subst
u +-> t     = [(u, t)]

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

merge      :: Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1++s2) else fail "merge fails"
 where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                   (map fst s1 `intersect` map fst s2)
--------------------------------------- 
-- TIMonad
---------------------------------------               
newtype TI a   = TI (Subst -> Int -> (Subst, Int, a))
instance Monad TI where
  return x   = TI (\s n -> (s,n,x))
  TI f >>= g = TI (\s n -> case f s n of
                            (s',m,x) -> let TI gx = g x
                                        in  gx s' m)

runTI       :: TI a -> a
runTI (TI f) = x where (s,n,x) = f nullSubst 0

getSubst   :: TI Subst
getSubst    = TI (\s n -> (s,n,s))

unify      ::   Type -> Type -> TI ()
unify  t1 t2 = do s <- getSubst
                  u <- mgu  (apply s t1) (apply s t2)
                  extSubst u

trim       :: [Tyvar] -> TI ()
trim vs     = TI (\s n ->
                  let s' = [ (v,t) | (v,t) <-s, v `elem` vs ]
                      force = length (tv (map snd s'))
                  in  force `seq` (s', n, ()))

extSubst   :: Subst -> TI ()
extSubst s' = TI (\s n -> (s'@@s, n, ()))

newTVar    :: Kind -> TI Type
newTVar k   = TI (\s n -> let v = Tyvar (enumId n) k
                          in  (s, n+1, TVar v))

freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)

---------------------------------------
-- Unification
---------------------------------------
varBind :: Monad m =>   Tyvar -> Type -> m Subst
varBind   u t | t == TVar u      = return nullSubst
                | u `elem` tv t    = fail "occurs check fails"
                | kind  u /= kind  t = fail $ 
                                       "kinds of " 
                                       ++ (show u) ++ 
                                       " and " 
                                       ++ (show t) ++
                                       " do not match!"
                | otherwise        = return (u +-> t)
lift m (IsIn i ts) (IsIn i' ts')
         | i == i'   = m ts ts'
         | otherwise = fail "classes differ"
--------------------------------------- 
-- Assump
---------------------------------------
find                 :: Monad m => Id -> [Assump] -> m Scheme
find i []             = fail ("unbound identifier: " ++ i)
find i ((i':>:sc):as) = if i==i' then return sc else find i as
--------------------------------------- 
-- ID
---------------------------------------
enumId  :: Int -> Id
enumId n = "v" ++ show n    
               
-----------------------------------      
-- KindInference
----------------------------------- 
--inferKind :: SSchme -> Scheme 
--inferKind (SForall vars preds st) = undefined



{-
cScheme :: HSE.Type -> Scheme
cScheme (TyForall Nothing [] t) = 
  Forall []  ([]:=>(cType t))                      
cScheme (TyForall Nothing (p:ps) t) = error $ "Type " ++ (prettyPrint t) 
            ++  " doesn't have the correct format!"
cScheme (TyForall (Just m) ps t) 
  | (length [1 | UnkindedVar _ <- m]) == 0 =  
   let 
     t' = cType t
     ps' = map cPred ps
     vars  = zip m [0.. (length m) - 1]                                         
     t'' = foldl (\tt ((KindedVar n k),i) -> 
                  apply (Tyvar (cId n) Star +->TGen i ) tt) t' vars
     ps'' =foldl (\tt ((KindedVar n k),i) -> 
                  apply (Tyvar (cId n) Star +->TGen i ) tt) ps' vars
     ks = [cKind k|KindedVar _ k <- m]     
    in 
    Forall ks (ps'' :=> t'')  
     
  | otherwise = error $ "These type variables need to be explicitly kinded: " 
                ++ ( show [prettyPrint t | UnkindedVar _ <- m])
cScheme t = Forall []  ([]:=>(cType t))                  

-}
--cType2Expression :: 
 
