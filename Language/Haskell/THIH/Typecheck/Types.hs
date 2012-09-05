-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Types
-- Copyright   :  (c) Shayan Najd, Mark P. Jones
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
module Language.Haskell.THIH.Typecheck.Types where

import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Syntax  

-----------------------------------
-- Internal Representation of Types
-----------------------------------                           
data Tyvar        = Tyvar Id Kind
                  deriving (Eq,Show)
--data Tycon        = Tycon Id Kind
--                  deriving (Eq,Show)
--data VarBind      = VarBind (Id, Kind)
--                  deriving (Eq,Show)                             
data Pred         = IsIn Id [Type]
                  deriving (Eq,Show)
data Type         = TVar Tyvar 
                  | TCon Id Kind
                  | TAp  Type Type 
                  | TGen Int
                  deriving (Eq,Show)                      
data Qual t       = [Pred] :=> t
                  deriving (Eq,Show)
data Scheme       = Forall [Kind] 
                    (Qual Type)
                  deriving (Eq,Show)   


type Kinded e = e Scheme 
       

data TypeSynonym  = TypeSynonym Id [Kind] Type -- not sure!
                  deriving (Eq,Show)
data DataType     = DataType Id Kind [Assump]
                  deriving (Eq,Show)
data TypeClass    = TypeClass [Pred] Id [Tyvar] [Assump] --[Instance]
                  deriving (Eq,Show)
data Instance     = Instance (Qual Pred)  
                  deriving (Eq,Show)
data Module       = Module [TypeSynonym] [DataType] 
                    [TypeClass] [Instance](Kinded Program)
                  deriving (Eq,Show)
data ModuleHeader = ModuleH [DataType][TypeClass] [Instance][Assump]
                  deriving (Eq,Show)

type Class    = ([Tyvar], [Pred], [Inst])
type Inst     = Qual Pred                             
                         
type ConEnv    = [(Id,Kind)]
data Assump    = Id :>: Scheme  deriving (Eq,Show)
data ClassEnv = ClassEnv { classes  :: Id -> Maybe Class,
                           defaults :: [Type], 
                           cls :: [(Id,Class)]}  

toScheme      :: Type -> Scheme
toScheme t = Forall [] ([] :=> t)


getName :: Type -> Id
getName (TCon x k) = x
-------------------------- 
-- Basic Types
--------------------------                        
tArrow   = TCon  "->" (Kfun Star (Kfun Star Star))
tChar    = TCon  "Char" Star
tInt     = TCon "Int"  Star
tDouble  = TCon "Double" Star
tInteger = TCon "Integer" Star
tList    = TCon  "[]" (Kfun Star Star)

list       :: Type -> Type
list t      = TAp tList t

tString    :: Type
tString     = list tChar

infixr      4 -->
(-->)      :: Type -> Type -> Type
a --> b    = TAp (TAp tArrow a) b

atyvar = Tyvar "a" Star
atype  = TVar atyvar
asig   = [atyvar]

mtyvar = Tyvar "m" (Kfun Star Star)
mtype  = TVar mtyvar
msig   = [mtyvar]

---------------------------------
-- Basic Types For Kind Inference
---------------------------------
star :: Type
star = TCon "Star" Star -- represents kind star

constraint :: Type
constraint = TCon "Constraint" Star -- represents kind constraint

kIClassEnv :: ClassEnv
kIClassEnv = initialEnv {defaults=[]}

{-
-- Sort level data constructors
kIConEnv :: ConEnv
kIConEnv = [("Star",Star) -- star kind has sort star
           ,("Constraint",Star) -- constraint kind has sort star
           ,("->", Kfun Star (Kfun Star Star) )] 
           -- kind level function has  -}
sortArrow :: Assump
sortArrow = ( "t->" :>: (toScheme $  
                         star --> star --> star))

kiAssump :: [Assump]
kiAssump =  kIAssump ++ [sortArrow]

kIAssump :: [Assump]
kIAssump = [ "==>" 
             :>: (toScheme $ 
                  constraint --> star --> star )
           , "constraint" 
             :>: (toScheme $  
                  constraint)
           , "star" 
             :>: (toScheme $ 
                  star)
           , "<+>"   
             :>: (toScheme $ 
                  star --> star --> star) 
           , "<&>"  
             :>: (toScheme $
                  constraint --> constraint --> constraint)
           , "<:>"
             :>: 
             (Forall [Star] 
              ([] :=> 
               (((TGen 0) --> star)--> constraint --> constraint )))]
           ++ [n :>:  (toScheme $
                       (foldl1   (-->)  (   [star |_ <- [1..i] ] 
                                            ++ [TCon n Star] )))
              | i <- [0..8] , let n = ("Prod" ++ (show i)) ] 
           -- max. 20 tyvars are accepted
           
---------------------------------
-- Basic ClassEnv Functions 
---------------------------
isIn1       :: Id -> Type -> Pred
isIn1 i t    = IsIn i [t]

initialEnv :: ClassEnv
initialEnv  = ClassEnv { classes  = \i -> fail "class not defined"
                       , defaults = [tInteger, tDouble]
                       ,cls =[] }