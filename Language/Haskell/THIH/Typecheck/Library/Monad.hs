module Language.Haskell.THIH.Typecheck.Library.Monad where

--import Language.Haskell.THIH.Combinators
import Language.Haskell.THIH.Typecheck.Library.Prelude
import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.Typecheck.Internals(mkInst)
import Language.Haskell.THIH.BasicTypes
import Control.Applicative

moduleMonad = ModuleH []  monadTypeClasses monadInstances monadFunctions

monadTypeClasses =  [tcMonadPlus] 

monadFunctions
 =  ["msum" :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonadPlus (TGen 0)] :=>
	    (TAp tList (TAp (TGen 0) (TGen 1)) --> TAp (TGen 0) (TGen 1))),
     "join" :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp (TGen 0) (TAp (TGen 0) (TGen 1)) --> TAp (TGen 0) (TGen 1))),
     "when" :>:
       Forall [Kfun Star Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (tBool --> TAp (TGen 0) tUnit --> TAp (TGen 0) tUnit)),
     "unless" :>:
       Forall [Kfun Star Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (tBool --> TAp (TGen 0) tUnit --> TAp (TGen 0) tUnit)),
     "liftM2" :>:
       Forall [Kfun Star Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TGen 3) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2) --> TAp (TGen 0) (TGen 3))),
     "ap" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp (TGen 0) (TGen 1 --> TGen 2) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2))),
     "guard" :>:
       Forall [Kfun Star Star]
	 ([isIn1 cMonadPlus (TGen 0)] :=>
	    (tBool --> TAp (TGen 0) tUnit)),
     "mapAndUnzipM" :>:
       Forall [Kfun Star Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TAp (TGen 0) (TAp (TAp tTuple2 (TGen 2)) (TGen 3))) --> TAp tList (TGen 1) --> TAp (TGen 0) (TAp (TAp tTuple2 (TAp tList (TGen 2))) (TAp tList (TGen 3))))),
     "zipWithM" :>:
       Forall [Kfun Star Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TAp (TGen 0) (TGen 3)) --> TAp tList (TGen 1) --> TAp tList (TGen 2) --> TAp (TGen 0) (TAp tList (TGen 3)))),
     "zipWithM_" :>:
       Forall [Kfun Star Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TAp (TGen 0) (TGen 3)) --> TAp tList (TGen 1) --> TAp tList (TGen 2) --> TAp (TGen 0) tUnit)),
     "foldM" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TAp (TGen 0) (TGen 1)) --> TGen 1 --> TAp tList (TGen 2) --> TAp (TGen 0) (TGen 1))),
     "filterM" :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TAp (TGen 0) tBool) --> TAp tList (TGen 1) --> TAp (TGen 0) (TAp tList (TGen 1)))),
     "liftM" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2))),
     "liftM3" :>:
       Forall [Kfun Star Star, Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TGen 3 --> TGen 4) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2) --> TAp (TGen 0) (TGen 3) --> TAp (TGen 0) (TGen 4))),
     "liftM4" :>:
       Forall [Kfun Star Star, Star, Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TGen 3 --> TGen 4 --> TGen 5) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2) --> TAp (TGen 0) (TGen 3) --> TAp (TGen 0) (TGen 4) --> TAp (TGen 0) (TGen 5))),
     "liftM5" :>:
       Forall [Kfun Star Star, Star, Star, Star, Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TGen 2 --> TGen 3 --> TGen 4 --> TGen 5 --> TGen 6) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2) --> TAp (TGen 0) (TGen 3) --> TAp (TGen 0) (TGen 4) --> TAp (TGen 0) (TGen 5) --> TAp (TGen 0) (TGen 6)))]



tcMonadPlus = TypeClass [IsIn cMonad [atype]] cMonadPlus asig
              [mzeroMfun,mplusMfun]
cMonadPlus = "MonadPlus"
mzeroMfun  = "mzero" :>: (Forall [Kfun Star Star, Star]
                          ([isIn1 cMonadPlus (TGen 0)] :=> 
                           (TAp (TGen 0) (TGen 1))))
mplusMfun  = "mplus" :>: (Forall [Kfun Star Star, Star]
                          ([isIn1 cMonadPlus (TGen 0)] :=> 
                           (TAp (TGen 0) (TGen 1) -->
                            TAp (TGen 0) (TGen 1) -->
                            TAp (TGen 0) (TGen 1))))

monadInstances = Instance <$> instsMonadPlus

instsMonadPlus
 = [mkInst [] ([] :=> isIn1 cMonadPlus tMaybe),
    mkInst [] ([] :=> isIn1 cMonadPlus tList)]