module Language.Haskell.THIH.Typecheck.Library.Maybe where

 
import Language.Haskell.THIH.Typecheck.Library.Prelude
import Language.Haskell.THIH.Syntax 
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.BasicTypes
 

moduleMaybe = ModuleH [] [] maybeFunctions

maybeFunctions
 =  ["isJust" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tMaybe (TGen 0) --> tBool)),
     "isNothing" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tMaybe (TGen 0) --> tBool)),
     "fromJust" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tMaybe (TGen 0) --> TGen 0)),
     "fromMaybe" :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 --> TAp tMaybe (TGen 0) --> TGen 0)),
     "maybeToList" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tMaybe (TGen 0) --> TAp tList (TGen 0))),
     "listToMaybe" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tMaybe (TGen 0))),
     "catMaybes" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TAp tMaybe (TGen 0)) --> TAp tList (TGen 0))),
     "mapMaybe" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TAp tMaybe (TGen 1)) --> TAp tList (TGen 0) --> TAp tList (TGen 1)))]
