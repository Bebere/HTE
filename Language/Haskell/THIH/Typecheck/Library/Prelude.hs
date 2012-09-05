module Language.Haskell.THIH.Typecheck.Library.Prelude where

import Language.Haskell.THIH.Syntax 
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Typecheck.Internals
import Control.Applicative

modulePrelude = ModuleH preludeTypes preludeTypeClasses preludeInstances 
                preludeFunctions

preludeTypes :: [DataType]
preludeTypes = 
  [dChar,dInt,dInteger,dFloat,dDouble,dArrow,dUnit,dList
  ,dTuple2,dTuple3,dTuple4,dTuple5,dTuple6,dTuple7,dBool,dMaybe
  ,dEither,dOrdering,dIO]
  
preludeTypeClasses :: [TypeClass]  
preludeTypeClasses = 
  [tcEq,tcOrd,tcShow,tcRead,tcBounded
  ,tcEnum,tcFunctor,tcMonad,tcNum,tcReal
  ,tcFractional,tcIntegral,tcRealFrac
  ,tcFloating,tcRealFloat,tcIx]

preludeInstances :: [Instance]
preludeInstances = Instance <$> concat 
                   [instsEq,instsOrd,instsShow,instsRead,instsBounded
                   ,instsEnum,instsFunctor,instsMonad,instsNum,instsReal
                   ,instsFractional,instsIntegral,instsRealFrac
                   ,instsFloating,instsRealFloat,instsIx]

preludeFunctions :: [Assump]
preludeFunctions = importsPrelude


----------------------------------
-- Primitives
-----------------------------------
dChar    = DataType (getName tChar) kChar []
kChar    = Star
--tChar  = TCon  "Char" 
-------------------  
dInt     = DataType (getName tInt) kInt []
kInt     = Star
--tInt     = TCon "Int"  
-------------------
dInteger = DataType (getName tInteger) kInteger []
kInteger = Star
--tInteger = TCon "Integer"  
-------------------
dFloat   = DataType (getName tFloat) kFloat []
kFloat   = Star
tFloat   = TCon "Float" kFloat
-------------------
dDouble  = DataType (getName tDouble) kDouble []
kDouble  = Star
--tDouble  = TCon "Double"  
-------------------
dArrow   = DataType (getName tArrow) kArrow []
kArrow   = Kfun Star (Kfun Star Star) 
--tArrow = TCon  "->" 
-------------------
dUnit     = DataType (getName tUnit) Star [unitCfun] 
kUnit    = Star
tUnit    = TCon "()" kUnit
unitCfun = "()" :>: (Forall [] ([] :=> tUnit))
-------------------
dList    = DataType (getName tList) kList [nilCfun,consCfun]
kList   =  Kfun Star Star
--list       :: Type -> Type
--list t      = TAp tList t
nilCfun  = "[]" :>: (Forall [Star] ([] :=> (TAp tList (TGen 0))))
consCfun = ":"  :>: (Forall [Star]
                     ([] :=> 
                      (TGen 0 -->
                       TAp tList (TGen 0) -->
                       TAp tList (TGen 0))))

-------------------
pair       :: Type -> Type -> Type
pair a b    = TAp (TAp tTuple2 a) b
kindTuple i = foldr (\ _ -> Kfun Star) Star [1..i]

dTuple2  = DataType (getName tTuple2) kTuple2 [tup2Cfun]
kTuple2  = kindTuple 2
tTuple2  = TCon  "(,)" kTuple2
tup2Cfun = "(,)" :>: (Forall [Star, Star]
                      ([] :=> 
                       (TGen 0 -->
                        TGen 1 -->
                        foldl TAp tTuple2 (map TGen [0..1]))))
-------------------
dTuple3  = DataType (getName tTuple3) kTuple3 [tup3Cfun]
kTuple3  = kindTuple 3
tTuple3  = TCon "(,,)"  kTuple3
tup3Cfun = "(,,)" :>: (Forall [Star, Star, Star]
                       ([] :=> 
                        (TGen 0 -->
                         TGen 1 -->
                         TGen 2 -->
                         foldl TAp tTuple3 (map TGen [0..2]))))
-------------------
dTuple4  = DataType (getName tTuple4) kTuple4 [tup4Cfun]
kTuple4  = kindTuple 4
tTuple4  = TCon "(,,,)" kTuple4
tup4Cfun = "(,,,)" :>: (Forall [Star, Star, Star, Star]
                        ([] :=> 
                         (TGen 0 -->
                          TGen 1 -->
                          TGen 2 -->
                          TGen 3 -->
                          foldl TAp tTuple4 (map TGen [0..3]))))
-------------------
dTuple5  = DataType (getName tTuple5) (kTuple5) [tup5Cfun]
kTuple5  = kindTuple 5
tTuple5  = TCon "(,,,,)" kTuple5
tup5Cfun = "(,,,,)" :>: (Forall [Star, Star, Star, Star, Star]
                         ([] :=> 
                          (TGen 0 -->
                           TGen 1 -->
                           TGen 2 -->
                           TGen 3 -->
                           TGen 4 -->
                           foldl TAp tTuple5 (map TGen [0..4]))))
-------------------
dTuple6  = DataType (getName tTuple6) (kTuple6) [tup6Cfun]
kTuple6  = kindTuple 6
tTuple6  = TCon "(,,,,,)" kTuple6
tup6Cfun = "(,,,,,)" :>: (Forall [Star, Star, Star, Star, Star, Star]
                          ([] :=> 
                           (TGen 0 -->
                            TGen 1 -->
                            TGen 2 -->
                            TGen 3 -->
                            TGen 4 -->
                            TGen 5 -->
                            foldl TAp tTuple6 (map TGen [0..5]))))
-------------------
dTuple7  = DataType (getName tTuple7) (kTuple7) [tup7Cfun]
kTuple7  = kindTuple 7
tTuple7  = TCon "(,,,,,,)" kTuple7
tup7Cfun = "(,,,,,,)" :>: (Forall [Star, Star, Star, Star, Star, Star, Star]
                           ([] :=> 
                            (TGen 0 -->
                             TGen 1 -->
                             TGen 2 -->
                             TGen 3 -->
                             TGen 4 -->
                             TGen 5 -->
                             TGen 6 -->
                             foldl TAp tTuple7 (map TGen [0..6]))))
-------------------
dBool     = DataType (getName tBool) (kBool) [falseCfun,trueCfun]
kBool     = Star
tBool     = TCon "Bool" kBool
falseCfun = "False" :>: (Forall [] ([] :=> tBool))
trueCfun  = "True" :>: (Forall [] ([] :=> tBool))
-------------------
dMaybe      = DataType (getName tMaybe) (kMaybe)[nothingCfun,justCfun] 
kMaybe      = Kfun Star Star
tMaybe      = TCon  "Maybe"  kMaybe
nothingCfun = "Nothing" :>: (Forall [Star]
                             ([] :=> (TAp tMaybe (TGen 0))))
justCfun    = "Just" :>: (Forall [Star]
                          ([] :=> (TGen 0 --> TAp tMaybe (TGen 0))))
-------------------
dEither   = DataType (getName tEither) (kEither) [leftCfun,rightCfun]
kEither   = Kfun Star (Kfun Star Star)
tEither   = TCon  "Either" kEither
leftCfun  = "Left" :>: (Forall [Star, Star]
                        ([] :=> 
                         (TGen 0 --> TAp (TAp tEither (TGen 0)) (TGen 1))))
rightCfun = "Right" :>: (Forall [Star, Star]
                         ([] :=> 
                          (TGen 1 --> TAp (TAp tEither (TGen 0)) (TGen 1))))
-------------------
dOrdering = DataType (getName tOrdering) (kOrdering) [lTCfun,eQCfun,gTCfun]
kOrdering = Star
tOrdering = TCon  "Ordering" kOrdering
lTCfun    = "LT" :>: (Forall [] ([] :=> tOrdering))
eQCfun    = "EQ" :>: (Forall [] ([] :=> tOrdering))
gTCfun    = "GT" :>: (Forall [] ([] :=> tOrdering))
-------------------
dIO       = DataType (getName tIO) (kIO) [iOCfun]
kIO       =  Kfun Star Star
tIO       = TCon "IO" kIO
iOCfun    = "IO" :>: (Forall [Star]
                      ([] :=> 
                       (((tIOError --> TAp tIOResult (TGen 0)) -->
                         (TGen 0 --> TAp tIOResult (TGen 0)) -->
                         TAp tIOResult (TGen 0)) -->
                          TAp tIO (TGen 0)))) 
-- The Eq class -------------------------------------------------------------
tcEq = TypeClass [] cEq asig [eqMfun,neqMfun]

cEq = "Eq"

eqMfun  = "==" :>: (Forall [Star]
                    ([isIn1 cEq (TGen 0)] :=> 
                     (TGen 0 --> TGen 0 --> tBool)))
neqMfun = "/=" :>: (Forall [Star]
                    ([isIn1 cEq (TGen 0)] :=> 
                     (TGen 0 --> TGen 0 --> tBool)))

instsEq
 = [mkInst [] ([] :=> isIn1 cEq tUnit),
    mkInst [] ([] :=> isIn1 cEq tChar),
    mkInst [Star]
     ([isIn1 cEq (TGen 0)] :=> 
      isIn1 cEq (TAp tList (TGen 0))),
    mkInst [] ([] :=> isIn1 cEq tInt),
    mkInst [] ([] :=> isIn1 cEq tInteger),
    mkInst [] ([] :=> isIn1 cEq tFloat),
    mkInst [] ([] :=> isIn1 cEq tDouble),
    mkInst [] ([] :=> isIn1 cEq tBool),
    mkInst [Star]
     ([isIn1 cEq (TGen 0)] :=> 
      isIn1 cEq (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1)] :=> 
      isIn1 cEq (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst [] ([] :=> isIn1 cEq tOrdering),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cEq (TAp tRatio (TGen 0))),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2),
       isIn1 cEq (TGen 3),
       isIn1 cEq (TGen 4)] :=> 
      isIn1 cEq (foldl TAp tTuple5 (map TGen [0..4]))),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2),
       isIn1 cEq (TGen 3)] :=> 
      isIn1 cEq (foldl TAp tTuple4 (map TGen [0..3]))),
    mkInst [Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2)] :=> 
      isIn1 cEq (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2))),
    mkInst [Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1)] :=> 
      isIn1 cEq (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))]

-- The Ord class ------------------------------------------------------------
tcOrd = TypeClass [IsIn "Eq" [atype]] cOrd asig [compareMfun
                                                ,ltMfun,leMfun,geMfun,
                                                 gtMfun,maxMfun
                                                ,minMfun]  

cOrd = "Ord"

compareMfun
 = "compare" :>: (Forall [Star]
                   ([isIn1 cOrd (TGen 0)] :=> 
                    (TGen 0 --> TGen 0 --> tOrdering)))
ltMfun
 = "<" :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> tBool)))
leMfun
 = "<=" :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=> 
               (TGen 0 --> TGen 0 --> tBool)))
geMfun
 = ">=" :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=> 
               (TGen 0 --> TGen 0 --> tBool)))
gtMfun
 = ">" :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> tBool)))
maxMfun
 = "max" :>: (Forall [Star]
               ([isIn1 cOrd (TGen 0)] :=> 
                (TGen 0 --> TGen 0 --> TGen 0)))
minMfun
 = "min" :>: (Forall [Star]
               ([isIn1 cOrd (TGen 0)] :=> 
                (TGen 0 --> TGen 0 --> TGen 0)))

instsOrd
 = [mkInst [] ([] :=> isIn1 cOrd tUnit),
    mkInst [] ([] :=> isIn1 cOrd tChar),
    mkInst [Star]
     ([isIn1 cOrd (TGen 0)] :=> 
      isIn1 cOrd (TAp tList (TGen 0))),
    mkInst [] ([] :=> isIn1 cOrd tInt),
    mkInst [] ([] :=> isIn1 cOrd tInteger),
    mkInst [] ([] :=> isIn1 cOrd tFloat),
    mkInst [] ([] :=> isIn1 cOrd tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cOrd (TAp tRatio (TGen 0))),
    mkInst [] ([] :=> isIn1 cOrd tBool),
    mkInst [Star]
     ([isIn1 cOrd (TGen 0)] :=> 
      isIn1 cOrd (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1)] :=> 
      isIn1 cOrd (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst [] ([] :=> isIn1 cOrd tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2),
       isIn1 cOrd (TGen 3),
       isIn1 cOrd (TGen 4)] :=> 
      isIn1 cOrd (foldl TAp tTuple5 (map TGen [0..4]))),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2),
       isIn1 cOrd (TGen 3)] :=> 
      isIn1 cOrd (foldl TAp tTuple4 (map TGen [0..3]))),
    mkInst [Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2)] :=> 
      isIn1 cOrd (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2))),
    mkInst [Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1)] :=> 
      isIn1 cOrd (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))]

-- The Bounded class --------------------------------------------------------
tcBounded = TypeClass [] cBounded asig [minBoundMfun,maxBoundMfun]  
cBounded = "Bounded"

minBoundMfun
 = "minBound" :>: (Forall [Star]
                    ([isIn1 cBounded (TGen 0)] :=> 
                     (TGen 0)))
maxBoundMfun
 = "maxBound" :>: (Forall [Star]
                    ([isIn1 cBounded (TGen 0)] :=> 
                     (TGen 0)))

instsBounded
 = [mkInst [] ([] :=> isIn1 cBounded tUnit),
    mkInst [] ([] :=> isIn1 cBounded tChar),
    mkInst [] ([] :=> isIn1 cBounded tInt),
    mkInst [] ([] :=> isIn1 cBounded tBool),
    mkInst [] ([] :=> isIn1 cBounded tOrdering)]

-- The Num class ------------------------------------------------------------
tcNum = TypeClass [IsIn "Eq" [atype],
                   IsIn "Show" [atype]] cNum asig 
        [plusMfun,minusMfun
        ,timesMfun,negateMfun
        ,absMfun,signumMfun
        ,fromIntegerMfun,fromIntMfun]   

cNum = "Num"

plusMfun
 = "+" :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> TGen 0)))
minusMfun
 = "-" :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> TGen 0)))
timesMfun
 = "*" :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> TGen 0)))
negateMfun
 = "negate" :>: (Forall [Star]
                  ([isIn1 cNum (TGen 0)] :=> 
                   (TGen 0 --> TGen 0)))
absMfun
 = "abs" :>: (Forall [Star]
               ([isIn1 cNum (TGen 0)] :=> 
                (TGen 0 --> TGen 0)))
signumMfun
 = "signum" :>: (Forall [Star]
                  ([isIn1 cNum (TGen 0)] :=> 
                   (TGen 0 --> TGen 0)))
fromIntegerMfun
 = "fromInteger" :>: (Forall [Star]
                       ([isIn1 cNum (TGen 0)] :=> 
                        (tInteger --> TGen 0)))
fromIntMfun
 = "fromInt" :>: (Forall [Star]
                   ([isIn1 cNum (TGen 0)] :=> 
                    (tInt --> TGen 0)))

instsNum
 = [mkInst [] ([] :=> isIn1 cNum tInt),
    mkInst [] ([] :=> isIn1 cNum tInteger),
    mkInst [] ([] :=> isIn1 cNum tFloat),
    mkInst [] ([] :=> isIn1 cNum tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cNum (TAp tRatio (TGen 0)))]

-- The Real class -----------------------------------------------------------
tcReal = TypeClass [IsIn "Num" [atype], IsIn "Ord" [atype]]
         cReal asig [toRationalMfun]  
cReal = "Real"

toRationalMfun
 = "toRational" :>: (Forall [Star]
                      ([isIn1 cReal (TGen 0)] :=> 
                       (TGen 0 --> tRational)))

instsReal
 = [mkInst [] ([] :=> isIn1 cReal tInt),
    mkInst [] ([] :=> isIn1 cReal tInteger),
    mkInst [] ([] :=> isIn1 cReal tFloat),
    mkInst [] ([] :=> isIn1 cReal tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cReal (TAp tRatio (TGen 0)))]

-- The Integral class -------------------------------------------------------
tcIntegral = TypeClass [IsIn "Real" [atype],IsIn "Enum" [atype]]
             cIntegral asig [quotMfun,remMfun,divMfun,modMfun
                             ,quotRemMfun,divModMfun,evenMfun
                             ,oddMfun,toIntegerMfun,toIntMfun]  
cIntegral = "Integral"

quotMfun
 = "quot" :>: (Forall [Star]
                ([isIn1 cIntegral (TGen 0)] :=> 
                 (TGen 0 --> TGen 0 --> TGen 0)))
remMfun
 = "rem" :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 --> TGen 0 --> TGen 0)))
divMfun
 = "div" :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 --> TGen 0 --> TGen 0)))
modMfun
 = "mod" :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 --> TGen 0 --> TGen 0)))
quotRemMfun
 = "quotRem" :>: (Forall [Star]
                   ([isIn1 cIntegral (TGen 0)] :=> 
                    (TGen 0 --> TGen 0 --> TAp (TAp tTuple2 (TGen 0)) (TGen 0))))
divModMfun
 = "divMod" :>: (Forall [Star]
                  ([isIn1 cIntegral (TGen 0)] :=> 
                   (TGen 0 --> TGen 0 --> TAp (TAp tTuple2 (TGen 0)) (TGen 0))))
evenMfun
 = "even" :>: (Forall [Star]
                ([isIn1 cIntegral (TGen 0)] :=> 
                 (TGen 0 --> tBool)))
oddMfun
 = "odd" :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 --> tBool)))
toIntegerMfun
 = "toInteger" :>: (Forall [Star]
                     ([isIn1 cIntegral (TGen 0)] :=> 
                      (TGen 0 --> tInteger)))
toIntMfun
 = "toInt" :>: (Forall [Star]
                 ([isIn1 cIntegral (TGen 0)] :=> 
                  (TGen 0 --> tInt)))

instsIntegral
 = [mkInst [] ([] :=> isIn1 cIntegral tInt),
    mkInst [] ([] :=> isIn1 cIntegral tInteger)]

-- The Fractional class -----------------------------------------------------
tcFractional = TypeClass [IsIn "Num" [atype]] cFractional asig 
               [divideMfun,recipMfun,fromRationalMfun,fromDoubleMfun] 
                
               
cFractional = "Fractional"

divideMfun
 = "/" :>: (Forall [Star]
             ([isIn1 cFractional (TGen 0)] :=> 
              (TGen 0 --> TGen 0 --> TGen 0)))
recipMfun
 = "recip" :>: (Forall [Star]
                 ([isIn1 cFractional (TGen 0)] :=> 
                  (TGen 0 --> TGen 0)))
fromRationalMfun
 = "fromRational" :>: (Forall [Star]
                        ([isIn1 cFractional (TGen 0)] :=> 
                         (tRational --> TGen 0)))
fromDoubleMfun
 = "fromDouble" :>: (Forall [Star]
                      ([isIn1 cFractional (TGen 0)] :=> 
                       (tDouble --> TGen 0)))

instsFractional
 = [mkInst [] ([] :=> isIn1 cFractional tFloat),
    mkInst [] ([] :=> isIn1 cFractional tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cFractional (TAp tRatio (TGen 0)))]

-- The Floating class -------------------------------------------------------
tcFloating  = TypeClass [IsIn "Fractional" [atype]] cFloating asig 
              [piMfun,expMfun,logMfun,sqrtMfun,starstarMfun,logBaseMfun
              ,sinMfun,cosMfun,tanMfun,asinMfun,acosMfun,atanMfun,sinhMfun
              ,coshMfun,tanhMfun,asinhMfun,acoshMfun,atanhMfun] 
               
cFloating = "Floating"

piMfun
 = "pi" :>: (Forall [Star]
              ([isIn1 cFloating (TGen 0)] :=> (TGen 0)))
expMfun
 = "exp" :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
logMfun
 = "log" :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
sqrtMfun
 = "sqrt" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
starstarMfun
 = "**" :>: (Forall [Star]
              ([isIn1 cFloating (TGen 0)] :=> 
               (TGen 0 --> TGen 0 --> TGen 0)))
logBaseMfun
 = "logBase" :>: (Forall [Star]
                   ([isIn1 cFloating (TGen 0)] :=> 
                    (TGen 0 --> TGen 0 --> TGen 0)))
sinMfun
 = "sin" :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
cosMfun
 = "cos" :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
tanMfun
 = "tan" :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
asinMfun
 = "asin" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
acosMfun
 = "acos" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
atanMfun
 = "atan" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
sinhMfun
 = "sinh" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
coshMfun
 = "cosh" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
tanhMfun
 = "tanh" :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
asinhMfun
 = "asinh" :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
acoshMfun
 = "acosh" :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))
atanhMfun
 = "atanh" :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> (TGen 0 --> TGen 0)))

instsFloating
 = [mkInst [] ([] :=> isIn1 cFloating tFloat),
    mkInst [] ([] :=> isIn1 cFloating tDouble)]

-- The RealFrac class -------------------------------------------------------
tcRealFrac = TypeClass [IsIn "Real" [atype], IsIn "Fractional" [atype]]
             cRealFrac asig [properFractionMfun,truncateMfun,roundMfun
                            ,ceilingMfun,floorMfun]  
             
cRealFrac = "RealFrac"

properFractionMfun
 = "properFraction" :>: (Forall [Star, Star]
                          ([isIn1 cRealFrac (TGen 0),
                            isIn1 cIntegral (TGen 1)] :=> 
                           (TGen 0 --> TAp (TAp tTuple2 (TGen 1)) (TGen 0))))
truncateMfun
 = "truncate" :>: (Forall [Star, Star]
                    ([isIn1 cRealFrac (TGen 0),
                      isIn1 cIntegral (TGen 1)] :=> 
                     (TGen 0 --> TGen 1)))
roundMfun
 = "round" :>: (Forall [Star, Star]
                 ([isIn1 cRealFrac (TGen 0),
                   isIn1 cIntegral (TGen 1)] :=> 
                  (TGen 0 --> TGen 1)))
ceilingMfun
 = "ceiling" :>: (Forall [Star, Star]
                   ([isIn1 cRealFrac (TGen 0),
                     isIn1 cIntegral (TGen 1)] :=> 
                    (TGen 0 --> TGen 1)))
floorMfun
 = "floor" :>: (Forall [Star, Star]
                 ([isIn1 cRealFrac (TGen 0),
                   isIn1 cIntegral (TGen 1)] :=> 
                  (TGen 0 --> TGen 1)))

instsRealFrac
 = [mkInst [] ([] :=> isIn1 cRealFrac tFloat),
    mkInst [] ([] :=> isIn1 cRealFrac tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> isIn1 cRealFrac (TAp tRatio (TGen 0)))]

-- The RealFloat class ------------------------------------------------------
tcRealFloat = TypeClass [IsIn "RealFrac" [atype],IsIn "Floating" [atype]]
               cRealFloat asig [floatRadixMfun,floatDigitsMfun,floatRangeMfun
                               ,decodeFloatMfun,encodeFloatMfun,exponentMfun
                               ,significandMfun,scaleFloatMfun,isNaNMfun
                               ,isInfiniteMfun,isDenormalizedMfun
                               ,isNegativeZeroMfun
                               ,isIEEEMfun,atan2Mfun]  
cRealFloat = "RealFloat"

floatRadixMfun
 = "floatRadix" :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 --> tInteger)))
floatDigitsMfun
 = "floatDigits" :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 --> tInt)))
floatRangeMfun
 = "floatRange" :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 --> TAp (TAp tTuple2 tInt) tInt)))
decodeFloatMfun
 = "decodeFloat" :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 --> TAp (TAp tTuple2 tInteger) tInt)))
encodeFloatMfun
 = "encodeFloat" :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (tInteger --> tInt --> TGen 0)))
exponentMfun
 = "exponent" :>: (Forall [Star]
                    ([isIn1 cRealFloat (TGen 0)] :=> 
                     (TGen 0 --> tInt)))
significandMfun
 = "significand" :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 --> TGen 0)))
scaleFloatMfun
 = "scaleFloat" :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (tInt --> TGen 0 --> TGen 0)))
isNaNMfun
 = "isNaN" :>: (Forall [Star]
                 ([isIn1 cRealFloat (TGen 0)] :=> 
                  (TGen 0 --> tBool)))
isInfiniteMfun
 = "isInfinite" :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 --> tBool)))
isDenormalizedMfun
 = "isDenormalized" :>: (Forall [Star]
                          ([isIn1 cRealFloat (TGen 0)] :=> 
                           (TGen 0 --> tBool)))
isNegativeZeroMfun
 = "isNegativeZero" :>: (Forall [Star]
                          ([isIn1 cRealFloat (TGen 0)] :=> 
                           (TGen 0 --> tBool)))
isIEEEMfun
 = "isIEEE" :>: (Forall [Star]
                  ([isIn1 cRealFloat (TGen 0)] :=> 
                   (TGen 0 --> tBool)))
atan2Mfun
 = "atan2" :>: (Forall [Star]
                 ([isIn1 cRealFloat (TGen 0)] :=> 
                  (TGen 0 --> TGen 0 --> TGen 0)))

instsRealFloat
 = [mkInst [] ([] :=> isIn1 cRealFloat tFloat),
    mkInst [] ([] :=> isIn1 cRealFloat tDouble)]

-- The Enum class -----------------------------------------------------------
tcEnum = TypeClass [] cEnum asig [succMfun,predMfun,toEnumMfun,fromEnumMfun
                                 ,enumFromMfun,enumFromThenMfun
                                 ,enumFromToMfun,enumFromThenToMfun]  
cEnum = "Enum"

succMfun
 = "succ" :>: (Forall [Star]
                ([isIn1 cEnum (TGen 0)] :=> (TGen 0 --> TGen 0)))
predMfun
 = "pred" :>: (Forall [Star]
                ([isIn1 cEnum (TGen 0)] :=> (TGen 0 --> TGen 0)))
toEnumMfun
 = "toEnum" :>: (Forall [Star]
                  ([isIn1 cEnum (TGen 0)] :=> (tInt --> TGen 0)))
fromEnumMfun
 = "fromEnum" :>: (Forall [Star]
                    ([isIn1 cEnum (TGen 0)] :=> (TGen 0 --> tInt)))
enumFromMfun
 = "enumFrom" :>: (Forall [Star]
                    ([isIn1 cEnum (TGen 0)] :=> 
                     (TGen 0 --> TAp tList (TGen 0))))
enumFromThenMfun
 = "enumFromThen" :>: (Forall [Star]
                        ([isIn1 cEnum (TGen 0)] :=> 
                         (TGen 0 --> TGen 0 --> TAp tList (TGen 0))))
enumFromToMfun
 = "enumFromTo" :>: (Forall [Star]
                      ([isIn1 cEnum (TGen 0)] :=> 
                       (TGen 0 --> TGen 0 --> TAp tList (TGen 0))))
enumFromThenToMfun
 = "enumFromThenTo" :>: (Forall [Star]
                          ([isIn1 cEnum (TGen 0)] :=> 
                           (TGen 0 --> TGen 0 --> TGen 0 --> TAp tList (TGen 0))))

instsEnum
 = [mkInst [] ([] :=> isIn1 cEnum tUnit),
    mkInst [] ([] :=> isIn1 cEnum tChar),
    mkInst [] ([] :=> isIn1 cEnum tInt),
    mkInst [] ([] :=> isIn1 cEnum tInteger),
    mkInst [] ([] :=> isIn1 cEnum tFloat),
    mkInst [] ([] :=> isIn1 cEnum tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cEnum (TAp tRatio (TGen 0))),
    mkInst [] ([] :=> isIn1 cEnum tBool),
    mkInst [] ([] :=> isIn1 cEnum tOrdering)]

-- The Read class -----------------------------------------------------------
tcRead = TypeClass [] cRead asig [readsPrecMfun,readListMfun]  
cRead = "Read"

readsPrecMfun
 = "readsPrec" :>: (Forall [Star]
                     ([isIn1 cRead (TGen 0)] :=> (tInt --> tReadS (TGen 0))))
readListMfun
 = "readList" :>: (Forall [Star]
                    ([isIn1 cRead (TGen 0)] :=> tReadS (TAp tList (TGen 0))))

instsRead
 = [mkInst [] ([] :=> isIn1 cRead tUnit),
    mkInst [] ([] :=> isIn1 cRead tChar),
    mkInst [Star]
     ([isIn1 cRead (TGen 0)] :=> isIn1 cRead (TAp tList (TGen 0))),
    mkInst [] ([] :=> isIn1 cRead tInt),
    mkInst [] ([] :=> isIn1 cRead tInteger),
    mkInst [] ([] :=> isIn1 cRead tFloat),
    mkInst [] ([] :=> isIn1 cRead tDouble),
    mkInst [Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cIntegral (TGen 0)] :=> isIn1 cRead (TAp tRatio (TGen 0))),
    mkInst [] ([] :=> isIn1 cRead tBool),
    mkInst [Star]
     ([isIn1 cRead (TGen 0)] :=> isIn1 cRead (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1)] :=> 
      isIn1 cRead (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst [] ([] :=> isIn1 cRead tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2),
       isIn1 cRead (TGen 3),
       isIn1 cRead (TGen 4)] :=> 
      isIn1 cRead (foldl TAp tTuple5 (map TGen [0..4]))),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2),
       isIn1 cRead (TGen 3)] :=> 
      isIn1 cRead (foldl TAp tTuple4 (map TGen [0..3]))),
    mkInst [Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2)] :=> 
      isIn1 cRead (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2))),
    mkInst [Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1)] :=> 
      isIn1 cRead (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))]

-- The Show class -----------------------------------------------------------
tcShow = TypeClass [] cShow asig [showMfun,showsPrecMfun,showListMfun
                                 ,showListMfun]  

cShow = "Show"

showMfun
 = "show" :>: (Forall [Star]
                ([isIn1 cShow (TGen 0)] :=> 
                 (TGen 0 --> tString)))
showsPrecMfun
 = "showsPrec" :>: (Forall [Star]
                     ([isIn1 cShow (TGen 0)] :=> 
                      (tInt --> TGen 0 --> tShowS)))
showListMfun
 = "showList" :>: (Forall [Star]
                    ([isIn1 cShow (TGen 0)] :=> 
                     (TAp tList (TGen 0) --> tShowS)))

instsShow
 = [mkInst [] ([] :=> isIn1 cShow tUnit),
    mkInst [] ([] :=> isIn1 cShow tChar),
    mkInst [Star]
     ([isIn1 cShow (TGen 0)] :=> 
      isIn1 cShow (TAp tList (TGen 0))),
    mkInst [] ([] :=> isIn1 cShow tInt),
    mkInst [] ([] :=> isIn1 cShow tInteger),
    mkInst [] ([] :=> isIn1 cShow tFloat),
    mkInst [] ([] :=> isIn1 cShow tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cShow (TAp tRatio (TGen 0))),
    mkInst [Star] ([] :=> isIn1 cShow (TAp tIO (TGen 0))),
    mkInst [] ([] :=> isIn1 cShow tIOError),
    mkInst [] ([] :=> isIn1 cShow tBool),
    mkInst [Star]
     ([isIn1 cShow (TGen 0)] :=> 
      isIn1 cShow (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1)] :=> 
      isIn1 cShow (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst [] ([] :=> isIn1 cShow tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2),
       isIn1 cShow (TGen 3),
       isIn1 cShow (TGen 4)] :=> 
      isIn1 cShow (foldl TAp tTuple5 (map TGen [0..4]))),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2),
       isIn1 cShow (TGen 3)] :=> 
      isIn1 cShow (foldl TAp tTuple4 (map TGen [0..3]))),
    mkInst [Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2)] :=> 
      isIn1 cShow (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2))),
    mkInst [Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1)] :=> 
      isIn1 cShow (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))]

-- The Ix class -------------------------------------------------------------
tcIx = TypeClass [IsIn cOrd [atype]] cIx asig [rangeMfun,indexMfun,inRangeMfun
                                              ,rangeSizeMfun]  
cIx = "Ix"

rangeMfun
 = "range" :>: (Forall [Star]
                ([isIn1 cIx (TGen 0)] :=> 
                 (TAp (TAp tTuple2 (TGen 0)) (TGen 0) -->
                  TAp tList (TGen 0))))
indexMfun
 = "index" :>: (Forall [Star]
                ([isIn1 cIx (TGen 0)] :=> 
                 (TAp (TAp tTuple2 (TGen 0)) (TGen 0) -->
                  TGen 0 --> tInt)))
inRangeMfun
 = "inRange" :>: (Forall [Star]
                  ([isIn1 cIx (TGen 0)] :=> 
                   (TAp (TAp tTuple2 (TGen 0)) (TGen 0) -->
                    TGen 0 --> tBool)))
rangeSizeMfun
 = "rangeSize" :>: (Forall [Star]
                    ([isIn1 cIx (TGen 0)] :=> 
                     (TAp (TAp tTuple2 (TGen 0)) (TGen 0) --> tInt)))

instsIx
 = [mkInst [] ([] :=> isIn1 cIx tUnit),
    mkInst [] ([] :=> isIn1 cIx tChar),
    mkInst [] ([] :=> isIn1 cIx tInt),
    mkInst [] ([] :=> isIn1 cIx tInteger),
    mkInst [] ([] :=> isIn1 cIx tBool),
    mkInst [] ([] :=> isIn1 cIx tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2),
       isIn1 cIx (TGen 3),
       isIn1 cIx (TGen 4)] :=> 
      isIn1 cIx (foldl TAp tTuple5 (map TGen [0..4]))),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2),
       isIn1 cIx (TGen 3)] :=> 
      isIn1 cIx (foldl TAp tTuple4 (map TGen [0..3]))),
    mkInst [Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2)] :=> 
      isIn1 cIx (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2))),
    mkInst [Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1)] :=> 
      isIn1 cIx (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))]

-- The Functor class --------------------------------------------------------
tcFunctor = TypeClass [] cFunctor msig [fmapMfun]  
cFunctor = "Functor"

fmapMfun
 = "fmap" :>: (Forall [Kfun Star Star, Star, Star]
                ([isIn1 cFunctor (TGen 0)] :=> 
                 ((TGen 1 --> TGen 2) -->
                  TAp (TGen 0) (TGen 1) -->
                  TAp (TGen 0) (TGen 2))))

instsFunctor
 = [mkInst [] ([] :=> isIn1 cFunctor tMaybe),
    mkInst [] ([] :=> isIn1 cFunctor tList),
    mkInst [] ([] :=> isIn1 cFunctor tIO)]

-- The Monad class ----------------------------------------------------------
tcMonad = TypeClass [] cMonad msig [returnMfun,mbindMfun
                                   ,mthenMfun,failMfun]  
cMonad = "Monad"

returnMfun
 = "return" :>: (Forall [Kfun Star Star, Star]
                  ([isIn1 cMonad (TGen 0)] :=> 
                   (TGen 1 --> TAp (TGen 0) (TGen 1))))
mbindMfun
 = ">>=" :>: (Forall [Kfun Star Star, Star, Star]
               ([isIn1 cMonad (TGen 0)] :=> 
                (TAp (TGen 0) (TGen 1) --> (TGen 1 --> TAp (TGen 0) (TGen 2)) --> TAp (TGen 0) (TGen 2))))
mthenMfun
 = ">>" :>: (Forall [Kfun Star Star, Star, Star]
              ([isIn1 cMonad (TGen 0)] :=> 
               (TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2) --> TAp (TGen 0) (TGen 2))))
failMfun
 = "fail" :>: (Forall [Kfun Star Star, Star]
                ([isIn1 cMonad (TGen 0)] :=> 
                 (tString --> TAp (TGen 0) (TGen 1))))

instsMonad
 = [mkInst [] ([] :=> isIn1 cMonad tMaybe),
    mkInst [] ([] :=> isIn1 cMonad tList),
    mkInst [] ([] :=> isIn1 cMonad tIO)]
   
----------------------------------------------------------------------------- 
tReadS a
 = TAp tList tChar --> TAp tList (TAp (TAp tTuple2 a) (TAp tList tChar))

tShowS = TAp tList tChar --> TAp tList tChar



kRational = Star
tRatio    = TCon  "Rational"  Star
consratCfun = ":%" :>: (Forall [Star]
              ([isIn1 cIntegral (TGen 0)] :=> 
               (TGen 0 --> TGen 0 --> TAp tRatio (TGen 0))))

tRational = TAp tRatio tInteger

tIOError  = TCon "IOError" Star
tFilePath = TAp tList tChar
tIOResult = TCon  "IOResult" Star 
-----------------------------------------
importsPrelude
 =  ["error" :>: 
       Forall [Star]
         ([] :=>
            (tString --> TGen 0)),
     "flip" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 2) --> TGen 1 --> TGen 0 --> TGen 2)),
     "subtract" :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TGen 0)),
     "gcd" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TGen 0)),
     "lcm" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TGen 0)),
     "otherwise" :>:
       Forall []
	 ([] :=>
	    tBool),
     "^" :>:
       Forall [Star, Star]
	 ([isIn1 cNum (TGen 0), isIn1 cIntegral (TGen 1)] :=>
	    (TGen 0 --> TGen 1 --> TGen 0)),
     "^^" :>:
       Forall [Star, Star]
	 ([isIn1 cFractional (TGen 0), isIn1 cIntegral (TGen 1)] :=>
	    (TGen 0 --> TGen 1 --> TGen 0)),
     "." :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1) --> (TGen 2 --> TGen 0) --> TGen 2 --> TGen 1)),
     "fromIntegral" :>:
       Forall [Star, Star]
	 ([isIn1 cIntegral (TGen 0), isIn1 cNum (TGen 1)] :=>
	    (TGen 0 --> TGen 1)),
     "realToFrac" :>:
       Forall [Star, Star]
	 ([isIn1 cReal (TGen 0), isIn1 cFractional (TGen 1)] :=>
	    (TGen 0 --> TGen 1)),
     "sequence" :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp tList (TAp (TGen 0) (TGen 1)) --> TAp (TGen 0) (TAp tList (TGen 1)))),
     "foldr" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 1) --> TGen 1 --> TAp tList (TGen 0) --> TGen 1)),
     "sequence_" :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp tList (TAp (TGen 0) (TGen 1)) --> TAp (TGen 0) tUnit)),
     "map" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1) --> TAp tList (TGen 0) --> TAp tList (TGen 1))),
     "mapM" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TAp (TGen 0) (TGen 2)) --> TAp tList (TGen 1) --> TAp (TGen 0) (TAp tList (TGen 2)))),
     "mapM_" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TAp (TGen 0) (TGen 2)) --> TAp tList (TGen 1) --> TAp (TGen 0) tUnit)),
     "=<<" :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 --> TAp (TGen 0) (TGen 2)) --> TAp (TGen 0) (TGen 1) --> TAp (TGen 0) (TGen 2))),
     "&&" :>:
       Forall []
	 ([] :=>
	    (tBool --> tBool --> tBool)),
     "||" :>:
       Forall []
	 ([] :=>
	    (tBool --> tBool --> tBool)),
     "not" :>:
       Forall []
	 ([] :=>
	    (tBool --> tBool)),
     "isAscii" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isControl" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isPrint" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isSpace" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isUpper" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isLower" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isAlpha" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isDigit" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isAlphaNum" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "digitToInt" :>:
       Forall []
	 ([] :=>
	    (tChar --> tInt)),
     "intToDigit" :>:
       Forall []
	 ([] :=>
	    (tInt --> tChar)),
     "toUpper" :>:
       Forall []
	 ([] :=>
	    (tChar --> tChar)),
     "toLower" :>:
       Forall []
	 ([] :=>
	    (tChar --> tChar)),
     "ord" :>:
       Forall []
	 ([] :=>
	    (tChar --> tInt)),
     "chr" :>:
       Forall []
	 ([] :=>
	    (tInt --> tChar)),
     "maybe" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TGen 0 --> (TGen 1 --> TGen 0) --> TAp tMaybe (TGen 1) --> TGen 0)),
     "either" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1) --> (TGen 2 --> TGen 1) --> TAp (TAp tEither (TGen 0)) (TGen 2) --> TGen 1)),
     "absReal" :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0), isIn1 cOrd (TGen 0)] :=>
	    (TGen 0 --> TGen 0)),
     "signumReal" :>:
       Forall [Star, Star]
	 ([isIn1 cNum (TGen 0), isIn1 cNum (TGen 1),
	   isIn1 cOrd (TGen 0)] :=>
	    (TGen 0 --> TGen 1)),
     "numericEnumFrom" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 --> TAp tList (TGen 0))),
     "iterate" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> TGen 0) --> TGen 0 --> TAp tList (TGen 0))),
     "numericEnumFromThen" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TAp tList (TGen 0))),
     "takeWhile" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "numericEnumFromTo" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TAp tList (TGen 0))),
     "numericEnumFromThenTo" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TGen 0 --> TAp tList (TGen 0))),
     "reduce" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TAp tRatio (TGen 0))),
     "%" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TAp tRatio (TGen 0))),
     "realFloatToRational" :>:
       Forall [Star]
	 ([isIn1 cRealFloat (TGen 0)] :=>
	    (TGen 0 --> TAp tRatio tInteger)),
     "floatToRational" :>:
       Forall []
	 ([] :=>
	    (tFloat --> TAp tRatio tInteger)),
     "doubleToRational" :>:
       Forall []
	 ([] :=>
	    (tDouble --> TAp tRatio tInteger)),
     "const" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TGen 0 --> TGen 1 --> TGen 0)),
     "asTypeOf" :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 --> TGen 0 --> TGen 0)),
     "numerator" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tRatio (TGen 0) --> TGen 0)),
     "denominator" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tRatio (TGen 0) --> TGen 0)),
     "rationalToRealFloat" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tRatio tInteger --> TGen 0)),
     "rationalToFloat" :>:
       Forall []
	 ([] :=>
	    (TAp tRatio tInteger --> tFloat)),
     "rationalToDouble" :>:
       Forall []
	 ([] :=>
	    (TAp tRatio tInteger --> tDouble)),
     "floatProperFraction" :>:
       Forall [Star, Star, Star]
	 ([isIn1 cRealFloat (TGen 0), isIn1 cNum (TGen 1),
	   isIn1 cRealFloat (TGen 2)] :=>
	    (TGen 2 --> TAp (TAp tTuple2 (TGen 1)) (TGen 0))),
     "fst" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp (TAp tTuple2 (TGen 0)) (TGen 1) --> TGen 0)),
     "snd" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp (TAp tTuple2 (TGen 0)) (TGen 1) --> TGen 1)),
     "curry" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TAp (TAp tTuple2 (TGen 0)) (TGen 1) --> TGen 2) --> TGen 0 --> TGen 1 --> TGen 2)),
     "uncurry" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 2) --> TAp (TAp tTuple2 (TGen 0)) (TGen 1) --> TGen 2)),
     "id" :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 --> TGen 0)),
     "$" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1) --> TGen 0 --> TGen 1)),
     "until" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> (TGen 0 --> TGen 0) --> TGen 0 --> TGen 0)),
     "undefined" :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0)),
     "intToRatio" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (tInt --> TAp tRatio (TGen 0))),
     "doubleToRatio" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (tDouble --> TAp tRatio (TGen 0))),
     "approxRational" :>:
       Forall [Star]
	 ([isIn1 cRealFrac (TGen 0)] :=>
	    (TGen 0 --> TGen 0 --> TAp tRatio tInteger)),
     "head" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "last" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "tail" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "init" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "null" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> tBool)),
     "++" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "filter" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "concat" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TAp tList (TGen 0)) --> TAp tList (TGen 0))),
     "foldl'" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 0) --> TGen 0 --> TAp tList (TGen 1) --> TGen 0)),
     "length" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> tInt)),
     "!!" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> tInt --> TGen 0)),
     "foldl" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 0) --> TGen 0 --> TAp tList (TGen 1) --> TGen 0)),
     "foldl1" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> TGen 0 --> TGen 0) --> TAp tList (TGen 0) --> TGen 0)),
     "scanl" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 0) --> TGen 0 --> TAp tList (TGen 1) --> TAp tList (TGen 0))),
     "scanl1" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> TGen 0 --> TGen 0) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "foldr1" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> TGen 0 --> TGen 0) --> TAp tList (TGen 0) --> TGen 0)),
     "scanr" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 1) --> TGen 1 --> TAp tList (TGen 0) --> TAp tList (TGen 1))),
     "scanr1" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> TGen 0 --> TGen 0) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "repeat" :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 --> TAp tList (TGen 0))),
     "take" :>:
       Forall [Star]
	 ([] :=>
	    (tInt --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "replicate" :>:
       Forall [Star]
	 ([] :=>
	    (tInt --> TGen 0 --> TAp tList (TGen 0))),
     "cycle" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "drop" :>:
       Forall [Star]
	 ([] :=>
	    (tInt --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "splitAt" :>:
       Forall [Star]
	 ([] :=>
	    (tInt --> TAp tList (TGen 0) --> TAp (TAp tTuple2 (TAp tList (TGen 0))) (TAp tList (TGen 0)))),
     "dropWhile" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "span" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> TAp (TAp tTuple2 (TAp tList (TGen 0))) (TAp tList (TGen 0)))),
     "break" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> TAp (TAp tTuple2 (TAp tList (TGen 0))) (TAp tList (TGen 0)))),
     "lines" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp tList tChar))),
     "words" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp tList tChar))),
     "concatMap" :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 --> TAp tList (TGen 1)) --> TAp tList (TGen 0) --> TAp tList (TGen 1))),
     "unlines" :>:
       Forall []
	 ([] :=>
	    (TAp tList (TAp tList tChar) --> TAp tList tChar)),
     "unwords" :>:
       Forall []
	 ([] :=>
	    (TAp tList (TAp tList tChar) --> TAp tList tChar)),
     "reverse" :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0))),
     "and" :>:
       Forall []
	 ([] :=>
	    (TAp tList tBool --> tBool)),
     "or" :>:
       Forall []
	 ([] :=>
	    (TAp tList tBool --> tBool)),
     "any" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> tBool)),
     "all" :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 --> tBool) --> TAp tList (TGen 0) --> tBool)),
     "elem" :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 --> TAp tList (TGen 0) --> tBool)),
     "notElem" :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 --> TAp tList (TGen 0) --> tBool)),
     "lookup" :>:
       Forall [Star, Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TGen 1)) --> TAp tMaybe (TGen 1))),
     "sum" :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "product" :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "maximum" :>:
       Forall [Star]
	 ([isIn1 cOrd (TGen 0)] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "minimum" :>:
       Forall [Star]
	 ([isIn1 cOrd (TGen 0)] :=>
	    (TAp tList (TGen 0) --> TGen 0)),
     "zipWith" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 2) --> TAp tList (TGen 0) --> TAp tList (TGen 1) --> TAp tList (TGen 2))),
     "zip" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 1) --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TGen 1)))),
     "zipWith3" :>:
       Forall [Star, Star, Star, Star]
	 ([] :=>
	    ((TGen 0 --> TGen 1 --> TGen 2 --> TGen 3) --> TAp tList (TGen 0) --> TAp tList (TGen 1) --> TAp tList (TGen 2) --> TAp tList (TGen 3))),
     "zip3" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 1) --> TAp tList (TGen 2) --> TAp tList (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2)))),
     "unzip" :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp tList (TAp (TAp tTuple2 (TGen 0)) (TGen 1)) --> TAp (TAp tTuple2 (TAp tList (TGen 0))) (TAp tList (TGen 1)))),
     "unzip3" :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    (TAp tList (TAp (TAp (TAp tTuple3 (TGen 0)) (TGen 1)) (TGen 2)) --> TAp (TAp (TAp tTuple3 (TAp tList (TGen 0))) (TAp tList (TGen 1))) (TAp tList (TGen 2)))),
     "reads" :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "shows" :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TGen 0 --> TAp tList tChar --> TAp tList tChar)),
     "nonnull" :>:
       Forall []
	 ([] :=>
	    ((tChar --> tBool) --> TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TAp tList tChar)) (TAp tList tChar)))),
     "lexDigits" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TAp tList tChar)) (TAp tList tChar)))),
     "lexmatch" :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TAp tList (TGen 0) --> TAp tList (TGen 0) --> TAp (TAp tTuple2 (TAp tList (TGen 0))) (TAp tList (TGen 0)))),
     "asciiTab" :>:
       Forall []
	 ([] :=>
	    (TAp tList (TAp (TAp tTuple2 tChar) (TAp tList tChar)))),
     "lexLitChar" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TAp tList tChar)) (TAp tList tChar)))),
     "lex" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TAp tList tChar)) (TAp tList tChar)))),
     "read" :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar --> TGen 0)),
     "showChar" :>:
       Forall []
	 ([] :=>
	    (tChar --> TAp tList tChar --> TAp tList tChar)),
     "showString" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList tChar --> TAp tList tChar)),
     "showParen" :>:
       Forall []
	 ([] :=>
	    (tBool --> (TAp tList tChar --> TAp tList tChar) --> TAp tList tChar --> TAp tList tChar)),
     "showField" :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TAp tList tChar --> TGen 0 --> TAp tList tChar --> TAp tList tChar)),
     "readParen" :>:
       Forall [Star]
	 ([] :=>
	    (tBool --> (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar))) --> TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "readField" :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "isOctDigit" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "isHexDigit" :>:
       Forall []
	 ([] :=>
	    (tChar --> tBool)),
     "readInt" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> (tChar --> tBool) --> (tChar --> tInt) --> TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "readHex" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "readOct" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "readDec" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "readLitChar" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 tChar) (TAp tList tChar)))),
     "protectEsc" :>:
       Forall [Star]
	 ([] :=>
	    ((tChar --> tBool) --> (TAp tList tChar --> TGen 0) --> TAp tList tChar --> TGen 0)),
     "showLitChar" :>:
       Forall []
	 ([] :=>
	    (tChar --> TAp tList tChar --> TAp tList tChar)),
     "showInt" :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 --> TAp tList tChar --> TAp tList tChar)),
     "readSigned" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    ((TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar))) --> TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "showSigned" :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    ((TGen 0 --> TAp tList tChar --> TAp tList tChar) --> tInt --> TGen 0 --> TAp tList tChar --> TAp tList tChar)),
     "readFloat" :>:
       Forall [Star]
	 ([isIn1 cRealFloat (TGen 0)] :=>
	    (TAp tList tChar --> TAp tList (TAp (TAp tTuple2 (TGen 0)) (TAp tList tChar)))),
     "putStrLn" :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar --> TAp tIO tUnit)),
     "print" :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TGen 0 --> TAp tIO tUnit)),
     "getLine" :>:
       Forall []
	 ([] :=>
	    (TAp tIO (TAp tList tChar))),
     "readIO" :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar --> TAp tIO (TGen 0))),
     "readLn" :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tIO (TGen 0))),
     "interact" :>:
       Forall []
	 ([] :=>
	    ((TAp tList tChar --> TAp tList tChar) --> TAp tIO tUnit))]