-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.THIH.Typecheck.Load
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.THIH.Typecheck.Load where

import Language.Haskell.THIH.Syntax
import Language.Haskell.THIH.SurfaceTypes 
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.THIH.Typecheck.Internals  
import Language.Haskell.THIH.Typecheck.Types
import Language.Haskell.THIH.Typecheck.Typecheck
import Language.Haskell.THIH.Typecheck.KindInference (mkModule)
import Language.Haskell.THIH.Typecheck.Library.Prelude

import Language.Haskell.Exts.Desugaring
import Language.Haskell.Exts.ToTHIH
import Language.Haskell.Exts.FromTHIH
import Language.Haskell.Exts (ParseResult(..),QName(..),parseType
                             ,prettyPrint,Pretty(..),Name(..),parseExp)
import qualified Language.Haskell.Exts as HSE

import Control.Applicative
import Data.Traversable

import Debug.Trace

-----------------------------------------------------
-- Start Here
-----------------------------------------------------
-- ex: tcStringWithPrelude3 "data X = X;f y = X"
tcStringWithPrelude3 :: String -> [ (String,String)]
tcStringWithPrelude3 inp = (\(x,y) -> (x,prettyPrint y))
                           <$> tcStringWithPrelude2 inp
                           
tcStringWithPrelude2 :: String -> [(String,HSE.Type)]
tcStringWithPrelude2 inp = cAssump <$>  tcStringWithPrelude inp

tcStringWithPrelude :: String -> [Assump]
tcStringWithPrelude inp = let
  ParseOk m = HSE.parseModule inp
  in tcHSEModuleWithPrelude m
     
tcHSEModuleWithPrelude ::  HSE.Module -> [Assump]
tcHSEModuleWithPrelude = tcHSEModule preludeEnv

tcHSEModule :: (ConEnv,ClassEnv,[Assump]) -> HSE.Module -> [Assump]
tcHSEModule envs m = let
  ((e2,e3), kp) = loadHSEModule envs   m
  in tiProgram e2 e3 kp  

testDesugaring :: String -> String
testDesugaring inp = let
  ParseOk m = HSE.parseModule inp
  Right dm = runUnique (desugar m) "_x" 
  in
   show dm
  
testConversion :: String -> String
testConversion inp = let
  ParseOk m = HSE.parseModule inp
  Right dm = runUnique (desugar m) "_x" 
  sm  = cSModule dm
  in
   show sm
-----------------------------------------------------
-- Loading
-----------------------------------------------------
loadHSEModule ::  (ConEnv,ClassEnv,[Assump]) -> 
                  HSE.Module -> 
                  ((ClassEnv,[Assump])
                  , Kinded Program)  
loadHSEModule envs m = let 
  Right dm = runUnique (desugar m) "_x" 
  sm  = cSModule dm
  in loadSModule envs sm

loadSModule :: (ConEnv,ClassEnv,[Assump]) -> 
               SModule -> 
               ((ClassEnv,[Assump]) , Kinded Program)
loadSModule es@(e1,e2,e3) sm = let
  e1' = e1 ++ [(n, foldl1 Kfun ( [k | Tyvar _ k <- tyv ] ++ [Constraint]))
              |(n,(tyv,_,_)) <- cls e2]
  m  =  mkModule e1  sm
  in loadModule es m  
     
loadModule ::(ConEnv,ClassEnv,[Assump]) -> 
             Module -> 
             ((ClassEnv,[Assump]),Kinded Program)
loadModule es m@(Module _ _ _ _ prog) =
  (loadTopModule es m , prog)
 
loadTopModule ::(ConEnv,ClassEnv,[Assump]) -> 
             Module -> 
             (ClassEnv,[Assump])
loadTopModule (e1,e2,e3) (Module syns dats clss ins prog) = let             
  et | null clss  = Just    
     | True      =  
       foldl1 (<:>)  [ addClass i vars sups
                     | TypeClass sups i vars _  <- clss] 
  inss =  [p | Instance p  <- ins]
  et'| null inss = et
     | True =  (et <:> instances inss  )  
  Just e2'  = et' e2 
   
  e3' = [m | TypeClass _ _ _ as  <- clss
           , m <- as] 
        ++
        [cn | DataType _ _ as <- dats
            , cn <- as] 
        ++ e3        
  in (e2', e3')

loadModuleHeader :: (ConEnv,ClassEnv,[Assump]) -> 
                  ModuleHeader -> 
                  (ConEnv,ClassEnv,[Assump])
loadModuleHeader (cn,ce,ass)  (ModuleH dts tcs is as) = 
  let cn' = [(n,k) | DataType  n k _ <- dts ] ++ 
            [ (n, foldl1 Kfun ([ k | Tyvar _ k <- tys ]++[Constraint]) ) 
            | TypeClass _ n tys _ <- tcs]
            ++   cn
     --check duplications? order
      cet | null tcs = Just 
          | True     = foldl1 (<:>) 
                       [addClass n v s| TypeClass s n v _ <- tcs]  
      inss =[ p | Instance p <-is]
      cet' | null inss = Just
           | True = (cet            
                  <:> 
                  instances inss)
      Just ce' =  cet' ce  
  in
   (cn',ce'
   , (concat ([as   |DataType _ _ as <- dts]))
     ++ (concat ([as| TypeClass _ _ _ as  <- tcs]))
     ++ as
     ++ ass --check duplications? order?
   ) 
 
preludeEnv :: (ConEnv,ClassEnv,[Assump])
preludeEnv = loadModuleHeader ([],initialEnv,[]) modulePrelude
