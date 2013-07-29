-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Exts.Desugaring
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}


module Language.Haskell.Exts.Desugaring where

import qualified Prelude
import Prelude (($),(.),Either(..),Maybe(..),Bool(..),(++)
   ,concat,filter,foldr,foldl,length,any,not,succ,String(..),Int
   ,fst,(&&),flip,Show(..))
import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc(noLoc)

import Control.Monad(mapM,sequence,Monad(..))
import Control.Monad.Trans(lift)
import Control.Monad.State(put,get,evalState,State(..))
import Control.Monad.Reader(ask,ReaderT(..))
import Control.Monad.Error(throwError,ErrorT(..))

import Debug.Trace

import Data.List(partition,(\\),lookup,foldl1,notElem,union)

import Control.Applicative ((<$>),(<*>))
--------------------------------------------
type Unique a = ErrorT String (ReaderT String (State ([Name],Int))) a

newVar :: Unique String
newVar = do
  seed <- ask
  (ns,r) <- lift get
  lift $ put $ (ns ,succ r)
  return $ seed ++ (Prelude.show r)

runUnique :: Unique a -> String -> Either String a
runUnique c seed =  evalState ((runReaderT $ runErrorT c) seed) ([], 0)

initUnique :: Unique ()
initUnique = lift $ put ([],0)

error :: String -> Unique a
error = throwError

push :: [Name] -> Unique ()
push ns = do
  (_,r) <- lift get
  lift $ put $ (ns ,r)

peak :: Unique [Name]
peak = fst <$> lift get

pop :: Unique [Name]
pop = do
      r <- peak
      push []
      return r

---------------------------------------------
class Desugar a where
  desugar :: a -> Unique a


-- Applicative style of applying desugaring

infixl 4 **,$$
(**) :: Desugar a => Unique (a -> b) -> a -> Unique b
x ** y = x <*> desugar y

($$) :: Desugar a => (a -> b) -> a -> Unique b
x $$ y = return x <*> desugar y

--------------------------------------------
instance Desugar QName where
  desugar = return

instance Desugar Name where
  desugar = return

instance Desugar SrcLoc where
  desugar = return

instance Desugar Literal where
  desugar = return

instance Desugar a => Desugar [a] where
  desugar = mapM desugar

instance Desugar Kind where
  desugar (KindParen k) =
    desugar k
  desugar KindBang =
    return KindBang
  desugar (KindFn k1 k2) =
    KindFn $$ k1 ** k2
  desugar (KindVar n) =
    KindVar $$ n

instance Desugar Asst where
  desugar (ClassA qName ts) =
    ClassA $$ qName ** ts
  -- common sense
  desugar (InfixA t1 qName t2) =
    desugar $ ClassA qName [t1,t2]
  desugar (IParam iPName t) =
    error "Not supported!"
  desugar (EqualP t1 t2)  =
    EqualP $$ t1 ** t2

instance Desugar TyVarBind where
   desugar (KindedVar n k) =
     KindedVar $$ n ** k
   desugar (UnkindedVar n) =
     UnkindedVar $$ n

instance Desugar Type where

  desugar (TyForall (Just _) _ _)  =
    error "ExplicitForAlls is not supported!"

  desugar (TyForall Nothing ctx ty) =
    do
     t  <- desugarT ty
     c  <- desugar ctx
     tys <- peak
     return
       $ TyForall
       (Just $ UnkindedVar <$> (tyvars t \\ tys))
       c t
  desugar ty  = do
    t <- desugarT ty
    tys <- peak

    return
      $ TyForall (Just $ UnkindedVar <$> (tyvars t \\ tys)) [] t

desugarT (TyApp t1 t2) =
    TyApp <$> desugarT t1 <*> desugarT t2
desugarT (TyCon qName) =
    TyCon <$> desugar qName
desugarT (TyVar  n) =
    TyVar <$> desugar  n
desugarT (TyKind t k) =
    TyKind <$> desugarT t <*> desugar k
desugarT (TyFun t1 t2) =
    desugarT $ TyInfix t1 (Special FunCon) t2
desugarT (TyTuple b ts) =
    desugarT $ foldl TyApp (TyCon $ Special $ TupleCon b $ length ts) ts
desugarT (TyList  t) =
    desugarT $ TyApp (TyCon $ Special ListCon) t
desugarT (TyInfix t1 qName t2) =
    desugarT $ TyApp (TyApp (TyCon qName) t1) t2
desugarT ( TyParen t ) =
    desugarT t



instance Desugar Pat where
  -- no desugaring
  desugar (PVar name) =
    PVar $$ name

  -- no desugaring
  desugar (PLit literal) =
    PLit $$ literal

  -- no desugaring
  desugar (PatTypeSig x pat ttype) =
    PatTypeSig $$ x ** pat ** ttype

  -- no desugaring
  desugar (PApp qName pats) =
    PApp $$ qName ** pats

  -- no desugaring
  desugar (PAsPat name pat) =
    PAsPat $$ name ** pat

  -- no desugaring
  desugar (PNPlusK name integer) =
    return $ PNPlusK name  integer

  -- no desugaring
  desugar (PViewPat eexp pat) =
    PViewPat $$ eexp ** pat

  -- no desugaring
  -- should be removed from HSE
  -- and replaced with literals
  desugar (PNeg pl@(PLit (Int x)))  =
    desugar (PLit (Int (-x)))
  desugar (PNeg pl@(PLit (Frac y)))  =
    desugar (PLit (Frac (-y)))
  desugar (PNeg _other) =
    error "In Patterns, negation can only be applied to numeric literals!"

  -- no desugaring
  -- in typechecking it is ommited
  desugar (PIrrPat pat) =
    PIrrPat $$ pat

  -- no desugaring
  -- in typechecking it is ommited
  desugar (PBangPat pat) =
    PBangPat $$ pat

  -- no desugaring
  desugar p@PWildCard =
    return $ PWildCard
    -- in typechecking PVar$Ident "_"

  -- HSE
  desugar (PParen pat) =
    desugar pat

  -- HSE
  desugar (PInfixApp pat1 qName pat2)=
    desugar$ PApp qName [pat1,pat2]

  -- HSE
  desugar (PTuple Boxed []) = desugar $ PApp (Special UnitCon) []
  desugar (PTuple Unboxed []) = error "Language.Haskell.Exts.Desugaring.desugar: Unboxed tuples not supported."
  desugar (PTuple Boxed [p]) = desugar p
  desugar (PTuple Unboxed _) = error "Language.Haskell.Exts.Desugaring.desugar: Unboxed tuples not supported."
  desugar (PTuple Boxed pats)=
    desugar$ PApp (Special $ TupleCon Boxed $ length pats) pats

  -- HSE
  desugar (PList []) = desugar $ PApp (Special ListCon) []
  desugar (PList pats) =
    desugar $ foldr (\p a -> PApp (Special Cons) [p,a]) (PList [])  pats

  desugar (PRec qName patFields) = error "Not supported!"
  desugar (PRPat rPats ) = error "Not supported!"
  desugar (PXTag srcLoc xName pXAttrs mPat pats ) =
    error "Not supported!"
  desugar (PXETag srcLoc xName pXAttrs mPat) = error "Not supported!"
  desugar (PXPcdata string) = error "Not supported!"
  desugar (PXPatTag pat) = error "Not supported!"
  desugar (PXRPats rPats) = error "Not supported!"
  desugar (PExplTypeArg qName t) = error "Not supported!"
  desugar (PQuasiQuote s1 s2) = error "Not supported!"

instance Desugar Exp where

  -- 3.2
  -- no desugaring
  desugar (Var qName)   =
    Var $$ qName

  -- 3.2
  -- no desugaring
  -- could be desugared to Var qname
  desugar (Con qName) =
    Con $$ qName

  -- no desugaring
  -- not 3.2
  -- could be considered as constant functions (Var)
  desugar (Lit literal) =
    Lit $$ literal

  -- 3.2
  -- no desugaring
  desugar (App e1 e2) =
    App $$ e1 ** e2

  -- 3.3
  -- HSE error
  desugar (Lambda src [] body) =
    error "No header for the lambda expression!"

  desugar (Lambda src [p] body)
    | (case p of {PVar _ -> False; _ -> True}) = do
     name <- newVar
     desugar $
        Lambda src [PVar $ Ident name]
         (Case (Var $ UnQual $ Ident name)
          [Alt (noLoc) p (UnGuardedAlt body) (BDecls [])])
  desugar (Lambda src ps body)
    | any (\p -> case p of {PVar _ -> False; _ -> True}) ps = do
     names <- sequence [newVar| _ <-ps]
     desugar $
        Lambda src ((PVar . Ident) <$> names)
         (Case (Tuple Boxed $ (Var . UnQual . Ident) <$> names)
          [Alt (noLoc) (PTuple Boxed ps) (UnGuardedAlt body) (BDecls [])])
  desugar (Lambda src [p] body) =
    Lambda $$ src ** [p] ** body
  desugar (Lambda src (p:ps) body) =
    Lambda $$ src  ** [p] ** (Lambda src ps body)

  -- 3.4
  desugar (NegApp e) =
    App $$ (Var (UnQual (Ident "negate"))) ** e

  -- 3.4
  desugar (InfixApp exp1 (QVarOp qName) exp2) = do
    e1 <- desugar exp1
    e2 <- desugar exp2
    return $ App (App (Var qName) e1) e2

  -- 3.4
  desugar (InfixApp exp1 (QConOp qName) exp2) = do
    e1 <- desugar exp1
    e2 <- desugar exp2
    return $ App (App (Con qName) e1) e2

  -- 3.5
  desugar (LeftSection ex qOp) = do
    n <- newVar
    e <- desugar ex
    return $  Lambda (noLoc)
      [PVar $ Ident n]
      (InfixApp e qOp (Var $ UnQual $ Ident n))

  -- 3.5
  desugar  (RightSection qOp ex) = do
    n <-newVar
    e <- desugar ex
    return $  Lambda (noLoc)
        [PVar $ Ident n]
        (InfixApp (Var $ UnQual $ Ident n) qOp e)

  -- 3.6
  desugar (If cond th el) =
    desugar $
    Case cond [ Alt (noLoc)
                (PApp (UnQual (Ident "True")) []) (UnGuardedAlt th) (BDecls [])
              ,Alt (noLoc)
               (PApp (UnQual (Ident "False")) []) (UnGuardedAlt el) (BDecls [])]

  -- 3.7
  desugar (List es) = do
   exps <- mapM desugar es
   return $ foldr (\e a -> App (App (Con $ Special Cons) e) a)
                  (Con (Special ListCon)) exps

  -- not 3.8
  -- common sense
  desugar (Tuple Boxed []) = desugar $ Con (Special UnitCon)
  desugar (Tuple Boxed [e]) = desugar $ e
  desugar (Tuple Boxed es@(_:_)) = do
    exps <- mapM desugar es
    return $ foldl App (Con $ Special $ TupleCon Boxed $ length exps) exps

  -- 3.9
  desugar (Paren ex) =
    desugar ex

  -- 3.10
  desugar  (EnumFrom exp) =
      (App  (Var (UnQual (Ident "enumFrom")))) $$ exp

  -- 3.10
  desugar  (EnumFromTo ex1 ex2) = do
    e1 <- desugar ex1
    e2 <- desugar ex2
    return $  App (App (Var (UnQual (Ident "enumFromTo"))) e1) e2

  -- 3.10
  desugar  (EnumFromThen ex1 ex2) = do
    e1 <- desugar ex1
    e2 <- desugar ex2
    return $  App (App (Var (UnQual (Ident "enumFromThen"))) e1) e2

  -- 3.10
  desugar   (EnumFromThenTo ex1 ex2 ex3) = do
    e1 <- desugar ex1
    e2 <- desugar ex2
    e3 <- desugar ex3
    return $
      App (App (App (Var (UnQual (Ident "enumFromThen"))) e1) e2) e3

  -- not 3.11
  -- Generalized to monad comprehensions
  -- based on: "Comprehending Moands" By Walder
  desugar (ListComp eexp qualStmts) =
       desugar $
       Do ( (cQualStmt <$> qualStmts) ++
            [(Qualifier (App (Var ((UnQual (Ident "return")))) eexp))])

  -- 3.12
  desugar (Let binds ex) =
    Let $$ binds ** ex

  -- 3.13 & 3.17.3  (a,b,c,s,t,u,v)
  -- only translations up to removal of guards are applied
  -- the optimization transformations (d .. r) are not implemented
  desugar (Case e alts) =  case e of
   --------------------------
   {(Con (Special UnitCon)) ->
     case alts of
     {((Alt src p galt decls)
       : talts@((Alt _ PWildCard (UnGuardedAlt e')
         (BDecls [])):[])) ->
         case galt of
         {(UnGuardedAlt e) ->
             stepA
          ----------------------
         ;(GuardedAlts gss) ->
           case p of
           {(PApp (Special UnitCon) []) ->
               case gss of
                 { [] ->
                      error "Wrong HSE Tree!"
                 ;[GuardedAlt _ stmts e] ->
                   case stmts of
                    { [] ->
                         error "Wrong HSE Tree!"
                    ; -- .v
                     [Qualifier e0] ->
                        desugar $ If e0 e e'
                    ; -- .u
                     [LetStmt decls] ->
                       desugar $ Let decls e
                    ; -- .t
                      [Generator _ p e0] ->
                       desugar $
                       Case e0
                       [Alt (noLoc) p (UnGuardedAlt e)(BDecls [])
                       ,Alt (noLoc)  PWildCard (UnGuardedAlt e')
                        (BDecls [])]
                    ; -- .s
                     gs  ->
                         desugar $ foldr
                         (\g ex->
                           (Case (Con (Special UnitCon))
                            ((Alt (noLoc) (PApp (Special UnitCon) [])
                              (GuardedAlts [GuardedAlt (noLoc) [g] e])
                              (BDecls []))
                             : (Alt (noLoc) PWildCard (UnGuardedAlt ex)
                                (BDecls [])):[]))
                         ) e' gs
                    }
                 ; gss ->
                     stepC  ((Alt src p (GuardedAlts gss) decls):talts)}
           ;_ ->   stepC  ((Alt src p (GuardedAlts gss) decls):talts)}
         }
        ;_ -> stepB
        }
   -----------
   ; (Var v) -> case alts of
      ---------------------
      {((Alt src p galt decls)
       : talts@((Alt _ PWildCard (UnGuardedAlt e')
         (BDecls [])):[])) ->
          case galt of
          -- common sense / final desired state
          {(UnGuardedAlt e) ->
              let
                ed = case decls of
                  {  BDecls [] ->
                        e
                  ; _ ->
                    Let decls e}
              in Case (Var v) <$>
                 sequence [Alt (noLoc) $$ p <*> (UnGuardedAlt $$ ed)
                           <*> return (BDecls [])
                          ,Alt (noLoc) PWildCard <$> (UnGuardedAlt $$ e')
                           <*> return (BDecls [])]
          ----------------------
          ;(GuardedAlts galts) ->
                stepC  ((Alt src p (GuardedAlts galts) decls):talts)
          }
      ----
      ; _ -> stepB}
    ----------
   ; _       ->
          stepA}
   where
      -- .a
      stepA = do
        v <- newVar
        desugar $
          App (Lambda (noLoc) [PVar $ Ident v]
               (Case (Var $ UnQual $ Ident v) alts))
          e
      -- .b
      stepB  = do
          desugar $ foldr (\alt ex ->
                            Case e [alt
                                   ,Alt (noLoc) PWildCard
                                    (UnGuardedAlt ex) (BDecls [])]
                          )
            (App (Var (UnQual (Ident "error"))) (Lit (String "No match")))
            alts
      -- .c
      stepC ((Alt _ p (GuardedAlts galts) decls)
              :(Alt (noLoc) PWildCard (UnGuardedAlt e')
                (BDecls [])):[]) = do
        {y <- newVar
        ;let fld = foldr
                   ( \(GuardedAlt _ stmts e) ex ->
                      Case (Con (Special UnitCon))
                      [(Alt (noLoc) (PApp (Special UnitCon) [])
                        (GuardedAlts [GuardedAlt (noLoc) stmts e])
                        (BDecls []))
                      , (Alt (noLoc) PWildCard (UnGuardedAlt ex)
                         (BDecls []))
                      ]
                   )
                   (Var $ UnQual $ Ident y) galts
        ;desugar $ Case e'
         [Alt (noLoc) (PVar $ Ident y)
          (UnGuardedAlt
           (Case e
            [Alt (noLoc) p (UnGuardedAlt
                               (Let decls
                                (fld)))(BDecls [])
            , Alt (noLoc) PWildCard
              (UnGuardedAlt $ Var $ UnQual $ Ident  y)
              (BDecls []) ])) (BDecls [])]}

  -- 3.14
  desugar (Do [])            =
    error "Empty do block!"
  desugar (Do [Qualifier e]) =
    return e
  desugar (Do [_])           =
    error "The last statement in a 'do' block must be an expression!"
  desugar (Do ((Qualifier e):ss)) =
    desugar $ InfixApp e (QVarOp (UnQual (Symbol ">>"))) (Do ss)
  desugar (Do ((Generator _ p e):stmts)) = do
    ok <- newVar
    desugar $
     Let
      (BDecls
       [FunBind [Match (noLoc) (Ident ok)
                 [p] Nothing
                 (UnGuardedRhs (Do stmts))
                 (BDecls [])
                ,Match (noLoc) (Ident ok)
                 [PWildCard] Nothing
                 (UnGuardedRhs (App (Var (UnQual (Ident "fail")))
                                (Lit (String "..."))))
                 (BDecls [])]])

      (InfixApp e
       (QVarOp (UnQual (Symbol ">>=")))
       (Var (UnQual (Ident ok))))
  desugar (Do ((LetStmt bs):ss)) =
      desugar $ Let bs (Do ss)

  -- not 3.15.2
  desugar (RecConstr qName fieldUpdates) =
    error "RecConstr is not supported!"
  -- not 3.15.3
  desugar (RecUpdate eexp fieldUpdates) =
    error "RecUpdate is not supported!"

  -- 3.16
  desugar (ExpTypeSig srcLoc e t) = do
    v <- newVar
    desugar $
     Let (BDecls [TypeSig (noLoc) [Ident v] t
                 ,PatBind (noLoc) (PVar (Ident v)) Nothing
                  (UnGuardedRhs e) (BDecls [])]) (Var (UnQual (Ident v)))


  -- common sense
  desugar (TupleSection Boxed mes) = do
    eExps <- nameNothings mes
    desugar $
     let
          ps =  [PVar n |Left n  <- eExps]
          body = (\x -> case x of
                         Left n  -> Var $ UnQual n
                         Right e -> e) <$> eExps
      in
       Lambda (noLoc) ps (Tuple Boxed body)

  -- Not Supported
  desugar (ParComp  eexp qualStmtss) =  error "Not supported!"
 {- let comps = [ ListComp
                (Tuple [patToExp p| (Generator _ p _ ) <- qualStmts ])
                qualStmts
              |  qualStmts <- qualStmtss
  let x = Generator (noLoc) (PTuple [PTuple  | <-])
      (foldl App (Var (UnQual $ Ident ("zip" ++ (show (length comps))))) comps )
       desugar (ListComp eexp x)  -}
  desugar (MDo stmts) = error "Not supported!"
  desugar (IPVar iPName)  =  error "Not supported!"
  -- Template Haskell
  desugar (VarQuote qQName)  =  error "Not supported!"
  desugar (TypQuote qQName)  =  error "Not supported!"
  desugar (BracketExp bBracket)  =  error "Not supported!"
  desugar (SpliceExp sSplice)  =  error "Not supported!"
  desugar (QuasiQuote sString1 sString2)  =  error "Not supported!"
  -- Hsx
  desugar (XTag sSrcLoc xXName xXAttrs mExp eExps)  =  error "Not supported!"
  desugar (XETag sSrcLoc xXName xXAttrs mExp)  =  error "Not supported!"
  desugar (XPcdata sString)  =  error "Not supported!"
  desugar (XExpTag eExp)  =  error "Not supported!"
  desugar (XChildTag sSrcLoc eExps)  =  error "Not supported!"
  -- Pragmas
  desugar (CorePragma        string eExp)  =  error "Not supported!"
  desugar (SCCPragma         sString eExp)  =  error "Not supported!"
  desugar (GenPragma s (i1,i2) (i3,i4) eExp)  =  error "Not supported!"
  -- Arrows
  desugar (Proc sSrcLoc     pPat eExp)  =  error "Not supported!"
  desugar (LeftArrApp      eExp1 eExp2)  =  error "Not supported!"
  desugar (RightArrApp     eExp1 eExp2)  =  error "Not supported!"
  desugar (LeftArrHighApp  eExp1 eExp2)  =  error "Not supported!"
  desugar (RightArrHighApp eExp1 eExp2)  =  error "Not supported!"

instance Desugar Binds where
  desugar (BDecls ds) = do
     BDecls <$> desugarDecls ds
  desugar (IPBinds _) =
    error "Not supported!"

instance Desugar DataOrNew where
  desugar = return

instance Desugar QualConDecl where
  desugar (QualConDecl src tvs ctx condecl) =
    QualConDecl $$ src ** tvs ** ctx ** condecl

instance Desugar ConDecl where
  desugar (ConDecl n bts) = ConDecl $$ n ** bts
  desugar (InfixConDecl bt1 n bt2) = desugar $
    ConDecl n [bt1,bt2]
  desugar (RecDecl n rs) = RecDecl $$ n ** rs

instance (Desugar a,Desugar b) => Desugar (a, b) where --deriving
  desugar (qName, ts) = do
    q <- desugar qName
    ts <- desugar ts
    return (q , ts)

instance Desugar BangType where
  desugar (BangedTy t)   = BangedTy   $$ t
  desugar (UnBangedTy t) = UnBangedTy $$ t
  desugar (UnpackedTy t) = UnpackedTy $$ t

instance Desugar Decl where
  desugar d@(TypeDecl src name tvs t ) =  do
    push $ (\(UnkindedVar x)->x) <$> tvs
    d <- TypeDecl $$ src ** name ** tvs ** t
    pop
    return d

  desugar d@(DataDecl src db ctx name tvs  qcds drs) = do
    push $ (\(UnkindedVar x)->x) <$> tvs
    d <- DataDecl $$ src ** db ** ctx ** name  ** tvs **  qcds ** drs
    pop
    return d

  desugar d@(DerivDecl src ctx qName ts) =
    DerivDecl $$ src ** ctx ** qName ** ts

  desugar d@(ClassDecl src ctx name tvs fundeps classDecls) = do
    push $ (\(UnkindedVar x)->x) <$> tvs
    cd' <- desugarDecls ((\(ClsDecl d)-> d) <$> classDecls)
    pop
    ClassDecl $$ src ** ctx ** name ** tvs <*> return fundeps
      <*> return (ClsDecl <$> cd')

  desugar d@(InstDecl src ctx qName ts instDecls) = do
    id' <- desugarDecls ((\ (InsDecl d) -> d) <$> instDecls)
    InstDecl $$ src ** ctx ** qName <*> return ts
      <*> return (InsDecl <$> id')

  desugar d@(PatBind src (PVar (Ident n)) (Just ty) (UnGuardedRhs exp) (BDecls []))
   = do
     -- having typevariables in the state desugar the type signature
     t@(TyForall (Just ttys) _ _)   <- desugar ty
     -- reset the state and store the old state
     tys <- pop
     -- push ttys -- for scoped type variables
     -- desugar the subexpression
     e    <-  desugar exp
     -- set the state back to the way it was
     push tys
     return $ PatBind  src   (PVar (Ident n)) (Just t)
       (UnGuardedRhs e)  (BDecls [])


  desugar d@(PatBind src (PVar (Ident n)) Nothing (UnGuardedRhs exp) (BDecls []))
   = (PatBind $$ src  ** (PVar (Ident n)) <*> return Nothing <*>
      (UnGuardedRhs $$ exp) <*> return
      (BDecls []))

  desugar d@(TypeFamDecl  src name tvs mk) = error "Not supported!"

  desugar d@(GDataDecl    src dn cxt name tvs mk gdcls drs ) = error "Not supported!"

  desugar d@(DataFamDecl  src  ctx name tvs mKind)  = error "Not supported!"

  desugar d@(DataInsDecl src db t qcds drs) = error "Not supported!"

  desugar d@(TypeInsDecl  src t1 t2) = error "Not supported!"

  desugar d@(GDataInsDecl src dn t mk gadtDecls drs)  = error "Not supported!"

  -- methods withouy body
  desugar d@(TypeSig      src names t)
   = TypeSig $$ src ** names ** t

  desugar d@(FunBind     _ )
   = error "Desugaring error: FunBind should already have been desugared!"

  desugar d@(PatBind _ _ _ _ _) = error "PatBind is in the wrong format!"

  desugar d@(DefaultDecl  src ts)
   =  error "Not supported!"

  desugar d@(SpliceDecl   src e)  = error "Not supported!"

  desugar d@(InfixDecl    src a i ops) = error "Not supported!"

  desugar d@(ForImp   src cnv st s name t)= error "Not supported!"

  desugar d@(ForExp   src cnv s name t)= error "Not supported!"

  desugar d@(RulePragmaDecl   _ _)= error "Not supported!"

  desugar d@(DeprPragmaDecl   _ _)= error "Not supported!"

  desugar d@(WarnPragmaDecl   _ _) = error "Not supported!"

  desugar d@(InlineSig        _ _ _ _) = error "Not supported!"

  desugar d@(InlineConlikeSig _ _ _) = error "Not supported!"

  desugar d@(SpecSig          src activation qName ts) = error "Not supported!"

  desugar d@(SpecInlineSig    src b ac qName ts)= error "Not supported!"

  desugar d@(InstSig          src ctx qName ts) = error "Not supported!"

  desugar d@(AnnPragma        src ann)= error "Not supported!"


instance Desugar Module where
  desugar (Module src n os mw me i ds) =
    Module src n os mw me i <$> desugarDecls ds

---------------------------------------
desugarDecls :: [Decl] -> Unique [Decl]
desugarDecls ds =  do
  let
    (fpbs,others) = partition isPatFun ds
  pbs <- concat <$> mapM desugarPatFunBind fpbs
  let
    (sgs,rest) = partition isSig others
    sigs = [ (n,t) | TypeSig _ ns t <- sgs, n <- ns ]
    -- attach signatures to their matching definitions
    explPBs =
              [ PatBind src (PVar n)
                (lookup n sigs)
                r bs
              | PatBind src (PVar n) _ r bs <- pbs]
    noBodySigs =
      [TypeSig (noLoc) [n] t
      |(n,t)<- sigs
      , notElem n [pn|PatBind _ (PVar pn) _ _ _ <- pbs] ]
    ds' = rest ++ noBodySigs ++explPBs
  desugar ds'


desugarPatFunBind :: Decl -> Unique [Decl]
-- 4.4.3.1
desugarPatFunBind f@(FunBind ms@((Match _ n ps _ _ _ ):_)) =  do
  names <- sequence [ Ident <$> newVar
                    | _  <- [1..length ps]]
  concat <$> mapM desugarPatFunBind
    [PatBind (noLoc) (PVar n) Nothing
     (UnGuardedRhs (Lambda (noLoc)
                    (PVar <$> names)
                    (Case (Tuple Boxed ((Var . UnQual) <$> names))
                     (cMatchs ms))))
     (BDecls [])]

-- 4.4.3.2
desugarPatFunBind (PatBind src p m (GuardedRhss  grhss) bnds) =
  concat <$> mapM desugarPatFunBind
  [PatBind src p m
  (UnGuardedRhs
   (Let bnds
     (Case (Con (Special UnitCon))
      [Alt (noLoc) (PApp (Special UnitCon) [])
       (GuardedAlts
        (cGuardedRhs <$> grhss)
       )(BDecls [])]
     )
   ))
  (BDecls [])]

-- Final State
desugarPatFunBind e@(PatBind src (PVar (Ident n)) m (UnGuardedRhs exp) (BDecls [])) =
    return  [e]

-- THIH 11.6.3
desugarPatFunBind (PatBind src p mt (UnGuardedRhs exp) (BDecls [])) = do
  seed <- newVar
  concat <$> mapM desugarPatFunBind
    ((PatBind (noLoc) (PVar $ Ident $ seed) mt (UnGuardedRhs exp) (BDecls []))
     :
     ((\v ->
        (PatBind (noLoc) (PVar $ v) Nothing
         (UnGuardedRhs
          (Case (Var (UnQual (Ident $ seed)))
           [Alt (noLoc) p (UnGuardedAlt (Var (UnQual v)))
            (BDecls [])]) ) (BDecls []))) <$> (patVar p)
     ))

{-
instance Desugar ClassDecl where
  desugar (ClsDecl decl) =  ClsDecl $$ decl

  desugar  x = error "Not Supported!"

instance Desugar InstDecl where
  desugar (InsDecl decl) = InsDecl $$ decl
  desugar  x = error "Not Supported!" -}

-- Converting Matches to Alts
-- HSE
---------------------------
cMatchs :: [Match] -> [Alt]
cMatchs ms  = cMatch <$> ms

cMatch :: Match -> Alt
cMatch (Match _ _ ps _ rhs binds) =
  Alt (noLoc) (PTuple Boxed ps) (cRhs rhs) binds

cRhs :: Rhs -> GuardedAlts
cRhs (UnGuardedRhs exp) =
  UnGuardedAlt exp
cRhs (GuardedRhss grhss) =
  GuardedAlts (cGuardedRhs <$> grhss)

cGuardedRhs :: GuardedRhs -> GuardedAlt
cGuardedRhs (GuardedRhs _ stmts exp) =
  GuardedAlt (noLoc) stmts exp


desugarLambda2Alt :: Exp -> Alt
desugarLambda2Alt (Lambda _ [p] body) =
  Alt (noLoc) p (UnGuardedAlt body) (BDecls [])

-- variables / name bound in a pattern
patVar :: Pat -> [Name]
patVar (PVar name)  = [name]
patVar (PLit _) = []
patVar (PatTypeSig _ pat _) = patVar pat
patVar (PApp _ pats) = concat (patVar <$> pats)
patVar (PAsPat name pat) = name : (patVar pat)
patVar (PParen pat) = patVar pat
patVar (PIrrPat pat) = patVar pat
patVar (PBangPat pat) = patVar pat
patVar (PNeg _) = []
patVar (PInfixApp pat1 _ pat2) = (patVar pat1) ++ (patVar pat2)
patVar (PTuple Boxed pats) =  concat $ patVar <$> pats
patVar (PList pats) = concat $ patVar <$> pats
patVar PWildCard  = []
patVar (PNPlusK _ _) = []
patVar (PViewPat _ pat) = patVar pat
patVar x = Prelude.error $ "Pattern " ++ (prettyPrint x) ++ " is not supported!"

{-
desugarPatBind2FunBind :: Decl -> Decl
desugarPatBind2FunBind
  (PatBind _ (PVar v) _ (UnGuardedRhs e) (BDecls [])) =
    FunBind [Match (noLoc) v [] Nothing (UnGuardedRhs e) (BDecls [])]
--desugarPatBind2FunBind x =
--  error "Desugaring error: patbind not in a correct format!"-}

nameNothings ::  [Maybe a] -> Unique [Either Name a]
nameNothings = mapM f
  where
    f :: Maybe a -> Unique (Either Name a)
    f Nothing  = Left . Ident <$> newVar
    f (Just x) =  return $ Right x

-- not implemented completely
-- based on: "Bringing Back Monad Comprehensions" By Giorgidze et al
cQualStmt :: QualStmt -> Stmt
cQualStmt (QualStmt (Qualifier e))       =
      Qualifier (App (Var (UnQual (Ident "guard"))) e)
cQualStmt (QualStmt g@(Generator _ _ _)) =
      g
cQualStmt (QualStmt l@(LetStmt _))       =
      l


isPatFun :: Decl -> Bool
isPatFun d = case d of
  PatBind _ _ _ _ _ -> True
  FunBind _ -> True
  _ -> False

isSig :: Decl -> Bool
isSig d = case d of
  TypeSig _ _ _ -> True
  _ -> False


tyvars :: Type -> [Name]
--tyvars (TyForall Nothing ctx t) = tyvars t --ambiguous types are not supported
tyvars (TyApp t1 t2) = (tyvars t1) `union`  (tyvars t2)
tyvars (TyVar n) = [n]
tyvars (TyCon _) = []
tyvars _ = Prelude.error "Not supported!"

{-
demoteQualConDecl :: Name -> [Name]-> QualConDecl -> Exp
demoteQualConDecl d vars (QualConDecl _ [] [] cdecl)
  = demoteConDecl d vars cdecl

demoteConDecl :: Name -> [Name]-> ConDecl -> Exp
demoteConDecl d vars (ConDecl _ bts)
  = App (App (Var (UnQual (Symbol "-->")))
         (foldl1
          (\a e ->App (App (Var (UnQual (Symbol "-->"))) a) e)
          (demoteBangType <$> bts) ))
         (foldl App  (Var $ UnQual d) ( (Var . UnQual)  <$> vars) )
demoteConDecl _ _ x = Prelude.error "Not supported!"

demoteBangType :: BangType -> Exp
demoteBangType (BangedTy   t) = demoteType t
demoteBangType (UnBangedTy t) = demoteType t
demoteBangType (UnpackedTy t) = demoteType t

demoteDecl :: Decl -> Decl
demoteDecl (DataDecl _ _ [] dn tys qconds drs) =
  PatBind (noLoc) (PVar dn') Nothing
  (UnGuardedRhs l) (BDecls [])
  where
    dn' = demoteName dn
    vars = (\(UnkindedVar n) -> n)  <$> tys
    pvars = PVar <$> vars
    l = Lambda (noLoc)  pvars $
         foldl1 (\a e ->App (App (Var (UnQual (Symbol "<+>"))) a) e)
        ((demoteQualConDecl dn' vars ) <$> qconds)
--TODO: demote of other declarations

demoteCTX :: Context -> Exp
demoteCTX []    = Var (UnQual (Ident "constraint"))
demoteCTX [asst] = demoteAsst asst
demoteCTX assts@(_:_)
  = foldl1
    (\a e -> App (App  (Var (UnQual (Symbol "<&>"))) a ) e)
    (demoteAsst <$> assts)

demoteAsst :: Asst -> Exp
demoteAsst (ClassA qName ts) = foldl App
                               (Var $ demoteQName qName)
                               (demoteType <$> ts)
demote x = Prelude.error "Not supported!"

demoteType :: Type -> Exp
demoteType (TyForall (Just bs) ctx ty) =
  Lambda (noLoc)
  ( (\(UnkindedVar n) -> PVar n)  <$> bs)
  (App (App (Var $ UnQual (Symbol "==>")) (demoteCTX ctx)) (demoteType ty))
demoteType (TyForall Nothing ctx ty) =
  Prelude.error "Wrong format!"
demoteType (TyApp t1 t2) =
  App (demoteType t1) (demoteType t2)
demoteType (TyCon qName) =
  Var $ demoteQName qName
demoteType (TyVar  n) =
  Var $ UnQual n


demoteQName :: QName -> QName
demoteQName (Qual m n) = Qual m $ demoteName n
demoteQName (UnQual n) = UnQual $ demoteName n
demoteQName (Special UnitCon) =  UnQual $ Ident "tUnit"
demoteQName (Special ListCon) =  UnQual $ Ident "tList"
demoteQName (Special FunCon)  =  UnQual $ Ident "-->"
demoteQName (Special (TupleCon Boxed i)) =  UnQual $ Ident
                                          $ "tTuple" ++ (Prelude.show i)

demoteName :: Name -> Name
demoteName (Ident n) = Ident $ "t" ++ n
demoteName (Symbol n) = Ident $ ":" -}
