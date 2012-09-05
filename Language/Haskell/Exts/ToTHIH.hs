-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Exts.ToTHIH
-- Copyright   :  (c) Shayan Najd
-- License     :  BSD-style (see the file LICENSE.txt)
--
-- Maintainer  :  Shayan Najd, shayan@chalmers.se
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Language.Haskell.Exts.ToTHIH where
import qualified Prelude
import Prelude (Bool(..),($),error)
import Language.Haskell.THIH.Syntax as TH
import Language.Haskell.THIH.SurfaceTypes 
import Language.Haskell.THIH.BasicTypes
import Language.Haskell.Exts.Syntax as HSE 
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Desugaring hiding (error)
 
import Data.List(partition,(++),foldl1,foldl,null)
import Data.Maybe(Maybe(..),fromJust,maybe)
import Control.Applicative ((<$>))


cId :: Name -> Id
cId (Ident x) = x
cId (Symbol s) = s 

cId2 :: QName -> Id
cId2 x@(Qual _ _)  = prettyPrint x 
cId2 (UnQual n)    = cId  n
cId2 x@(Special FunCon) = "->"
cId2 x@(Special ListCon) = "[]"
cId2 x@(Special UnitCon) = "()"
cId2 x@(Special Cons) = ":"
cId2 x@(Special _) = prettyPrint x

cSPred :: Asst -> SPred
cSPred (ClassA qName ts) = SIsIn (cId2 qName) (cSType <$> ts)
cSPred x = error $ "Predicate " ++ (prettyPrint x) ++ " is not supported!"

cSVarBind :: TyVarBind -> SVarBind
cSVarBind (KindedVar name _) = cId name --No explicit kinding is supported!
cSVarBind (UnkindedVar name) = cId name

cSScheme :: HSE.Type -> SScheme
cSScheme (TyForall vars ps t) = SForall    
                                (maybe [] (cSVarBind <$>) vars) 
                                ((cSPred <$> ps):==> 
                                (cSType t))
cSScheme t                    = SForall [] ([]:==> (cSType t))

cSType :: HSE.Type -> SType 
cSType (TyCon qName) = SCon (cId2 qName)
cSType (TyApp t1 t2) = SApp  (cSType t1) (cSType t2)   
-- it's a hack and is expected to be replaced by TGen
cSType (TyVar n )    = SVar (cId n)  
cSType (TyKind x k)  = error "TyKind is not supported!" 
                       --   if explicit typing were allowed in the  
                       -- typechecker we could support TyKind.
cSType (TyForall (Just []) [] (x)) = cSType x
cSType x = error $ "Type is not desugared: " ++  (Prelude.show x)
                        
cLiteral :: HSE.Literal -> TH.Literal
cLiteral (Int i) = LitInt i
cLiteral (Char c) = LitChar c
cLiteral (Frac r) = LitRat  r
cLiteral (String s) = LitStr s
cLiteral x = error "Unboxed literals are not supported!"

cPat :: HSE.Pat -> TH.Pat
cPat (HSE.PVar n) = TH.PVar (cId n)
cPat (HSE.PWildCard) = TH.PWildcard
cPat (PAsPat n p ) = PAs (cId n) (cPat p)
cPat (HSE.PLit l) = TH.PLit (cLiteral l)
cPat (PNPlusK n i) = PNpk (cId n) i
cPat (PApp qName ps) = PCon (cId2 qName) (cPat <$> ps) 
                       --need to pass the environment
cPat (PIrrPat p) = PLazy (cPat p)
cPat (PatTypeSig _ pat ttype) = error "PatTypeSig is not supported!"
cPat (PViewPat eexp pat) = error "PViewPat is not supported!"
cPat (PRec qName patFields) = error "PViewPat is not supported!"
cPat (PNeg pl@(HSE.PLit (Int _))) = cPat pl
cPat (PNeg pl@(HSE.PLit (Frac _))) = cPat pl
cPat (PNeg _other) = 
  error "In Patterns, negation can only be applied to numeric literals!"
cPat (PBangPat pat) = cPat pat -- no effect on typechecking
cpat x = error "not supported" 

cExpr :: Exp -> Unkinded Expr
cExpr (HSE.Lit lit)  = TH.Lit (cLiteral lit)      
cExpr (HSE.Var qName)= TH.Var (cId2 qName)
cExpr (HSE.Con qName)= TH.Var (cId2 qName)
cExpr (App e1 e2)    = Ap (cExpr e1) (cExpr e2)
cExpr (HSE.Let binds e) = TH.Let (cBindGroup binds) (cExpr e)
cExpr (Lambda _ ps e) =  Lam  (TH.Alt (cPat <$> ps) (cExpr e)) 
cExpr (HSE.Case e alts) = TH.Case (cExpr e) (cTHAlt <$> alts)
cExpr (HSE.ExpTypeSig srcLoc eexp ttype) = error "ExpTypeSig is not supported!"
cExpr (MDo stmts) = error "MDo is not supported!"
cExpr (RecConstr qName fieldUpdates) = 
  error "Really? Haskell2010 records? I don't support them!"
cExpr (RecUpdate eexp fieldUpdates) = 
   error "Really? Haskell2010 records? I don't support them!"
cExpr x = Prelude.error $ 
          "Other expression formats are not supported: " ++ (Prelude.show x)   
 
type THAlt = (TH.Pat,Unkinded Expr)
cTHAlt :: HSE.Alt -> THAlt 
cTHAlt (HSE.Alt _ p (UnGuardedAlt e) (BDecls [])) =
  (cPat p, cExpr e)
cTHAlt x = error "Conversion of Alts Failed!"

cExpl :: Decl   -> Unkinded Expl
cExpl (PatBind _ (HSE.PVar n) (Just t) (UnGuardedRhs e)  _ ) =
 Expl (cId n) (cSScheme t) [TH.Alt [] (cExpr e)]

 
cImpl :: Decl -> Unkinded  Impl
cImpl (PatBind _ (HSE.PVar n) _ (UnGuardedRhs e)  _ ) = 
  Impl (cId n) [TH.Alt [] (cExpr e)]

cBindGroup :: Binds -> Unkinded  BindGroup
cBindGroup (BDecls ds) = 
  let
    (hexpls,himpss) = dependencyAnalysis ds
  in BindGroup (cExpl <$> hexpls) ((cImpl <$>) <$> himpss)
cBindGroup (IPBinds ps) = error "IPBinds is not supported!"

cProgram :: [HSE.Binds] -> Unkinded  Program
cProgram bs = Program $  cBindGroup <$> bs
 
cSModule :: Module -> SModule
cSModule (Module _ _ _ _ _ _ decls) =
  let 
    tySyns  = [ STypeSynonym (cId n)    
               [cId n |UnkindedVar n <- tys]
               (cSType t)
              | TypeDecl _ n tys t <- decls ]
    dataTys = [ SDataType nD
                vars
                [ (cId cn
                  , foldl1 (\a e -> (SApp (SApp (SCon "->") a) e ))     
                    (bts' ++ [tD]))
                | QualConDecl _ [] [] (ConDecl cn bts) <- qualConDecls
                , let bts' = (\(UnBangedTy x) -> cSType x) <$> bts]
              
              | DataDecl _ _ [] n tys qualConDecls _ <- decls
              , let nD = cId n                                         
              , let vars = (\(UnkindedVar x) -> cId x) <$> tys
              , let tyVars = SVar <$> vars
              , let tD = foldl SApp (SCon nD )tyVars]          
    tyClss  = [STypeClass 
               (cSPred <$> context)
               nc
               vars
               ( -- signatures of default methods
                 [  (cId n, cSScheme tt)
                 | ClsDecl pb@(PatBind _ (HSE.PVar n) (Just tt) _ _) <- cls]
               ++ 
                 -- signatures without body
                 [  (cId n, cSScheme tt)
                 | ClsDecl pb@(TypeSig _ [n] tt) <- cls])
               | ClassDecl _ context n tys [] cls <- decls
               , let vars = (\(UnkindedVar x) -> cId x) <$> tys
               , let nc   = cId n ]
    instns  = ([ SInstance
                 (cSPred <$> cxt) 
                 (cId2 qName)
                 (cSType <$> ts)
               | InstDecl _ cxt qName ts _ <- decls] 
               ++ 
               [ SInstance
                []
                (cId2 qName)
                [foldl SApp (SVar $ cId n ) 
                 ((\(UnkindedVar x) -> SVar $ cId x) <$> tys)]
               | DataDecl _ _ _ n tys _ drs <- decls
               , (qName,[]) <- drs]
               ++
               [ SInstance
                 (cSPred <$> ctx)
                 (cId2 qName)
                 (cSType <$> ts)
               | DerivDecl _ ctx qName ts <- decls ])
    pbs     = cProgram
             [ BDecls [ pb | pb@(PatBind _ _ _ _ _) <- decls]]
   in 
   SModule tySyns dataTys tyClss instns pbs

-- Just a too simplistic implementation
dependencyAnalysis :: [Decl] -> ([Decl],[[Decl]])  
dependencyAnalysis ds =   
  let (expls, impls) = partition isExplTyped ds
      implss | null impls = []
             | True = [impls]
  in  (expls,implss) 
  where
    isExplTyped :: Decl -> Bool
    isExplTyped (PatBind _ (HSE.PVar n)  (Just _) _ _) = True
    isExplTyped _ = False
 	

     