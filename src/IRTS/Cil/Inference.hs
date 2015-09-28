{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module IRTS.Cil.Inference (TExp(..), inferDecls) where

import           Control.Monad.State
import           Control.Monad.RWS
import           Control.Monad (replicateM)
import           IRTS.Lang
import           IRTS.Simplified
import           Idris.Core.CaseTree (CaseType(Shared))
import           Idris.Core.TT hiding (Type, TCon, instantiate)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Language.Cil as Cil

import Debug.Trace

newtype TVar = TV String deriving (Eq, Ord)

instance Show TVar where
  show (TV s) = s

data TCon = TCon String Int [Type] deriving (Show, Eq, Ord)

data Type
  = TVar TVar
  | TData (Set.Set TCon)
  | TPrim Cil.PrimitiveType
  | TFun [TVar] [Type] Type
  | TAny
  | TNothing
  deriving (Show, Eq, Ord)

data TDecl = TSFun Name [Name] Int TExp Type
  deriving Show

data TExp
  = TSV LVar Type
  | TSApp Bool Name [(LVar, Type)] Type
  | TSLet LVar TExp TExp
  | TSUpdate LVar TExp
  | TSCon (Maybe LVar)
          Int Name [LVar] Type
  | TSCase CaseType LVar [TSAlt]
  | TSChkCase LVar [TSAlt]
  | TSProj LVar Int
  | TSConst Const Type
  | TSForeign FDesc FDesc [(FDesc, LVar)]
  | TSOp PrimFn [(LVar, Type)] Type
  | TSNothing
  | TSError String
  deriving Show

data TSAlt
  = TSConCase Int Int Name [Name] TExp
  | TSConstCase Const TExp
  | TSDefaultCase TExp
  deriving Show

expType :: TExp -> Type
expType (TSV _ t) = t
expType (TSApp _ _ _ t) = t
expType (TSLet _ _ t) = expType t
expType (TSCon _ _ _ _ t) = t
expType (TSCase _ _ (alt:alts)) = altType alt -- whop whop
expType (TSChkCase _ (alt:alts)) = altType alt
expType (TSProj _ _) = error "TSProj type"
expType (TSConst _ t) = t
expType (TSForeign _ _ _) = error "TSForeign type"
expType (TSOp _ _ t) = t
expType TSNothing = TNothing
expType (TSError _) = error "Error type"

altType (TSConCase _ _ _ _ e) = expType e
altType (TSConstCase _ e) = expType e
altType (TSDefaultCase e) = expType e

instance Ord LVar where
  (Glob _) `compare` (Loc _) = GT
  (Loc _) `compare` (Glob _) = LT
  (Glob a) `compare` (Glob b) = a `compare` b
  (Loc a) `compare` (Loc b) = a `compare` b

newtype TypeEnv = TypeEnv (Map.Map LVar Type) deriving (Show)
emptyEnv = TypeEnv Map.empty

data InferState = InferState { count :: Int }
type Constraint = (Type, Type)
type Infer a = RWS TypeEnv [Constraint] InferState a

extend :: TypeEnv -> (LVar, Type) -> TypeEnv
extend (TypeEnv env) (lv, t) = TypeEnv (Map.insert lv t env)

unify :: Type -> Type -> Infer ()
unify t1 t2 = tell [(t1, t2)]

data SubstKey = SubstTVar TVar | SubstType Type deriving (Eq, Ord, Show)
newtype Subst = Subst (Map.Map SubstKey Type)
  deriving (Eq, Ord, Show, Monoid)

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable TCon where
  apply s (TCon name tag args) = TCon name tag (apply s args)

instance Substitutable Type where
  apply _ (TPrim t)               = TPrim t
  apply (Subst s) t@(TData ctors) =
    case Map.lookup (SubstType t) s of
      Just t' -> apply (Subst s) t'
      Nothing -> TData $ Set.map (apply (Subst s)) ctors
  apply (Subst s) t@(TVar a)      = Map.findWithDefault t (SubstTVar a) s
  apply s@(Subst sm) (TFun tvs args ret)     = TFun tvs (map (apply s') args) (apply s' ret)
    where s' = Subst $ foldr Map.delete sm as'
          as' = map SubstTVar tvs
  apply _ TAny                    = TAny
  apply _ TNothing                = TNothing

instance Substitutable Constraint where
   apply s (t1, t2) = (apply s t1, apply s t2)

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env

instance Substitutable (LVar, Type) where
  apply s (lv, t) = (lv, apply s t)

instance Substitutable TDecl where
  apply s (TSFun n args i exp t) = TSFun n args i (apply s exp) (apply s t)

instance Substitutable TExp where
  apply s (TSV lv t) = TSV lv (apply s t)
  apply s (TSLet lv e1 e2) = TSLet lv (apply s e1) (apply s e2)
  apply s (TSApp tailrec name args ret) =
    TSApp tailrec name (map (apply s) args) (apply s ret)
  apply s (TSUpdate lv e) = TSUpdate lv (apply s e)
  apply s (TSCon lv tag name args ty) =
    TSCon lv tag name args (apply s ty)
  apply s (TSCase ct lv alts) = TSCase ct lv (map (apply s) alts)
  apply s (TSChkCase lv alts) = TSChkCase lv (map (apply s) alts)
  apply s (TSProj lv i) = TSProj lv i
  apply s (TSConst c t) = TSConst c (apply s t)
  apply s (TSOp primfn args ty) =
    TSOp primfn (map (apply s) args) (apply s ty)
  apply s e = e

instance Substitutable TSAlt where
  apply s (TSConCase ofs tag name args e) = TSConCase ofs tag name args (apply s e)
  apply s (TSConstCase c e) = TSConstCase c (apply s e)
  apply s (TSDefaultCase e) = TSDefaultCase (apply s e)

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  return $ TVar $ TV (letters !! count s)

instantiate :: Type -> Infer Type
instantiate (TFun tvs args ret) = do
  tvs' <- mapM (const fresh) tvs
  let s = Subst $ Map.fromList $ zip (map SubstTVar tvs) tvs'
      t = (TFun [] (apply s args) (apply s ret))
  return t
instantiate t = return t

generalize :: TypeEnv -> TDecl -> TDecl
generalize env (TSFun name argNames i e t@(TFun _ params ret)) =
  TSFun name argNames i e (TFun as params ret)
    where as = Set.toList $ freeTypeVars t `Set.difference` freeEnvVars env

freeTypeVars :: Type -> Set.Set TVar
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TFun tvs args ret) =
  fromArgs `Set.union` fromRet `Set.difference` Set.fromList tvs
  where fromArgs = foldr Set.union Set.empty $ map freeTypeVars args
        fromRet = freeTypeVars ret
freeTypeVars _ = Set.empty

freeEnvVars :: TypeEnv -> Set.Set TVar
freeEnvVars (TypeEnv env) = foldr (Set.union . freeTypeVars) Set.empty $ Map.elems env

lookupEnv :: LVar -> Infer Type
lookupEnv lv = do
  TypeEnv env <- ask
  case Map.lookup lv env of
    Nothing -> error $ "Unbound variable: " ++ show lv
    Just t  -> instantiate t

inferApp :: Type -> [SExp] -> Infer Type
inferApp ft args = do
  ts <- mapM infer args
  tv <- fresh
  let t = TFun [] (map expType ts) tv
  unify ft t
  return t

infer :: SExp -> Infer TExp

infer (SV l) = do
  t <- lookupEnv l
  return (TSV l t)

infer (SLet lv e1 e2) = do
  e1 <- infer e1
  e2 <- local (`extend` (lv, expType e1)) $ infer e2
  return (TSLet lv e1 e2)

infer (SApp tr name args) = do
  ft <- lookupEnv (Glob name)
  TFun [] argTys retTy <- inferApp ft (map SV args)
  return (TSApp tr name (zip args argTys) retTy)

infer (SOp primFn args) = do
  TFun [] argTys retTy <- inferApp (inferPrim primFn) (map SV args)
  return (TSOp primFn (zip args argTys) retTy)

infer (SConst c) = do
  let t = TPrim $ constType c
  return (TSConst c t)

infer (SCon reloc tag name params) = do
  args <- mapM (infer . SV) params
  let ty = TData $ Set.singleton $ TCon (show name) tag $ map expType args
  return (TSCon reloc tag name params ty)

infer SNothing = return TSNothing

infer (SCase caseType lv clauses) = do
  ce <- infer (SV lv)
  t <- fresh
  tclauses <- mapM (inferSAlt (expType ce) t) clauses
  return (TSCase caseType lv tclauses)

infer (SChkCase lv clauses) = do
  ce <- infer (SV lv)
  tclauses <- mapM (inferSAlt (expType ce) TAny) clauses
  return (TSChkCase lv tclauses)

infer sexp = error $ "Unhandled expression: " ++ show sexp

inferSAlt :: Type -> Type -> SAlt -> Infer TSAlt
inferSAlt vt t alt = do
  e <- inferClause vt alt
  unify (expType e) t
  return (mapAlt alt e)
  where
    mapAlt (SConCase ofs tag name names _) txp = TSConCase ofs tag name names txp
    mapAlt (SConstCase c _) txp = TSConstCase c txp
    mapAlt (SDefaultCase _) txp = TSDefaultCase txp

inferClause :: Type -> SAlt -> Infer TExp
inferClause _ (SDefaultCase e) = infer e
inferClause vt (SConCase offset tag name params e) = do
  args <- mapM (\(MN i _) -> fresh >>= \tv -> return (Loc $ i + offset, tv)) params
  env <- ask
  let ct = TData $ Set.singleton $ TCon (show name) tag (map snd args)
  unify vt ct
  local (extendEnv args) $ infer e
  where
    extendEnv args env = foldl extend env args
inferClause vt (SConstCase c e) = do
    let ct = TPrim $ constType c
    unify vt ct
    infer e

inferPrim :: PrimFn -> Type
inferPrim (LPlus (ATInt _)) = let t' = TPrim Cil.Int32 in TFun [] [t', t'] t'
inferPrim (LPlus ATFloat) = let t' = TPrim Cil.Float32 in TFun [] [t', t'] t'
inferPrim (LTimes (ATInt _)) = let t' = TPrim Cil.Int32 in TFun [] [t', t'] t'
inferPrim (LTimes ATFloat) = let t' = TPrim Cil.Float32 in TFun [] [t', t'] t'
inferPrim (LMinus (ATInt _)) = let t' = TPrim Cil.Int32 in TFun [] [t', t'] t'
inferPrim (LStrConcat) = let t = TPrim Cil.String in TFun [] [t, t] t
inferPrim (LStrEq) = TFun [] [TPrim Cil.String, TPrim Cil.String] (TPrim $ Cil.Int32)
inferPrim (LStrRev)= TFun [] [TPrim Cil.String] (TPrim Cil.String)
inferPrim (LStrSubstr) = TFun [] [TPrim Cil.Int32, TPrim Cil.Int32, TPrim Cil.String] (TPrim Cil.String)
inferPrim (LWriteStr) = TFun [] [TNothing, TPrim Cil.String] TNothing
inferPrim (LExternal (UN "prim__eqManagedPtr")) = TFun [] [TNothing, TNothing] (TPrim Cil.Int32)
inferPrim (LExternal (UN "prim__eqPtr")) = TFun [] [TNothing, TNothing] (TPrim Cil.Int32)
inferPrim (LExternal (UN "prim__writeString")) = TFun [] [TNothing, TPrim Cil.String] TNothing
inferPrim (LExternal _) = TNothing
inferPrim p = error $ "Unhandled primFn: " ++ show p

constType :: Const -> Cil.PrimitiveType
constType (BI _) = Cil.Int32 -- for now
constType (I _) = Cil.Int32
constType (Fl _) = Cil.Float32
constType (Ch _) = Cil.Char
constType (Str _) = Cil.String
constType (B8 _) = Cil.Char
constType (B32 _) = Cil.Int32
constType c = error $ "Unmapped Const: " ++ constDocs c

inferDecls :: TypeEnv -> [SDecl] -> [TDecl]
inferDecls env decls =
  let (fts, state, _) = runRWS (mapM freshType decls) env (InferState 0)
      env' = foldl extend env fts
      (_, cs, exps) = foldl (runInfer env') (state, [], []) decls
      subst = runSolve cs
  in map (generalize env . apply subst) exps
  where
    runInfer env (st, cs, decls) d@(SFun name _ _ _) =
      let (decl, st', cs') = runRWS (inferDecl d) env st
      in (st', cs ++ cs', decls ++ [decl])
    inferDecl :: SDecl -> Infer TDecl
    inferDecl (SFun name argNames i exp) = do
      (TFun tvs params ret) <- lookupEnv (Glob name)
      let args = map (\(i, tv) -> (Loc i, tv)) $ zip [0..] params
      e <- local (\env -> foldl extend env args) $ infer exp
      let t = expType e
      unify ret t -- TODO ???
      return (TSFun name argNames i e (TFun [] params t))
    freshType (SFun name@(MN _ "APPLY") _ _ _) = do
      return (Glob name, TFun (map TV tvs) (map (TVar . TV) tvs) TAny)
      where tvs = ["a", "b"]
    freshType (SFun name@(MN _ "EVAL") _ _ _) = do
      return (Glob name, TFun (map TV tvs) (map (TVar . TV) tvs) TAny)
      where tvs = ["a"]
    freshType (SFun name params _ _) = do
      args <- mapM (const fresh) params
      ret <- fresh
      return (Glob name, TFun (map (\(TVar a) -> a) $ args ++ [ret]) args ret) -- TODO

inferProgram :: [[SDecl]] -> [TDecl]
inferProgram declGroups =
  let (_, res) = foldl infer (emptyEnv, []) declGroups
  in res
 where
   infer (env, tdecls) sdecls =
     let tdecls' = trace ("env: " ++ show env) $ inferDecls env sdecls
         env' = foldr (\(TSFun name _ _ _ t) e -> trace ("ex: " ++ show t) $ extend e (Glob name, t)) env tdecls'
     in trace ("env': " ++ show env') (env', tdecls ++ tdecls')


emptySubst :: Subst
emptySubst = mempty

compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

-- | Solver

runSolve :: [Constraint] -> Subst
runSolve cs = solver (emptySubst, cs)
  where
    solver (su, cs) =
        case cs of
        [] -> su
        ((t1, t2) : cs0) ->
          let su1 = unifies t1 t2
          in solver (su1 `compose` su, fmap (apply su1) cs0)

unifyMany :: [Type] -> [Type] -> Subst
unifyMany [] [] = emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  let su1 = unifies t1 t2
      su2 = unifyMany (apply su1 ts1) (apply su1 ts2)
  in su2 `compose` su1
unifyMany t1 t2 = error $ "Unification mismatch: " ++ show t1 ++ " ~ " ++ show t2

unifies :: Type -> Type -> Subst
unifies t1 t2 | t1 == t2 = emptySubst
unifies (TVar v) t = v `bind` t
unifies t (TVar v) = v `bind` t
unifies (TFun [] args ret) (TFun [] args' ret') = unifyMany (args ++ [ret]) (args' ++ [ret'])
unifies t1@(TData ctors1) t2@(TData ctors2) | ctors1 /= ctors2 =
  let t = TData $ ctors1 `Set.union` ctors2
  in (Subst $ Map.fromList [(SubstType t1, t), (SubstType t2, t)])
unifies t1 t2 = error $ "Unification fail: " ++ show t1 ++ " ~ " ++ show t2

bind ::  TVar -> Type -> Subst
bind a t | t == TVar a     = emptySubst
         | otherwise       = Subst $ Map.singleton (SubstTVar a) t

-- | tests

add = SFun (UN "Main.add") [MN 0 "e", MN 1 "e"] 1
       (SOp (LPlus (ATInt ITNative)) [Loc 0,Loc 1])

add5 = SFun (UN "Main.add5") [MN 0 "e"] 1 (SLet (Loc 1) (SConst (I 5)) (SOp (LPlus (ATInt ITNative)) [Loc 0,Loc 1]))
slet = SLet (Loc 1) (SConst (I 5)) (SOp (LPlus (ATInt ITNative)) [Loc 0,Loc 1])

doubles = SFun (UN "Main.doubles") [MN 0 "e"] 2 (SLet (Loc 1) (SConst (Fl 3.0)) (SLet (Loc 2) (SLet (Loc 2) (SConst (Fl 42.0)) (SOp (LTimes ATFloat) [Loc 0,Loc 2])) (SOp (LPlus ATFloat) [Loc 1,Loc 2])))

bang = SFun (UN "Main.bang")[MN 0 "e"] 4
        (SLet (Loc 1) (SLet (Loc 1) SNothing
                        (SLet (Loc 2) (SConst (Str "!"))
                          (SLet (Loc 3) (SConst (I 3))
                            (SLet (Loc 4) (SConst (Str  ""))
                              (SApp False (UN "Main.repeat, repeat'")[Loc 1,Loc 2,Loc 3,Loc 4])))))
          (SOp LStrConcat [Loc 0,Loc 1]))

repeat' = SFun (UN "Main.repeat, repeat'" )[MN 0 "e", MN 1 "e", MN 2 "e", MN 3 "e"] 3
            (SCase Shared (Loc 2)
              [SConstCase (I 0)
                (SV (Loc 3))
              ,SDefaultCase
                (SLet (Loc 4) SNothing
                  (SLet (Loc 5) (SLet (Loc 5) (SConst (I 1))
                                  (SOp (LMinus (ATInt ITNative)) [Loc 2,Loc 5]))
                    (SLet (Loc 6) (SOp LStrConcat [Loc 3,Loc 1])
                      (SApp True (UN "Main.repeat, repeat'")[Loc 4,Loc 1,Loc 5,Loc 6]))))])

printFoo = SFun (UN "Main.printFoo")[MN 0 "e"] 1
             (SCase Shared (Loc 0)
               [SConCase 1 0 (UN "Main.FooNumber") [MN 0 "in"]
                 (SLet (Loc 2) SNothing
                   (SLet (Loc 3) (SConst (Str "!" ))
                     (SLet (Loc 4) (SConst (Str ""))
                       (SApp True (UN "Main.repeat, repeat'") [Loc 2,Loc 3,Loc 1,Loc 4]))))
               ,SConCase 1 1 (UN "Main.FooString") [MN 0 "in"]
                 (SV (Loc 1))])

-- putStr = SFun (UN "Prelude.Interactive.putStr") [MN 0 "e", MN 1 "e"] 5
--   (SLet (Loc 2) SNothing
--    (SLet (Loc 3) SNothing
--     (SLet (Loc 4) SNothing
--      (SLet (Loc 5) (SCon Nothing 65670 {U_Prelude.Interactive.{putStr0}1} [Loc 1])
--       (SLet (Loc 6) (SCon Nothing 65671 {U_Prelude.Interactive.{putStr1}1} [])
--        (SCon Nothing 65674 {U_io_bind1} [Loc 2,Loc 3,Loc 4,Loc 5,Loc 6]))))))

toIntNat = SFun (UN "Prelude.Nat.toIntNat, toIntNat'") [MN 0 "e", MN 1 "e", MN 2 "e"] 3
  (SCase Shared (Loc 1)
   [SConstCase (BI 0) (SV (Loc 2))
   ,SDefaultCase
    (SLet (Loc 3) (SLet (Loc 3) (SConst (BI 1)) (SOp (LMinus (ATInt ITBig)) [Loc 1,Loc 3]))
     (SLet (Loc 4) SNothing (SLet (Loc 5) (SLet (Loc 5) (SConst (I 1)) (SOp (LPlus (ATInt ITNative)) [Loc 2,Loc 5])) (SApp True (UN "Prelude.Nat.toIntNat, toIntNat'") [Loc 4,Loc 3,Loc 5]))))])

substr = SFun (UN "Prelude.Strings.substr") [MN 0 "e", MN 1 "e", MN 2 "e"] 3
  (SLet (Loc 3)
   (SLet (Loc 3) SNothing
    (SLet (Loc 4) (SConst (I 0))
     (SApp False (UN "Prelude.Nat.toIntNat, toIntNat'") [Loc 3,Loc 0,Loc 4])))
   (SLet (Loc 4)
    (SLet (Loc 4) SNothing
     (SLet (Loc 5) (SConst (I 0))
      (SApp False (UN "Prelude.Nat.toIntNat, toIntNat'") [Loc 4,Loc 1,Loc 5])))
    (SOp LStrSubstr [Loc 3,Loc 4,Loc 2])))

preludePutStr = SFun (UN "Prelude.Interactive.putStr") [MN 0 "e", MN 1 "e"] 5
  (SLet (Loc 2) SNothing
   (SLet (Loc 3) SNothing
    (SLet (Loc 4) SNothing
     (SLet (Loc 5) (SCon Nothing 65670 (MN 1 "U_Prelude.Interactive.{putStr0}") [Loc 1])
      (SLet (Loc 6) (SCon Nothing 65671 (MN 1 "U_Prelude.Interactive.{putStr1}") [])
       (SCon Nothing 65674 (MN 1 "U_io_bind") [Loc 2,Loc 3,Loc 4,Loc 5,Loc 6]))))))
  
testSubstr = SFun (UN "Main.testSubstr") [MN 0 "e"] 6
  (SCase Shared (Loc 0)
   [SConCase 1 0 (UN "Builtins.MkPair") [MN 0 "in", MN 1 "in"]
    (SLet (Loc 3) SNothing
     (SLet (Loc 4)
      (SLet (Loc 4)
       (SLet (Loc 4) (SConst $ Str "(")
        (SLet (Loc 5)
         (SLet (Loc 5) (SLet (Loc 5) (SConst $ Str "Hello, Idris!")
                        (SApp False (UN "Prelude.Strings.substr") [Loc 1,Loc 2,Loc 5]))
          (SLet (Loc 6) (SConst $ Str ")")
           (SOp LStrConcat [Loc 5,Loc 6])))
         (SOp LStrConcat [Loc 4,Loc 5])))
       (SLet (Loc 5) (SConst $ Str "\n") (SOp LStrConcat [Loc 4,Loc 5])))
      (SApp True (UN "Prelude.Interactive.putStr") [Loc 3,Loc 4])))])

applicativePure = SFun (UN "Prelude.Applicative.pure") [MN 0 "e",MN 1 "e",MN 2 "e"] 2
  (SCase Shared (Loc 2)
   [SConCase 3 0 (UN "constructor of Prelude.Applicative.Applicative") [MN 0 "in",MN 1 "in",MN 2 "in"]
    (SApp True (MN 0 "APPLY") [Loc 4,Loc 1])])

foldableFoldr = SFun (UN "Prelude.Foldable.foldr") [MN 0 "e",MN 1 "e",MN 2 "e",MN 3 "e"] 1
  (SLet (Loc 4) (SApp False (MN 0 "APPLY") [Loc 3,Loc 1])
   (SApp True (MN 0 "APPLY") [Loc 4,Loc 2]))

traverse_ = SFun (UN "Prelude.Traversable.traverse_") [MN 0 "e",MN 1 "e",MN 2 "e",MN 3 "e",MN 4 "e",MN 5 "e",MN 6 "e"] 7
  (SLet (Loc 7)
   (SLet (Loc 7)
    (SLet (Loc 7) SNothing
     (SLet (Loc 8) SNothing
      (SLet (Loc 9) SNothing
       (SApp False (UN "Prelude.Foldable.foldr") [Loc 7,Loc 8,Loc 9,Loc 4]))))
    (SLet (Loc 8)
     (SLet (Loc 8) SNothing
      (SLet (Loc 9) SNothing
       (SLet (Loc 10) SNothing
        (SLet (Loc 11)
         (SLet (Loc 11) SNothing
          (SLet (Loc 12) SNothing
           (SLet (Loc 13) SNothing
            (SCon Nothing 65678 (MN 2 "U_Prelude.Applicative.*>") [Loc 11,Loc 12,Loc 13,Loc 5]))))
         (SCon Nothing 65664 (MN 1 "U_Prelude.Basics..") [Loc 8,Loc 9,Loc 10,Loc 11,Loc 6])))))
     (SApp False (MN 0 "APPLY") [Loc 7,Loc 8])))
   (SLet (Loc 8)
    (SLet (Loc 8)
     (SLet (Loc 8) SNothing
      (SLet (Loc 9) SNothing
       (SApp False (UN "Prelude.Applicative.pure") [Loc 8,Loc 9,Loc 5])))
     (SLet (Loc 9) (SCon Nothing 0 (UN "MkUnit") [])
      (SApp False (MN 0 "APPLY") [Loc 8,Loc 9])))
    (SApp True (MN 0 "APPLY") [Loc 7,Loc 8])))

main15 = SFun (UN "Main.{main15}") [MN 1 "in"] 8
  (SLet (Loc 1) (SLet (Loc 1) SNothing
                 (SLet (Loc 2) SNothing
                  (SLet (Loc 3) SNothing
                   (SLet (Loc 4) SNothing
                    (SLet (Loc 5) (SCon Nothing 65638 (MN 1 "U_Main.{main4}") [])
                     (SLet (Loc 6) (SLet (Loc 6) (SCon Nothing 65642 (MN 1 "U_Main.{main8}") [])
                                    (SLet (Loc 7) (SCon Nothing 65628 (MN 1 "U_Main.{main10}") [])
                                     (SLet (Loc 8) (SCon Nothing 65632 (MN 1 "U_Main.{main14}") [])
                                      (SCon Nothing 0 (UN "constructor of Prelude.Applicative.Applicative") [Loc 6,Loc 7,Loc 8]))))
                      (SLet (Loc 7) (SCon Nothing 65626 (MN 1 "U_Main.testSubstr") [])
                       (SApp False (UN "Prelude.Traversable.traverse_") [Loc 1,Loc 2,Loc 3,Loc 4,Loc 5,Loc 6,Loc 7]))))))))
   (SLet (Loc 2) (SLet (Loc 2) (SLet (Loc 2) (SConst $ I 0)
                                (SLet (Loc 3) (SConst $ I 5)
                                 (SCon Nothing 0 (UN "Builtins.MkPair") [Loc 2,Loc 3])))
                  (SLet (Loc 3) (SCon Nothing 0 (UN "Prelude.List.Nil") [])
                   (SCon Nothing 1 (UN "Prelude.List.::") [Loc 2,Loc 3])))
    (SApp True (MN 0 "APPLY") [Loc 1,Loc 2])))

applicative' =
  SFun (UN "Prelude.Applicative.*>")[UN "e0", UN "e1", UN "e2", UN "e3", UN "e4", UN "e5"] 5
    (SLet (Loc 6)
      (SLet (Loc 6)
        (SLet (Loc 6) SNothing
          (SLet (Loc 7) SNothing
            (SLet (Loc 8) SNothing
              (SApp False (UN "Prelude.Applicative.<*>") [Loc 6,Loc 7,Loc 8,Loc 3]))))
        (SLet (Loc 7) (SLet (Loc 7)
                        (SLet (Loc 7)
                          (SLet (Loc 7) SNothing
                            (SLet (Loc 8) SNothing
                              (SLet (Loc 9) SNothing
                                (SLet (Loc 10)
                                  (SCase Shared (Loc 3)
                                    [SConCase 10 0 (UN "constructor of Prelude.Applicative.Applicative") [UN "in0", UN "in1", UN "in2"] (SV (Loc 10))])
                                  (SApp False (UN "Prelude.Functor.map") [Loc 7,Loc 8,Loc 9,Loc 10])))))
                        (SLet (Loc 8)
                          (SLet (Loc 8) SNothing (SLet (Loc 9) SNothing (SLet (Loc 10) (SLet (Loc 10) SNothing (SCon Nothing 65667 (UN "U_Prelude.Basics.id1") [Loc 10])) (SCon Nothing 65665 (UN "U_Prelude.Basics.const1") [Loc 8,Loc 9,Loc 10]))))
                          (SApp False (UN "APPLY0") [Loc 7,Loc 8])))
                      (SApp False (UN "APPLY0") [Loc 7,Loc 4]))
        (SApp False (UN "APPLY0") [Loc 6,Loc 7])))
    (SApp True (UN "APPLY0") [Loc 6,Loc 5]))

main0 = SFun (UN "Main.{main0}") [MN 4 "in",MN 5 "in",MN 6 "in"] 2
  (SLet (Loc 3) SNothing
   (SLet (Loc 4) SNothing
    -- (SApp True (UN "Prelude.Foldable.Prelude.List.List instance of Prelude.Foldable.Foldable, method foldr") [Loc 3,Loc 4,Loc 0,Loc 1,Loc 2])
    (SV $ Loc 4)
   ))

cheatedApply = SFun (MN 0 "APPLY") [MN 0 "fn",MN 0 "arg"] 6
  (SChkCase (Loc 0)
   [SConCase 2 65626 (UN "U_Main.testSubstr1") [] (SApp True (UN "Main.testSubstr") [Loc 1])
   ,SConCase 2 65627 (UN "U_Main.{main0}1") [MN 0 "P_c", MN 1 "P_c"] (SApp True (UN "Main.{main0}") [Loc 2,Loc 3,Loc 1])])

--prog = [main0, preludePutStr, toIntNat, substr, testSubstr, cheatedApply, applicativePure, foldableFoldr--, traverse_, main15
--       ]
prog = [[add], [add5], [doubles], [toIntNat], [substr], [preludePutStr]]

test = do
  let txps = inferProgram prog
  print "TExps:"
  print $ show txps

