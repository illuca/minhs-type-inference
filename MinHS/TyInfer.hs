module MinHS.TyInfer where

import MinHS.Bwd
import MinHS.Syntax
import qualified MinHS.Subst as S (Subst, SubstSem, substFlex, substRigid, fromList)
import MinHS.TCMonad

import Control.Monad (foldM)
import Data.List (delete)
import Data.Set (Set, notMember, fromList, difference, member, toList)
import Data.Bifunctor (Bifunctor(..), second)
import MinHS.Subst ((=:))

-- | A monomorphic type injected into a type scheme with no quantified
-- type variables.
mono :: Type -> Scheme
mono t = Forall [] t

primOpType :: Op -> Scheme
primOpType Gt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = mono $ Base Int `Arrow` Base Int
primOpType Fst  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "a"
primOpType Snd  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "b"
primOpType _    = mono $ Base Int `Arrow` (Base Int `Arrow` Base Int)

conType :: Id -> Maybe Scheme
conType "True"  = Just $ mono $ Base Bool
conType "False" = Just $ mono $ Base Bool
conType "()"    = Just $ mono $ Base Unit
conType "Pair"  = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "b" `Arrow` (RigidVar "a" `Prod` RigidVar "b"))
conType "Inl"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType "Inr"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "b" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType _       = Nothing

freshForall :: [Id] -> TC [(Id,Id)]
freshForall xs = mapM (\x -> (,) <$> pure x <*> freshId) xs

-- | Produce fresh flexible variables for a type scheme
specialise :: Scheme -> TC (Type, Suffix)
specialise (Forall xs t) =
  do ids <- freshForall xs
     return (S.substRigid (S.fromList (map (second FlexVar) ids)) t
            , map (flip (,) HOLE . snd) ids)

-- | Extend a typing context with a collection of flexible declarations
extend :: Gamma -> Suffix -> Gamma
extend g [] = g
extend g ((v,d) : ds) = extend (g :< v := d) ds

--infer :: Program -> Either TypeError (Program, Gamma)
infer program = runTC $ inferProgram BEmpty program

-- | Perform unification of the given types
unify :: Gamma -> Type -> Type -> TC Gamma

-- SKIP-MARK
unify (g1 :< Mark) (FlexVar t1) (FlexVar t2) = unify g1 (FlexVar t1) (FlexVar t2)
-- SKIP-TM
unify (g1 :< TermVar id scheme) (FlexVar t1) (FlexVar t2) = do
  g2 <- unify g1 (FlexVar t1) (FlexVar t2)
  return (g2 :< TermVar id scheme)

unify (g1 :< (:=) p decl) (FlexVar a) (FlexVar b)
  -- REFL
  | a == b = return g1'
  -- SKIP-TY
  | p /= a && p /= b = do
      g2 <- unify g1 (FlexVar a) (FlexVar b)
      return g1'
  -- DEFN
  | p == a && p /= b = do
      return (g1 :< (:=) p (Defn $ FlexVar b))
  | otherwise = case decl of
        Defn t -> do
            let subs = S.fromList [(p,t)]
                aS = S.substFlex subs (getType g1' a)
                bS = S.substFlex subs (getType g1' b)
            g2 <- unify g1 aS bS
            return (g2 :< (:=) p decl)
        _ -> error $ "\ng1: " ++ show g1'
                  ++ "\n" ++ show (FlexVar a)
                  ++ "\n" ++ show (FlexVar b)
  where g1' = g1 :< (:=) p decl

-- INST
unify g1 (FlexVar t1) t2 = inst g1 [] t1 t2

unify g1 t1 (FlexVar t2) = inst g1 [] t2 t1

-- my-PROD

-- ARROW
unify g1 (Arrow a b) (Arrow a' b') =
  do  g2 <- unify g1 a a'
      g3 <- unify g2 b b'
      return g3

--unify g1 a (Arrow a' _) = unify g1 a a'
--unify g1 (Arrow a b) a' = unify g1 a a'

unify g t1 t2
  | t1 == t2 = return g
  | otherwise =
      error $ show g
        ++ "\nt1:" ++ show t1
        ++ "\nt2:" ++ show t2

-- | Instantiation the type variable a with the type t
inst :: Gamma -> Suffix -> Id -> Type -> TC Gamma

inst (g1 :< (:=) b bDecl) suffix a t
  -- DEFN
  | b == a && notMember a (ffv t) =
      return (extend g1 suffix :< (:=) a (Defn t))
  -- DEPEND
  | b /= a && member b (ffv t) =
      inst g1 ((b, bDecl):suffix) a t
  -- SKIP-TY
  | b /= a && notMember b (ffv t) = do
      g2 <- inst g1 suffix a t
      return (g2 :< (:=) b bDecl)
  -- SUBST
  | otherwise = case bDecl of
        Defn t' ->  do
              let subs = S.fromList [(b,t')]
                  aS = S.substFlex subs (getType g1' a)
                  tS = S.substFlex subs t
              g2 <- unify (extend g1 suffix) aS tS
              return (g2 :< (:=) b bDecl)
        _ ->  error $ "\nΓ: " ++ show g1'
                    ++ "\nb: " ++ show b
                    ++ "\nsuffix: " ++ show suffix
                    ++ "\na: " ++ show a
                    ++ "\nt: " ++ show t
    where g1' = g1 :< (:=) b bDecl

inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g1 (SBind x _ e) = do
  (scheme, g2) <- generalize g1 e
  return (SBind x (Just scheme) e, g2)

inferProgram g1 program = error $
     "\ng1: " ++ show g1 ++
     "\nprogram: " ++ show program


inferExp :: Gamma -> Exp -> TC (Type, Gamma)

-- VAR
inferExp g (Var x) = do
  let (Forall ps tau) = getScheme g x
  pqs <- freshForall ps
  let subs = S.fromList $ map (\pq -> (fst pq, FlexVar $ snd pq)) pqs
      tau' = S.substRigid subs tau
      qSuffix = map (\pq -> (snd pq, HOLE)) pqs
  return (tau',extend g qSuffix)


-- INT
inferExp g (Num _) = return (Base Int, g)

-- CON
-- ConType for True,False,(),Pair,Inl,Inr
inferExp g (Con c) =
  case conType c of
    Just scheme -> do
      (t, suffix) <- specialise scheme
      return (t, extend g suffix)
-- PRIM
-- prim operations for Ge,Ge,Lt,Le,Eq,Ne,Neg,Fst,Snd
inferExp g (Prim op) = do
  (t, suffix) <- specialise (primOpType op)
  return (t, extend g suffix)

-- APP
inferExp g1 (App e1 e2) =
  do
    (ty1, g2) <- inferExp g1 e1
    (ty2, g3) <- inferExp g2 e2
    (p, g3') <-  introduce g3
    g4 <- unify g3' ty1 (Arrow ty2 $ FlexVar p)
    t <- lastFlex g4
--    let subs = S.fromList $ tolist g4
--        t' = S.substFlex subs t
    return (t, g4)

-- Let
inferExp g1 (Let [SBind x _ e1] e2) = do
   (sigma, g2) <- generalize g1 e1
   (tau,gtmp) <- inferExp (g2:< TermVar x sigma) e2
   let  suffix = tosuffix $ takeWhilst notX gtmp
--   error $ show $ dropWhilst notX gtmp
        (g3 :< TermVar _ _) = dropWhilst notX gtmp 
   return (tau, extend g3 suffix)
   where
     notX = not . isX
     isX (TermVar x' scheme) = x == x'
     isX _ = False

--inferExp g1 (Let e1 e2) = do

inferExp g e = error $ show e

-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives

-- GEN
generalize :: Gamma -> Exp -> TC (Scheme, Gamma)
generalize g1 e = do
  (tau, g2) <- inferExp (g1 :< Mark) e
  let bwd = takeWhilst notMark g2
      suffix = reverse $ tosuffix bwd
  scheme <- gen suffix tau []
  return (scheme, g2)
  where
    notMark = not . isMark
    isMark Mark = True
    isMark _ = False

-- gen
gen :: Suffix -> Type -> Suffix -> TC Scheme
gen [] tau s2 = return (mono tau)

gen ((id,Defn idT):s1) tau s2 = do
  let subst = S.fromList [(id,idT)]
      tau' = S.substFlex subst tau
  gen s1 tau' s2

gen ((id, HOLE):s1) tau s2 = do
  let subst = S.fromList [(id, RigidVar id)]
      tau' = S.substFlex subst tau
  gen s1 tau' ((id, HOLE):s2)

introduce :: Gamma -> TC (Id, Gamma)
introduce g =
  do id <- freshId
     return (id, g :< (:=) id HOLE)


lastFlex :: Gamma -> TC Type
lastFlex g =
  case g of
    xs :< (:=) id (Defn t) -> return t
    _ -> error $ show g

-- | Perform unification of the given types
notFlexVar :: Type -> Bool
notFlexVar = not . isFlexVar

isFlexVar :: Type -> Bool
isFlexVar (FlexVar _) = True
isFlexVar _ = False

tosuffix :: Gamma -> Suffix
tosuffix BEmpty = []
tosuffix (xs :< x) =
  case x of
    (:=) id decl -> (id,decl) : tosuffix xs
    _ -> tosuffix xs

tolist :: Gamma -> [(Id,Type)]
tolist BEmpty = []
tolist (xs :< x) =
  case x of
    (:=) id (Defn t) -> (id,t) : tolist xs
    _ -> tolist xs

getType :: Gamma -> Id -> Type
getType BEmpty id = error $ "cannot find type for " ++ show id
getType (xs :< x) id =
  case x of
    (:=) id' (Defn t) -> if id == id' then t else getType xs id
    _ -> getType xs id

getScheme :: Gamma -> Id -> Scheme
getScheme BEmpty id = error $ "cannot find scheme for " ++ show id
getScheme (xs :< x) id =
  case x of
    TermVar id' scheme -> if id == id' then scheme else getScheme xs id
    _ -> getScheme xs id