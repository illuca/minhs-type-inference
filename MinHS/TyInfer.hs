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
import Debug.Trace


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
-- SKIP-TM: skip term
unify (g1 :< TermVar id scheme) (FlexVar t1) (FlexVar t2) = do
  g2 <- unify g1 (FlexVar t1) (FlexVar t2)
  return (g2 :< TermVar id scheme)

-- SUBST: substitution if p is defined
unify (g1 :< (:=) p (Defn t)) (FlexVar a) (FlexVar b) = do
  let subs = S.fromList [(p,t)]
      aS = S.substFlex subs (getType (g1 :< (:=) p (Defn t)) a)
      bS = S.substFlex subs (getType (g1 :< (:=) p (Defn t)) b)
  g2 <- unify g1 aS bS
  return (g2 :< (:=) p (Defn t))

unify (g1 :< (:=) p HOLE) (FlexVar a) (FlexVar b)
  -- REFL: reflection
  | a == b = return (g1 :< (:=) p HOLE)
  -- SKIP-TY: Skip if p does not occur in the problem
  | p /= a && p /= b = do
      g2 <- unify g1 (FlexVar a) (FlexVar b)
      return (g2 :< (:=) p HOLE)
  -- DEFN: definition 1
  | p == a && p /= b = do
      return (g1 :< (:=) p (Defn $ FlexVar b))
  -- DEFN: definition 2
  | p /= a && p == b = do
      return (g1 :< (:=) p (Defn $ FlexVar a))
  | otherwise = error $ "\ng1: " ++ show (g1 :< (:=) p HOLE)
                  ++ "\n" ++ show (FlexVar a)
                  ++ "\n" ++ show (FlexVar b)

-- two base type
unify g1 (Base _) (Base _) =
  return g1
-- two rigid type
unify g1 (RigidVar _) (RigidVar _) =
  return g1
unify g1 (RigidVar t1) t2 = do
  inst g1 [] t1 t2
unify g1 t1 (RigidVar t2) = do
  inst g1 [] t2 t1

-- Instantiation: tau is not a flexvar
unify g1 (FlexVar a) tau = inst g1 [] a tau

unify g1 tau (FlexVar a) = inst g1 [] a tau

-- product
unify g1 (Prod a b) (Prod a' b') = do
  g2 <- unify g1 a a'
  g3 <- unify g2 b b'
  return g3

-- ARROW
unify g1 (Arrow a b) (Arrow a' b') = do
  g2 <- unify g1 a a'
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
-- SKIP-TM
inst (g1 :< TermVar x sigma) suffix a tau = do
  g2 <- inst g1 suffix a tau
  return (g2 :< TermVar x sigma)
inst (g1 :< Mark) suffix a tau = do
  g2 <- inst g1 suffix a tau
  return (g2 :< Mark)

inst (g1 :< (:=) b (Defn tau')) suffix a tau = do 
  let subs = S.fromList [(b,tau')]
      aS = S.substFlex subs (getType g1' a)
      tS = S.substFlex subs tau
  g2 <- unify (extend g1 suffix) aS tS
  return (g2 :< (:=) b (Defn tau'))
  where g1' = g1 :< (:=) b (Defn tau')

inst (g1 :< (:=) b HOLE) suffix a tau
  -- DEFN 
  | b == a && notMember a (ffv tau) = do
     return (extend g1 suffix :< (:=) a (Defn tau))
  -- DEPEND
  | b /= a && member b (ffv tau) = do
     inst g1 ((b, HOLE):suffix) a tau
  -- SKIP-TY
  | b /= a && notMember b (ffv tau) = do
      g2 <- inst g1 suffix a tau
      return (g2 :< (:=) b HOLE) 


inst g1 suffix a t = error $ "\nΓ: " ++ show g1
                          ++ "\nsuffix: " ++ show suffix
                          ++ "\na: " ++ show a
                          ++ "\nt: " ++ show t

inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g1 (SBind x _ e) = do
  (scheme, g2) <- generalize g1 e
  return (SBind x (Just scheme) e, g2)

inferProgram g1 program = error $
     "\ng1: " ++ show g1 ++
     "\nprogram: " ++ show program


inferExp :: Gamma -> Exp -> TC (Type, Gamma)

-- VAR
inferExp g (Var x)
  | isScheme g x =  do
      let (Forall ps tau) = getScheme g x
      pqs <- freshForall ps
      let subs = S.fromList $ map (\pq -> (fst pq, FlexVar $ snd pq)) pqs
          tau' = S.substRigid subs tau
          qSuffix = map (\pq -> (snd pq, HOLE)) pqs
      return (tau',extend g qSuffix)
  | isType g x = do
      let tau = getType g x
      return (tau, g)
  | otherwise = error $ "cannot find entry for: " ++ show x


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
inferExp g1 (App e1 e2) = do
    (ty1, g2) <- inferExp g1 e1
    (ty2, g3) <- inferExp g2 e2
    (p, g3') <-  introduce g3
    g4 <- unify g3' ty1 (Arrow ty2 $ FlexVar p)
    if isType g4 p
    then let tau = getType g4 p
         in return (tau, g4)
    else return (FlexVar p, g4)

-- IF-THEN-ELSE
inferExp g1 (If e et ef) = do
  (tau, g2) <- inferExp g1 e
  g3 <- unify g2 tau (Base Bool)
  (tauT, g4) <- inferExp g3 et
  (tauF, g5) <- inferExp g4 ef
  g6 <- unify g5 tauT tauF
  return (tauT, g6)

-- CASE
--inferExp g1 (Case e [(Alt _ [x] e1), Alt _ [y] e2]) = do
--  (tau, g2) <- e
--  a <- freshId
--  b <- freshId
--  g3 <- unify (g2 :< (:=) a HOLE :< (:=) b HOLE) 
--              tau 
--              (Sum (Flex a) (Flex b))
--  (tau1, g4tmp) <- inferExp (g3 :< TermVar x (Flex a)) e1
--  
--  return (tau1, g6)  

-- RECFUN
inferExp g1 (Recfun (MBind f x e)) = do
  a <- freshId
  b <- freshId
  (tau,gtmp) <- inferExp
                  (g1 :< (:=) a HOLE
                      :< (:=) b HOLE
                      :< (:=) x (Defn (FlexVar a))
                      :< (:=) f (Defn (FlexVar b)))
                  e
  let g2 :< (:=) x (Defn aF) = dropWhilst notX gtmp
      bF = getType gtmp f
      suffix = takeSuffix notF gtmp
  g3 <- unify (extend g2 suffix) bF (Arrow aF tau)
  return (bF, g3)
  where
    notF = not . isF
    isF ((:=) f' _) = f == f'
    isF _ = False

    notX = not . isX
    isX ((:=) x' _) = x == x'
    isX _ = False

-- Let
inferExp g1 (Let [SBind x _ e1] e2) = do
   (sigma, g2) <- generalize g1 e1
   (tau,gtmp) <- inferExp (g2:< TermVar x sigma) e2
   let  suffix = takeSuffix notX gtmp
        (g3 :< TermVar _ _) = dropWhilst notX gtmp
   return (tau, extend g3 suffix)
   where
     notX = not . isX
     isX (TermVar x' scheme) = x == x'
     isX _ = False


inferExp g e = error $ show e

-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives

xx :: Gamma -> Id -> Gamma
g `xx` id = g :< (:=) id HOLE

-- GEN
generalize :: Gamma -> Exp -> TC (Scheme, Gamma)
generalize g1 e = do
  (tau, g2) <- inferExp (g1 :< Mark) e
  let suffix = reverse $ takeSuffix notMark g2
  scheme <- gen suffix tau []
  return (scheme, g2)
  where
    notMark = not . isMark
    isMark Mark = True
    isMark _ = False

-- gen
gen :: Suffix -> Type -> Suffix -> TC Scheme
gen [] tau s2 = return (mono tau)

gen ((a,Defn tau'):s1) tau s2 = do
  let subst = S.fromList [(a,tau')]
      resT = S.substFlex subst tau
  gen s1 resT s2

gen ((id, HOLE):s1) tau s2 = do
  let subst = S.fromList [(id, RigidVar id)]
      resT = S.substFlex subst tau
  gen s1 resT ((id, HOLE):s2)

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


takeSuffix :: (Entry -> Bool) -> Bwd Entry -> Suffix
takeSuffix f g = toSuffix $ takeWhilst f g

toSuffix :: Gamma -> Suffix
toSuffix BEmpty = []
toSuffix (xs :< x) =
  case x of
    (:=) id decl -> (toSuffix xs) ++ [(id,decl)]
    _ -> toSuffix xs

isType :: Gamma -> Id -> Bool
isType BEmpty id = False
isType (xs :< x) id =
    case x of
      (:=) id' (Defn t) -> if id == id' then True else isType xs id
      (:=) id' HOLE -> if id == id' then True else isType xs id
      _ -> isType xs id
getType :: Gamma -> Id -> Type
getType BEmpty id = error $ "cannot find type for " ++ show id
getType (xs :< x) id =
  case x of
    (:=) id' (Defn t) -> if id == id' then t else getType xs id
    (:=) id' HOLE -> if id == id' then FlexVar id else getType xs id
    _ -> getType xs id

isScheme :: Gamma -> Id -> Bool
isScheme BEmpty id = False
isScheme (xs :< x) id =
  case x of
    TermVar id' scheme -> if id == id' then True else isScheme xs id
    _ -> isScheme xs id


getScheme :: Gamma -> Id -> Scheme
getScheme BEmpty id = error $ "cannot find scheme for " ++ show id
getScheme (xs :< x) id =
  case x of
    TermVar id' scheme -> if id == id' then scheme else getScheme xs id
--    (:=) id' (Defn t) -> if id == id' then mono t else getScheme xs id
    _ -> getScheme xs id

ppType :: Type -> String
ppType (Arrow t1 t2) = ppType t1 ++ " -> " ++ ppType t2
ppType (Sum t1 t2) = "(" ++ ppType t1 ++ " + " ++ ppType t2 ++ ")"
ppType (Prod t1 t2) = ppType t1 ++ " * " ++ ppType t2
ppType (Base Unit) = "()"
ppType (Base t) = show t
ppType (FlexVar id) = id
ppType (RigidVar id) = id ++ "R"
ppT = removeQuotes . ppType

ppBwdEntry :: Entry -> String
ppBwdEntry (TermVar id scheme) = "TermVar " ++ id ++ " " ++ show scheme
ppBwdEntry ((:=) id HOLE) = id
ppBwdEntry ((:=) id (Defn t)) = id ++ ": " ++ ppType t
ppBwdEntry Mark = "Mark"

ppBwd :: Show a => Bwd a -> String
ppBwd BEmpty = "$"
ppBwd (xs :< x) = ppBwd xs ++ show x ++ ", "

ppSchemeEntry :: (Id,Decl) -> String
ppSchemeEntry (id, HOLE) = id
ppSchemeEntry (id, Defn t) = id ++ ": " ++ ppType t

ppScheme :: Show a => [a]-> String
ppScheme [] = ""
ppScheme (x:xs) = show x ++ ", " ++ ppScheme xs

ppS :: Suffix -> String
ppS suffix = "Δ: " ++ (removeQuotes . ppScheme . fmap ppSchemeEntry) suffix

ppG :: Gamma -> String
ppG g = "Γ: " ++ (removeQuotes . ppBwd . fmap ppBwdEntry) g

removeQuotes :: String -> String
removeQuotes = filter (`notElem` ['"', '\'', '1'])


dot x = trace x (return ())