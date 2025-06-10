{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module Copattern.Block.Syntax where

data Term i a
  = Var a
  | Term i a :*: Term i a
  | Term i a :@: i
  | Dot (Term i a)
  | Obj [Option i a]
  deriving (Show, Functor)

infixl 7 :*:
infixl 7 :@:

data Option i a = Copattern i a :-> Term i a
  deriving (Show, Functor)

data Copattern i a
  = Nop
  | a :* Copattern i a
  | i :@ Copattern i a
  deriving (Show, Eq, Functor)

infixr 7 :*
infixr 7 :@

type Question i a = Copattern i (Term i a)

type ClosQuestion i a = Copattern i (Closure i a)

instance Semigroup (Copattern i a) where
  Nop      <> q' = q'
  (x :* q) <> q' = x :* (q <> q')
  (i :@ q) <> q' = i :@ (q <> q')

instance Monoid (Copattern i a) where
  mempty = Nop

extract :: Copattern i a -> [a]
extract Nop      = []
extract (x :* q) = x : extract q
extract (i :@ q) = extract q

ask :: Term i a -> Question i a -> Term i a
ask m Nop      = m
ask m (n :* q) = ask (m :*: n) q
ask m (i :@ q) = ask (m :@: i) q

type Env a b = [(a, b)]

type TermEnv i a = Env a (Term i a)

type ClosEnv i a = Env a (Closure i a)

data Closure i a = (:/:) { openTerm :: Term i a, staticEnv :: ClosEnv i a }
  deriving (Show)

lookupTerm :: Eq a => a -> TermEnv i a -> Term i a
lookupTerm x env = case lookup x env of
  Just m  -> m
  Nothing -> Var x

-- CAUTION: Capturing substitution!

-- Be sure that the free variables introduced by the replacement terms in the
-- `TermEnv i a` are different than the bound variables of the term we are
-- performing substitution on.  An easy way to meet this prerequisite is if the
-- `TermEnv i a` only contains closed term replacements.

(//) :: Eq a => Term i a -> TermEnv i a -> Term i a
(Var x)   // e = lookupTerm x e
(m :*: n) // e = (m // e) :*: (n // e)
(m :@: i) // e = (m // e) :@: i
(Obj ops) // e = Obj [ q :-> (n // e) | q :-> n <- ops ]
(Dot m)   // e = Dot (m // e)

inlineClos :: Eq a => Closure i a -> Term i a
inlineClos (m :/: env) = m // inlineEnv env

inlineEnv :: Eq a => ClosEnv i a -> TermEnv i a
inlineEnv env = [ (x, inlineClos m) | (x, m) <- env ]

infixl 2 //
infixl 2 :/:
