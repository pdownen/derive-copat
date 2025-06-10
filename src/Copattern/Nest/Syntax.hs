{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module Copattern.Nest.Syntax where

data Response i a
  = Splat a
  | End
  | Term i a :!: Response i a
  deriving (Show, Functor)

data Term i a
  = Var a
  | Term i a :*: Term i a
  | Term i a :@: i
  | Dot (Term i a)
  | Option i a :?: Term i a
  | a :!-> Response i a
  | Raise
  deriving (Show, Functor)

data Option i a
  = a :*-> Option i a
  | i :@-> Option i a
  | a :?-> Term i a
  deriving (Show, Functor)

infixl 7 :*:
infixl 7 :@:

infixr 6 :*->
infixr 6 :@->
infixr 6 :?->
infixr 6 :!->

data Copattern i a
  = Nop
  | a :* Copattern i a
  | i :@ Copattern i a
  deriving (Show, Eq, Functor)

type Question i a = Copattern i (Term i a)

data Message i a = Msg { question :: Question i a,
                         punctuation :: Response i a }

infixr 7 :*
infixr 7 :@

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

send :: Term i a -> Message i a -> Response i a
send m d = (m `ask` question d) :!: punctuation d

type Env a b = [(a, b)]

data TRSub i a = TSub (Term i a) | RSub (Response i a)
  deriving (Show)

type TREnv i a = Env a (TRSub i a)

data ClosSub i a = CSub (Closure i a) | QSub (ClosQuestion i a)
  deriving (Show)

type ClosEnv i a = Env a (ClosSub i a)

data Closure i a = (:/:) { openTerm :: Term i a, staticEnv :: ClosEnv i a }
  deriving (Show)

type ClosQuestion i a = Copattern i (Closure i a)

lookupTerm :: Eq a => a -> TREnv i a -> Term i a
lookupTerm x env = case lookup x env of
  Just (TSub m) -> m
  _             -> Var x

lookupResponse :: Eq a => a -> TREnv i a -> Response i a
lookupResponse q env = case lookup q env of
  Just (RSub r) -> r
  _             -> Splat q

-- CAUTION: Capturing substitution!

-- Be sure that the free variables introduced by the replacements (terms or
-- term->response contexts) in the `TEnv i a` are different than the bound
-- variables of the expression (term, option, or response) we are performing
-- substitution on.  An easy way to meet this prerequisite is if `TermEnv i a`
-- only contains closed replacements.

(//) :: Eq a => Term i a -> TREnv i a -> Term i a
(Var x)    // e = lookupTerm x e
(m :*: n)  // e = (m // e) :*: (n // e)
(m :@: i)  // e = (m // e) :@: i
(Dot m)    // e = Dot (m // e)
(o :?: m)  // e = (o /?/ e) :?: (m // e)
(k :!-> r) // e = k :!-> (r /!/ e)
(Raise)    // e = Raise

(/?/) :: Eq a => Option i a -> TREnv i a -> Option i a
(x :*-> o) /?/ e = x :*-> (o /?/ e)
(i :@-> o) /?/ e = i :@-> (o /?/ e)
(x :?-> m) /?/ e = x :?-> (m // e)

(/!/) :: Eq a => Response i a -> TREnv i a -> Response i a
(Splat q) /!/ e = Raise :!: lookupResponse q e
(End)     /!/ e = End
(m :!: r) /!/ e = (m // e) :!: (r /!/ e)

{-
inlineClos :: Eq a => Closure i a -> Term i a
inlineClos (m :/: env) = m // inlineEnv env

inlineEnv :: Eq a => ClosEnv i a -> TermEnv i a
inlineEnv env = [ (x, inlineClos m) | (x, m) <- env ]
-}

infixl 2 //
-- infixl 2 :/:
