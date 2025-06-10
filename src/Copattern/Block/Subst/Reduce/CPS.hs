{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Reduce.CPS where
import Copattern.Block.Syntax

data Redex i a
  = Introspect (Term i a)
  | Respond [Option i a]
  | FreeVar a
  deriving (Show)

reform :: Redex i a -> Term i a
reform (Introspect m) = Dot m
reform (Respond ops)  = Obj ops
reform (FreeVar x)    = Var x

data Reduct i a
  = Reduced (Term i a)
  | Unhandled
  | Unknown a
  deriving (Show)

data Followup i a
  = Next (Reduct i a) (Question i a)
  | More (Copattern i a) (Term i a) [Option i a] (Question i a)
  deriving (Show)

reduce :: (Eq i, Eq a) => Redex i a -> Question i a -> Followup i a
reduce (Introspect m)                q = Next (Reduced $ m :*: m) q
reduce (FreeVar x)                   q = Next (Unknown x) q
reduce (Respond (lhs :-> rhs : ops)) q = comatch lhs q $ \case
  Comatch env (Followup q')  -> Next (Reduced $ rhs // env) q'
  Comatch env (Unasked lhs') -> More lhs' (rhs // env) ops q
  Comatch env (Mismatch _ _) -> reduce (Respond ops) q
reduce (Respond [])                  q = Next Unhandled q

data CoMatch i a b
  = Comatch { prefix :: Env a b,
              suffix :: Remainder i a b }
    deriving (Show)

data Remainder i a b
  = Followup (Copattern i b)
  | Unasked  (Copattern i a)
  | Mismatch (Copattern i a) (Copattern i b)
  deriving (Show)

comatch :: Eq i
        => Copattern i a -> Copattern i b
        -> (CoMatch i a b -> r) -> r
comatch Nop        cxt        k = k $ Comatch [] (Followup cxt)
comatch lhs        Nop        k = k $ Comatch [] (Unasked lhs)
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ \case
  Comatch env rest -> k $ Comatch ((x, y) : env) rest
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = k $ Comatch [] (Mismatch lhs cxt)
