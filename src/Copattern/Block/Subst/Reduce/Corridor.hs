{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Reduce.Corridor where
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
reduce (Respond (lhs :-> rhs : ops)) q = comatch lhs q $ ComatchCxt [] (rhs, ops, q)
reduce (Respond [])                  q = Next Unhandled q

data CoMatchCxt i a
  = ComatchCxt { bind :: TermEnv i a,
                 base :: (Term i a, [Option i a], Question i a) }

comatch :: (Eq a, Eq i)
        => Copattern i a -> Question i a
        -> CoMatchCxt i a -> Followup i a
comatch Nop        cxt        k = Next (Reduced $ rhs // env) cxt
  where (ComatchCxt env (rhs, _, _)) = k 
comatch lhs        Nop        k = More lhs (rhs // env) ops q
  where (ComatchCxt env (rhs, ops, q)) = k
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ k{ bind = (x,y) : bind k }
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = reduce (Respond ops) q
  where (ComatchCxt _   (_, ops, q)) = k
