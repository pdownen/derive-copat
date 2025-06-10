module Copattern.Block.Env.Reduce.Corridor where
import Copattern.Block.Syntax

data Redex i a
  = Introspect (Term i a) (ClosEnv i a)
  | Respond [Option i a] (ClosEnv i a)
  | FreeVar a (ClosEnv i a)
  deriving (Show)

data Reduct i a
  = Reduced (Closure i a)
  | Unhandled
  | Unknown a
  deriving (Show)

data Followup i a
  = Next (Reduct i a) (ClosQuestion i a)
  | More (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  deriving (Show)

reduce :: (Eq i, Eq a) => Redex i a -> ClosQuestion i a -> Followup i a
reduce (Introspect m env)                q = Next (Reduced $ m :*: m :/: env) q
reduce (FreeVar x env)                   q = case lookup x env of
  Nothing -> Next (Unknown x) q
  Just m  -> Next (Reduced m) q
reduce (Respond (lhs :-> rhs : ops) env) q = comatch lhs q  $ ComatchCxt [] (rhs, ops, env, q)
reduce (Respond [] env)                  q = Next Unhandled q

data CoMatchCxt i a
  = ComatchCxt { bind :: ClosEnv i a,
                 base :: (Term i a, [Option i a], ClosEnv i a, ClosQuestion i a) }

comatch :: (Eq a, Eq i)
        => Copattern i a -> ClosQuestion i a
        -> CoMatchCxt i a -> Followup i a
comatch Nop        cxt        k = Next (Reduced $ rhs :/: env' ++ env) cxt
  where (ComatchCxt env' (rhs, _, env, _)) = k 
comatch lhs        Nop        k = More lhs (rhs :/: env') ops env q
  where (ComatchCxt env' (rhs, ops, env, q)) = k
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ k{ bind = (x, y) : bind k }
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = reduce (Respond ops env) q
  where (ComatchCxt _    (_, ops, env, q)) = k
