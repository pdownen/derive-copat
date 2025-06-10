module Copattern.Block.Env.Step.Corridor where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = refocus (m :/: []) Nop

iter :: (Eq a, Eq i) => Decomp i a -> Answer i a
iter (Asked r q) = reduce r q

continue :: (Eq a, Eq i) => Followup i a -> Answer i a
continue (Next (Reduced m)     k) = refocus m k
continue (Next (Unknown x)     k) = Stuck x k
continue (Next Unhandled       k) = Raise k
continue (More lhs rhs ops env k) = Under lhs rhs ops env k

data Decomp i a
  = Asked (Redex i a) (ClosQuestion i a)
  deriving (Show)

refocus :: (Eq a, Eq i) => Closure i a -> ClosQuestion i a -> Answer i a
refocus (Var x :/: env)   k = case lookup x env of
  Nothing -> Stuck x k
  Just m  -> refocus m k
refocus (Dot m :/: env)   k = refocus (m :/: env) $ (m :/: env) :* k
refocus (Obj ops :/: env) k = reduce (Respond ops env) k
refocus (m :*: n :/: env) k = refocus (m :/: env) $ (n :/: env) :* k
refocus (m :@: i :/: env) k = refocus (m :/: env) $ i :@ k

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

reduce :: (Eq i, Eq a) => Redex i a -> ClosQuestion i a -> Answer i a
reduce (Introspect m env)                q = refocus (m :/: env) $ (m :/: env) :* q
reduce (FreeVar x env)                   q = case lookup x env of
  Nothing -> Stuck x q
  Just m  -> refocus m q
reduce (Respond (lhs :-> rhs : ops) env) q = comatch lhs q $ ComatchCxt [] (rhs, ops, env, q)
reduce (Respond [] env)                  q = Raise q

data CoMatchCxt i a
  = ComatchCxt { bind :: ClosEnv i a,
                 base :: (Term i a, [Option i a], ClosEnv i a, ClosQuestion i a) }

comatch :: (Eq a, Eq i)
        => Copattern i a -> ClosQuestion i a
        -> CoMatchCxt i a -> Answer i a
comatch Nop        cxt        k = refocus (rhs :/: env' ++ env) cxt
  where (ComatchCxt env' (rhs, _, env, _)) = k 
comatch lhs        Nop        k = Under lhs (rhs :/: env') ops env q
  where (ComatchCxt env' (rhs, ops, env, q)) = k
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ k{ bind = (x, y) : bind k }
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = reduce (Respond ops env) q
  where (ComatchCxt _    (_, ops, env, q)) = k
