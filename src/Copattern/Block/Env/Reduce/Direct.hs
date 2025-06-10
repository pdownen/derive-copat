module Copattern.Block.Env.Reduce.Direct where
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
reduce (Respond (lhs :-> rhs : ops) env) q = case comatch lhs q of
  Comatch env' (Followup q')  -> Next (Reduced $ rhs :/: env' ++ env) q'
  Comatch env' (Unasked lhs') -> More lhs' (rhs :/: env') ops env q
  Comatch env' (Mismatch _ _) -> reduce (Respond ops env) q
reduce (Respond [] env)                  q = Next Unhandled q

data CoMatch i a b
  = Comatch { prefix :: Env a b,
              suffix :: Remainder i a b }
    deriving (Show)

data Remainder i a b
  = Followup (Copattern i b)
  | Unasked  (Copattern i a)
  | Mismatch (Copattern i a) (Copattern i b)
  deriving (Show)

comatch :: Eq i => Copattern i a -> Copattern i b -> CoMatch i a b
comatch Nop        cxt        = Comatch [] (Followup cxt)
comatch lhs        Nop        = Comatch [] (Unasked lhs)
comatch (x :* lhs) (y :* cxt) = case comatch lhs cxt of
  Comatch env rest -> Comatch ((x, y) : env) rest
comatch (i :@ lhs) (j :@ cxt)
  | i == j                    = case comatch lhs cxt of
      Comatch env rest -> Comatch env rest
comatch lhs        cxt        = Comatch [] (Mismatch lhs cxt)
