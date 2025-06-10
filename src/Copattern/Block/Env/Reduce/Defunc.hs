{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Env.Reduce.Defunc where
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
  | More (Copattern i a) (Closure i a) [Option i a] (ClosQuestion i a)
  deriving (Show)

reduce :: (Eq i, Eq a) => Redex i a -> ClosQuestion i a -> Followup i a
reduce (Introspect m env)                q = Next (Reduced $ m :*: m :/: env) q
reduce (FreeVar x env)                   q = case lookup x env of
  Nothing -> Next (Unknown x) q
  Just m  -> Next (Reduced m) q
reduce (Respond (lhs :-> rhs : ops) env) q = comatch lhs q $ OnMatch rhs ops env q
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

data CoMatchCxt i a
  = OnMatch (Term i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | BindArg (a, Closure i a) (CoMatchCxt i a)

comatch :: (Eq i, Eq a)
        => Copattern i a -> ClosQuestion i a
        -> CoMatchCxt i a -> Followup i a
comatch Nop        cxt        k = found k $ Comatch [] (Followup cxt)
comatch lhs        Nop        k = found k $ Comatch [] (Unasked lhs)
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ BindArg (x, y) k
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = found k $ Comatch [] (Mismatch lhs cxt)

found :: (Eq i, Eq a)
      => CoMatchCxt i a
      -> CoMatch i a (Closure i a) -> Followup i a
found (OnMatch rhs ops env q) = \case
  Comatch env' (Followup q')   -> Next (Reduced $ rhs :/: env') q'
  Comatch env' (Unasked  lhs') -> More lhs' (rhs :/: env') ops q
  Comatch env' (Mismatch _ _)  -> reduce (Respond ops env) q
found (BindArg bind k)    = \case
  Comatch env' rest -> found k $ Comatch (bind : env') rest
