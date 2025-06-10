module Copattern.Block.Env.Reduce where
import Copattern.Block.Syntax

data Redex i a
  = Introspect (Term i a) (ClosEnv i a)
  | Respond [Option i a] (ClosEnv i a)
  | FreeVar a (ClosEnv i a)
  deriving (Show)

reform :: Eq a => Redex i a -> Term i a
reform (Introspect m env) = Dot m // inlineEnv env
reform (Respond ops env)  = Obj ops // inlineEnv env
reform (FreeVar x env)    = Var x // inlineEnv env

data Reduct i a
  = Reduced (Closure i a)
  | Unhandled
  | Unknown a
  deriving (Show)

data Followup i a
  = Next (Reduct i a) (ClosQuestion i a)
  | More (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  deriving (Show)

fromReduct :: Eq a => Reduct i a -> Term i a
fromReduct (Reduced m) = inlineClos m
fromReduct Unhandled   = Obj []
fromReduct (Unknown x) = Var x

follow :: Eq a => Followup i a -> Term i a
follow (Next r q)               = fromReduct r `ask` fmap inlineClos q
follow (More lhs rhs ops env q) = Obj [lhs :-> (inlineClos rhs // env'),
                                       Nop :-> (m `ask` fmap inlineClos q)]
  where m    = Obj [ (q :-> (n // env')) | (q :-> n) <- ops ]
        env' = inlineEnv env

reduce :: (Eq i, Eq a) => Redex i a -> ClosQuestion i a -> Followup i a
reduce (Introspect m env)                q = Next (Reduced $ m :*: m :/: env) q
reduce (FreeVar x env)                   q = case lookup x env of
  Nothing -> Next (Unknown x) q
  Just m  -> Next (Reduced m) q
reduce (Respond (lhs :-> rhs : ops) env) q = case suffix match of
  Followup q'  -> Next (Reduced $ rhs :/: prefix match ++ env) q'
  Unasked lhs' -> More lhs' (rhs :/: prefix match) ops env q
  Mismatch _ _ -> reduce (Respond ops env) q
  where match = comatch lhs q
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
comatch (x :* lhs) (y :* cxt) = Comatch ((x, y) : prefix q) (suffix q)
  where q = comatch lhs cxt
comatch (i :@ lhs) (j :@ cxt)
  | i == j                    = comatch lhs cxt
comatch lhs        cxt        = Comatch [] (Mismatch lhs cxt)
