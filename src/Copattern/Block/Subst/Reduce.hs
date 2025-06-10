module Copattern.Block.Subst.Reduce where
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

fromReduct :: Reduct i a -> Term i a
fromReduct (Reduced m) = m
fromReduct Unhandled   = Obj []
fromReduct (Unknown x) = Var x

follow :: Followup i a -> Term i a
follow (Next r q)           = fromReduct r `ask` q
follow (More lhs rhs ops q) = Obj [lhs :-> rhs,
                                   Nop :-> (Obj ops `ask` q)]

reduce :: (Eq i, Eq a) => Redex i a -> Question i a -> Followup i a
reduce (Introspect m)                q = Next (Reduced $ m :*: m) q
reduce (FreeVar x)                   q = Next (Unknown x) q
reduce (Respond (lhs :-> rhs : ops)) q = case suffix match of
  Followup q'  -> Next (Reduced rhs') q'
  Unasked lhs' -> More lhs' rhs' ops q
  Mismatch _ _ -> reduce (Respond ops) q
  where match = comatch lhs q
        rhs'  = rhs // prefix match
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

comatch :: Eq i => Copattern i a -> Copattern i b -> CoMatch i a b
comatch Nop        cxt        = Comatch [] (Followup cxt)
comatch lhs        Nop        = Comatch [] (Unasked lhs)
comatch (x :* lhs) (y :* cxt) = Comatch ((x, y) : prefix q) (suffix q)
  where q = comatch lhs cxt
comatch (i :@ lhs) (j :@ cxt)
  | i == j                    = comatch lhs cxt
comatch lhs        cxt        = Comatch [] (Mismatch lhs cxt)
