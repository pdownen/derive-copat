module Copattern.Block.Env.Step.Deforest where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

-- inline `Closure i a` on call sites

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = refocus m [] Nop

-- `iter` is no longer used

-- `continue` is no longer used

-- `Decomp` is no longer used

-- `refocus (Obj ops)` now subsumes `reduce (Respond ops)` by matching on `ops`

-- rewrite: `refocus (m :/: env)` --> `refocus m env`

refocus :: (Eq a, Eq i)
        => Term i a -> ClosEnv i a -> ClosQuestion i a
        -> Answer i a
refocus (Var x)   env k = case lookup x env of
  Nothing -> Stuck x k
  Just (m :/: env)  -> refocus m env k
refocus (Dot m)   env k = refocus m env $ (m :/: env) :* k
refocus (Obj ops) env k = case ops of
  lhs :-> rhs : ops' -> comatch lhs k [] rhs ops env k
  []                 -> Raise k
refocus (m :*: n) env k = refocus m env $ (n :/: env) :* k
refocus (m :@: i) env k = refocus m env $ i :@ k

-- `Redex i a` is no longer used

-- `Reduct i a` is no longer used

-- `Followup i a` is no longer used

-- only the `Respond` case of `reduce` is accessible.
-- rewrite: `reduce (Respond ops)` --> `refocus (Obj ops)`

-- inline `ComatchCxt bind base` on call sites

comatch :: (Eq a, Eq i)
        => Copattern i a -> ClosQuestion i a
        -> ClosEnv i a -> Term i a -> [Option i a] -> ClosEnv i a -> ClosQuestion i a
        -> Answer i a
comatch Nop        cxt        env' rhs _   env _ = refocus rhs (env' ++ env) cxt
comatch lhs        Nop        env' rhs ops env q = Under lhs (rhs :/: env') ops env q
comatch (x :* lhs) (y :* cxt) env' rhs ops env q = comatch lhs cxt ((x,y):env') rhs ops env q
comatch (i :@ lhs) (j :@ cxt) env' rhs ops env q
  | i == j                                       = comatch lhs cxt env' rhs ops env q
comatch lhs        cxt        _    _   ops env q = refocus (Obj ops) env q
