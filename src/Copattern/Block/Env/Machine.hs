module Copattern.Block.Env.Machine where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = refocus m [] Nop

refocus :: (Eq a, Eq i)
        => Term i a -> ClosEnv i a -> ClosQuestion i a
        -> Answer i a
refocus (Var x)   env k = case lookup x env of
  Nothing -> Stuck x k
  Just (m :/: env)  -> refocus m env k
refocus (Dot m)   env k = refocus m env $ (m :/: env) :* k
refocus (Obj os) env k = case os of
  lhs :-> rhs : os -> comatch lhs k [] rhs os env k
  []               -> Raise k
refocus (m :*: n) env k = refocus m env $ (n :/: env) :* k
refocus (m :@: i) env k = refocus m env $ i :@ k

comatch :: (Eq a, Eq i)
        => Copattern i a -> ClosQuestion i a
        -> ClosEnv i a -> Term i a -> [Option i a] -> ClosEnv i a -> ClosQuestion i a
        -> Answer i a
comatch Nop        cxt        env' rhs _   env _ = refocus rhs (env' ++ env) cxt
comatch lhs        Nop        env' rhs os env q = Under lhs (rhs :/: env') os env q
comatch (x :* lhs) (y :* cxt) env' rhs os env q = comatch lhs cxt ((x,y):env') rhs os env q
comatch (i :@ lhs) (j :@ cxt) env' rhs os env q
  | i == j                                      = comatch lhs cxt env' rhs os env q
comatch lhs        cxt        _    _   os env q = refocus (Obj os) env q
