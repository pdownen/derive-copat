module Copattern.Block.Env.Machine.Shallow where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m [] Nop

-- rewrite: `refocus (Obj ops)` --> `select ops`

refocus :: (Eq i, Eq a)
        => Term i a -> ClosEnv i a -> ClosQuestion i a
        -> Answer i a
refocus (Var x)   env k = case lookup x env of
  Nothing -> Stuck x k
  Just (m :/: env)  -> refocus m env k
refocus (Dot m)   env k = refocus m env $ (m :/: env) :* k
refocus (Obj ops) env k = select ops env k
refocus (m :*: n) env k = refocus m env $ (n :/: env) :* k
refocus (m :@: i) env k = refocus m env $ i :@ k

select :: (Eq i, Eq a)
       => [Option i a] -> ClosEnv i a -> ClosQuestion i a
       -> Answer i a
select []         env q = Raise q
select (op : ops) env q = option op ops env q

option :: (Eq i, Eq a)
       => Option i a -> [Option i a] -> ClosEnv i a -> ClosQuestion i a
       -> Answer i a
option (lhs :-> rhs) ops env q = comatch lhs q [] rhs ops env q

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
