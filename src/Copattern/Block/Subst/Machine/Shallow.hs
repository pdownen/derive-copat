module Copattern.Block.Subst.Machine.Shallow where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

-- rewrite: `refocus (Obj ops)` --> `select ops`

refocus :: (Eq i, Eq a)
        => Term i a -> Question i a
        -> Answer i a
refocus (Var x)   k = Stuck x k
refocus (Dot m)   k = refocus m $ m :* k
refocus (Obj ops) k = select ops k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k

select :: (Eq i, Eq a) => [Option i a] -> Question i a -> Answer i a
select []         q = Raise q
select (op : ops) q = option op ops q

option :: (Eq i, Eq a) => Option i a -> [Option i a] -> Question i a -> Answer i a
option (lhs :-> rhs) ops q = comatch lhs q rhs ops q

comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> Term i a -> [Option i a] -> Question i a
        -> Answer i a
comatch Nop         cxt       rhs _   _ = refocus rhs cxt
comatch lhs         Nop       rhs ops q = Under lhs rhs ops q
comatch (x :* lhs) (y :* cxt) rhs ops q = comatch lhs cxt (rhs // [(x,y)]) ops q
comatch (i :@ lhs) (j :@ cxt) rhs ops q
  | i == j                              = comatch lhs cxt rhs ops q
comatch lhs         cxt       _   ops q = select ops q

