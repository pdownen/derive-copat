module Copattern.Block.Subst.Machine.Case where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

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
select (eq : ops) q = equate eq ops q

equate :: (Eq i, Eq a) => Option i a -> [Option i a] -> Question i a -> Answer i a
equate (lhs :-> rhs) ops q = comatch lhs q rhs ops q

comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> Term i a -> [Option i a] -> Question i a
        -> Answer i a
comatch Nop        cxt rhs _   _ = refocus rhs cxt
comatch (x :* lhs) cxt rhs ops q = case cxt of
  (y :* k) -> comatch lhs k (rhs // [(x,y)]) ops q
  Nop      -> Under (x :* lhs) rhs ops q
  _        -> select ops q
comatch (i :@ lhs) cxt rhs ops q = case cxt of
  (j :@ k) | i == j -> comatch lhs cxt rhs ops q
  Nop               -> Under (i :@ lhs) rhs ops q
  _                 -> select ops q

