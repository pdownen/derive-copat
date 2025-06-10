module Copattern.Block.Subst.Machine where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

refocus :: (Eq i, Eq a) => Term i a -> Question i a -> Answer i a
refocus (Var x)   k = Stuck x k
refocus (Dot m)   k = refocus m $ m :* k
refocus (Obj os)  k = case os of
  []               -> Raise k
  lhs :-> rhs : os -> comatch lhs k rhs os k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k

comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> Term i a -> [Option i a] -> Question i a
        -> Answer i a
comatch Nop         cxt       rhs _  _ = refocus rhs cxt
comatch lhs         Nop       rhs os q = Under lhs rhs os q
comatch (x :* lhs) (y :* cxt) rhs os q = comatch lhs cxt (rhs // [(x,y)]) os q
comatch (i :@ lhs) (j :@ cxt) rhs os q
  | i == j                             = comatch lhs cxt rhs os q
comatch lhs         cxt       _   os q = refocus (Obj os) q

