module Copattern.Block.Subst.Step.Subst where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

-- rewrite: `comatch lhs k env rhs` --> `comatch lhs k (rhs // env)`

-- Lemma: `m // [] = m`
refocus :: (Eq i, Eq a) => Term i a -> Question i a -> Answer i a
refocus (Var x)   k = Stuck x k
refocus (Dot m)   k = refocus m $ m :* k
refocus (Obj eqs) k = case eqs of
  []                -> Raise k
  lhs :-> rhs : eqs -> comatch lhs k rhs eqs k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k

-- Immediately substitute at each matching step.

-- Lemma: `m // (env ++ env') = (m // env) // env'`
comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> Term i a -> [Option i a] -> Question i a
        -> Answer i a
comatch Nop        cxt        rhs _   _ = refocus rhs cxt
comatch lhs        Nop        rhs eqs q = Under lhs rhs eqs q
comatch (x :* lhs) (y :* cxt) rhs eqs q = comatch lhs cxt (rhs // [(x,y)]) eqs q
comatch (i :@ lhs) (j :@ cxt) rhs eqs q
  | i == j                              = comatch lhs cxt rhs eqs q
comatch lhs        cxt        _   eqs q = refocus (Obj eqs) q

