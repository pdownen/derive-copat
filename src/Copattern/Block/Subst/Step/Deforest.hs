module Copattern.Block.Subst.Step.Deforest where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

-- `iter` is no longer used

-- `continue` is no longer used

-- `Decomp` is no longer used

-- `refocus (Obj eqs)` now subsumes `reduce (Respond eqs)` by matching on `eqs`

refocus :: (Eq i, Eq a)
        => Term i a -> Question i a
        -> Answer i a
refocus (Var x)   k = Stuck x k
refocus (Dot m)   k = refocus m $ m :* k
refocus (Obj eqs) k = case eqs of
  []                -> Raise k
  lhs :-> rhs : eqs -> comatch lhs k [] rhs eqs k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k


-- `Redex i a` is no longer used

-- `Reduct i a` is no longer used

-- `Followup i a` is no longer used

-- only the `Respond` case of `reduce` is accessible.
-- rewrite: `reduce (Respond eqs)` --> `refocus (Obj eqs)`

-- inline `ComatchCxt bind base` on call sites

comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> TermEnv i a -> Term i a -> [Option i a] -> Question i a
        -> Answer i a
comatch Nop        cxt        env rhs _   _ = refocus (rhs // env) cxt
comatch lhs        Nop        env rhs eqs q = Under lhs (rhs // env) eqs q
comatch (x :* lhs) (y :* cxt) env rhs eqs q = comatch lhs cxt ((x,y) : env) rhs eqs q
comatch (i :@ lhs) (j :@ cxt) env rhs eqs q
  | i == j                                  = comatch lhs cxt env rhs eqs q
comatch lhs        cxt        env _   eqs q = refocus (Obj eqs) q

