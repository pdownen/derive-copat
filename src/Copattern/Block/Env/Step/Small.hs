module Copattern.Block.Env.Step.Small where
import Copattern.Block.Syntax
import Copattern.Block.Env.Reduce
import Copattern.Block.Env.Decomp

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = iter $ refocus (m :/: []) Nop

iter :: (Eq a, Eq i) => Decomp i a -> Answer i a
iter (Asked r q) = continue $ reduce r q

continue :: (Eq a, Eq i) => Followup i a -> Answer i a
continue (Next (Reduced m)     k) = iter $ refocus m k
continue (Next (Unknown x)     k) = Stuck x k
continue (Next Unhandled       k) = Raise k
continue (More lhs rhs ops env k) = Under lhs rhs ops env k
