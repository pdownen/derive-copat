module Copattern.Block.Subst.Step.Refocus where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce
import Copattern.Block.Subst.Decomp

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

-- Property: decomp m = refocus m Nop

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = iter $ refocus m Nop

iter :: (Eq a, Eq i) => Decomp i a -> Answer i a
iter (Asked r q) = continue $ reduce r q

-- Lemma: decomp . recomp m = refocus m

-- Corollary: eval . recomp m = iter . decomp . recomp m = iter . refocus m
continue :: (Eq a, Eq i) => Followup i a -> Answer i a
continue (Next (Reduced m) k) = iter $ refocus m k
continue (Next (Unknown x) k) = Stuck x k
continue (Next Unhandled   k) = Raise k
continue (More lhs rhs eqs k) = Under lhs rhs eqs k

