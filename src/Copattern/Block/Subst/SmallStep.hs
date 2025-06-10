module Copattern.Block.Subst.SmallStep where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce
import Copattern.Block.Subst.Decomp

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

fromAnswer :: Answer i a -> Term i a
fromAnswer (Stuck x q)           = Var x `ask` q
fromAnswer (Raise q)             = Obj [] `ask` q
fromAnswer (Under lhs rhs eqs q) = Obj [lhs :-> rhs,
                                        Nop :-> (Obj eqs `ask` q)]

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = iter $ decomp m

iter :: (Eq a, Eq i) => Decomp i a -> Answer i a
iter (Asked r q) = case reduce r q of
  Next (Reduced m) k -> eval $ recomp m k
  Next (Unknown x) k -> Stuck x k
  Next Unhandled   k -> Raise k
  More lhs rhs eqs k -> Under lhs rhs eqs k
