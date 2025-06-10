module Copattern.Block.Env.SmallStep where
import Copattern.Block.Syntax
import Copattern.Block.Env.Reduce
import Copattern.Block.Env.Decomp

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

fromAnswer :: Eq a => Answer i a -> Term i a
fromAnswer (Stuck x q)               = Var x `ask` fmap inlineClos q
fromAnswer (Raise q)                 = Obj [] `ask` fmap inlineClos q
fromAnswer (Under lhs rhs ops env q) = Obj [lhs :-> (inlineClos rhs // env'),
                                            Nop :-> (m `ask` fmap inlineClos q)]
  where env' = inlineEnv env
        m    = Obj [ q :-> (n // env') | (q :-> n) <- ops ]

eval :: (Eq a, Eq i) => Term i a -> Answer i a
eval m = iter $ decomp (m :/: [])

-- Start with refocusing form

iter :: (Eq a, Eq i) => Decomp i a -> Answer i a
iter (Asked r q) = case reduce r q of
  Next (Reduced m)     k -> iter $ refocus m k
  Next (Unknown x)     k -> Stuck x k
  Next Unhandled       k -> Raise k
  More lhs rhs ops env k -> Under lhs rhs ops env k
