module Copattern.Block.Subst.Decomp where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce

data Decomp i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

recomp :: Term i a -> Question i a -> Term i a
recomp = ask

decomp :: Term i a -> Decomp i a
decomp m = refocus m Nop

refocus :: Term i a -> Question i a -> Decomp i a
refocus (Var x)   k = Asked (FreeVar x) k
refocus (Dot m)   k = Asked (Introspect m) k
refocus (Obj eqs) k = Asked (Respond eqs) k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k
