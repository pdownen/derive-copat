module Copattern.Block.Subst.Search.Direct where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce

data Found i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

search :: Term i a -> Found i a
search (Var x)   = Asked (FreeVar x) Nop
search (Dot m)   = Asked (Introspect m) Nop
search (Obj ops) = Asked (Respond ops) Nop
search (m :*: n) = case search m of
  Asked r q -> Asked r $ q <> n :* Nop
search (m :@: i) = case search m of
  Asked r q -> Asked r $ q <> i :@ Nop
