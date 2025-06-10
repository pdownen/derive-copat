module Copattern.Block.Subst.Search.Corridor where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce

data Found i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

search :: Term i a -> Found i a
search m = search' m Nop

search' :: Term i a -> Question i a -> Found i a
search' (Var x)   k = Asked (FreeVar x) k
search' (Dot m)   k = Asked (Introspect m) k
search' (Obj ops) k = Asked (Respond ops) k
search' (m :*: n) k = search' m $ n :* k
search' (m :@: i) k = search' m $ i :@ k
