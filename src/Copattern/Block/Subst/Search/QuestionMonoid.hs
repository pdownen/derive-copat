module Copattern.Block.Subst.Search.QuestionMonoid where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce

data Found i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

-- Simplifying `resume` using the Monoid properties of Questions

search :: Term i a -> Found i a
search m = search' m Nop

search' :: Term i a -> Question i a -> Found i a
search' (Var x)   k = resume  k $ Asked (FreeVar x)    Nop
search' (Dot m)   k = resume  k $ Asked (Introspect m) Nop
search' (Obj ops) k = resume  k $ Asked (Respond ops)  Nop
search' (m :*: n) k = search' m $ n :* k
search' (m :@: i) k = search' m $ i :@ k

resume :: Question i a -> Found i a -> Found i a
resume k (Asked r q) = Asked r (q <> k)
