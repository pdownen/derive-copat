{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Search.CPS where
import Copattern.Block.Syntax
import Copattern.Block.Subst.Reduce

data Found i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

search :: Term i a -> Found i a
search m = search' m id

search' :: Term i a -> (Found i a -> r) -> r
search' (Var x)   k = k $ Asked (FreeVar x) Nop
search' (Dot m)   k = k $ Asked (Introspect m) Nop
search' (Obj ops) k = k $ Asked (Respond ops) Nop
search' (m :*: n) k = search' m $ \case
  Asked r q -> k $ Asked r $ q <> n :* Nop
search' (m :@: i) k = search' m $ \case
  Asked r q -> k $ Asked r $ q <> i :@ Nop
