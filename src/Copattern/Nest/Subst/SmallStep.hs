module Copattern.Nest.Subst.SmallStep where
import Copattern.Nest.Syntax
import Copattern.Nest.Subst.Reduce
import Copattern.Nest.Subst.Decomp

data Answer i a
  = Final   (Question i a)
  | Stuck   [Term i a] a (Question i a)
  | CoStuck [Term i a] a
  deriving (Show)

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = eval $ o :?: Raise

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = run $ m :!: End

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = case delimit r of
  Around r q s -> case reduce r of
    UnknownA x -> Stuck s x q
    RdT m      -> run $ unwind s $ recomp q m :!: End
  Caught r s   -> case handle r of
    UnknownQ k -> CoStuck s k
    RdR r      -> run $ unwind s r
  Uncaught q   -> Final q
