module Copattern.Nest.Subst.Machine.Recomp where
import Copattern.Nest.Syntax
import Copattern.Nest.Subst.Reduce
import Copattern.Nest.Subst.Decomp

data Answer i a
  = Final   (Question i a)
  | Stuck   (MetaCont i a) a (Question i a)
  | CoStuck (MetaCont i a) a
  deriving (Show)

type MetaCont i a = [Term i a]

-- Start

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = loop (delim r [])

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = iter (refocus m Nop) []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = iter (decide (consider o Raise) Nop) []

-- Loop

iter :: (Eq i, Eq a) => Decomp i a -> MetaCont i a -> Answer i a
iter (Internal r q) s = next (reduce r) q s
iter (External r)   s = resume (handle r) s

-- Lemma: `decomp (recomp k m) = refocus m k`
next :: (Eq i, Eq a) => RdTerm i a
     -> Question i a -> MetaCont i a -> Answer i a
next (UnknownA x) k s = Stuck s x k
next (RdT m)      k s = iter (decomp (recomp k m)) s

loop :: (Eq i, Eq a) => Delimit i a -> Answer i a
loop (Around r q s) = next (reduce r) q s
loop (Caught r s)   = resume (handle r) s
loop (Uncaught q)   = Final q

-- Lemma: `delimit (unwind s r) = delim r s`
resume :: (Eq a, Eq i) => RdResponse i a -> MetaCont i a -> Answer i a
resume (UnknownQ k) s = CoStuck s k
resume (RdR r)      s = loop (delimit (unwind s r))
