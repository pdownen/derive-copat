module Copattern.Nest.Subst.Machine.Small where
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

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = eval $ o :?: Raise

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = run $ m :!: End

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = loop $ delimit r

-- Loop

loop :: (Eq i, Eq a) => Delimit i a -> Answer i a
loop (Around r q s) = next (reduce r) q s
loop (Caught r s)   = resume (handle r) s
loop (Uncaught q)   = Final q

iter :: (Eq i, Eq a) => Decomp i a -> MetaCont i a -> Answer i a
iter (Internal r q) s = next (reduce r) q s
iter (External r)   s = resume (handle r) s

-- Corollary: `loop (delimit r) = run r`
resume :: (Eq a, Eq i) => RdResponse i a
       -> MetaCont i a -> Answer i a
resume (UnknownQ k) s = CoStuck s k
resume (RdR r)      s = run $ unwind s r

-- Lemma: `delimit (unwind s (m :!: end)) = Caught (decomp m) s`
-- Proof: by induction on s.

-- Corollary:
--     iter (decomp m) s
--     = loop (delimit (unwind s (m :!: End)))
--     = run (unwind s (m :!: End))

--     iter (decomp (recomp k m)) s
--     = run (unwind s (recomp k m :!: End))

next :: (Eq i, Eq a) => RdTerm i a
     -> Question i a -> MetaCont i a -> Answer i a
next (UnknownA x) k s = Stuck s x k
next (RdT m)      k s = run $ unwind s $ recomp k m :!: End

