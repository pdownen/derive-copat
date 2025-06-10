module Copattern.Nest.Subst.Machine.Refocused where
import Copattern.Nest.Syntax
import Copattern.Nest.Subst.Reduce

data Answer i a
  = Final   (Question i a)
  | Stuck   (MetaCont i a) a (Question i a)
  | CoStuck (MetaCont i a) a
  deriving (Show)

type MetaCont i a = [Term i a]

-- rewrite: `delim r s`   --> `loop (delim r s)`
-- rewrite: `refocus m k` --> `iter (refocus m k)`

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

next :: (Eq i, Eq a) => RdTerm i a
     -> Question i a -> MetaCont i a -> Answer i a
next (UnknownA x) k s = Stuck s x k
next (RdT m)      k s = iter (refocus m k) s

loop :: (Eq i, Eq a) => Delimit i a -> Answer i a
loop (Around r q s) = next (reduce r) q s
loop (Caught r s)   = resume (handle r) s
loop (Uncaught q)   = Final q

resume :: (Eq a, Eq i) => RdResponse i a -> MetaCont i a -> Answer i a
resume (UnknownQ k) s = CoStuck s k
resume (RdR r)      s = loop (delim r s)

-- Refocusing

data Delimit i a
  = Around (RxTerm i a) (Question i a) (MetaCont i a)
  | Caught (RxResponse i a) (MetaCont i a)
  | Uncaught (Question i a)

delim :: Response i a -> MetaCont i a -> Delimit i a
delim (m :!: r) s     = delim r (m : s)
delim (End)     (m:s) = catch (refocus m Nop) s
delim (End)     []    = Uncaught Nop
delim (Splat k) s     = Caught (FreeCoVar k) s

catch :: Decomp i a -> [Term i a] -> Delimit i a
catch (Internal r q) s     = Around r q s
catch (External r)   s     = Caught r s
catch (Raised q)     (m:s) = Caught (Reset m q) s
catch (Raised q)     []    = Uncaught q

-- rewrite: `next (reduce r) k`  -->  `Internal r k`
-- rewrite: `resume (handle r)`  -->  `External r`
data Decomp i a
  = Internal (RxTerm i a) (Question i a)
  | External (RxResponse i a)
  | Raised   (Question i a)

refocus :: Term i a -> Question i a -> Decomp i a
refocus (m :*: n)  k = refocus m (n :* k)
refocus (m :@: i)  k = refocus m (i :@ k) 
refocus (o :?: m)  k = decide (consider o m) k
refocus (Dot m)    k = Internal (Introspect m) k
refocus (q :!-> r) k = External (Shift q r k)
refocus (Raise)    k = Raised k
refocus (Var x)    k = Internal (FreeVar x) k

-- rewrite: `next (reduce (Try x n m))`  -->  `Inward x n m`
-- rewrite: `comatch o`                  -->  `Outward o`
data Consider i a
  = Inward a (Term i a) (Term i a)
  | Outward (CoObject i a)

consider :: Option i a -> Term i a -> Consider i a
consider (x :?-> n) m = Inward x n m
consider (x :*-> o) m = Outward $ CoO (Arg x) o m
consider (i :@-> o) m = Outward $ CoO (At i) o m

decide :: Consider i a -> Question i a -> Decomp i a
decide (Outward o)    = comatch o
decide (Inward x n m) = Internal (Try x n m)

comatch :: CoObject i a -> Question i a -> Decomp i a
comatch o (n :* k) = Internal (Pop o n) k
comatch o (j :@ k) = Internal (Get o j) k
comatch o Nop      = External $ Under o
