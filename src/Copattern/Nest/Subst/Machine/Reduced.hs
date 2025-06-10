module Copattern.Nest.Subst.Machine.Reduced where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (Cont i a)
  | Stuck   (MetaCont i a) a (Cont i a)
  | CoStuck (MetaCont i a) a
  deriving (Show)

type Cont     i a = Question i a
type MetaCont i a = [Term i a]

subQ :: Question i a -> TRSub i a
subQ k = RSub (Raise `ask` k :!: End)

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = delim r []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = consider o Raise Nop []


-- Reduction

data CoFrame i a
  = Arg a
  | At i

data CoObject i a
  = CoO { coframe :: CoFrame i a,
          success :: Option i a,
          failure :: Term i a }

data RxTerm i a
  = FreeVar a
  | Introspect (Term i a)
  | Try a (Term i a) (Term i a)
  | Pop (CoObject i a) (Term i a)
  | Get (CoObject i a) i

data RdTerm i a
  = RdT (Term i a)
  | UnknownA a

reduce :: (Eq i, Eq a) => RxTerm i a -> RdTerm i a
reduce (FreeVar x)    = UnknownA x
reduce (Introspect m) = RdT $ m :*: m
reduce (Try x n m)    = RdT $ n // [(x, TSub m)]
reduce (Pop (CoO (Arg x) o m) n)
                      = RdT $ (o /?/ [(x, TSub m)]) :?: (m :*: n)
reduce (Pop o n)      = RdT $ failure o :*: n
reduce (Get (CoO (At i) o m) j)
  | i == j            = RdT $ o :?: (m :@: i)
reduce (Get o i)      = RdT $ failure o :@: i

data RxResponse i a
  = FreeCoVar a
  | Reset (Term i a) (Cont i a)
  | Shift a (Response i a) (Cont i a)
  | Under (CoObject i a)

data RdResponse i a
  = RdR (Response i a)
  | UnknownQ a

handle :: Eq a => RxResponse i a -> RdResponse i a
handle (FreeCoVar k) = UnknownQ k
handle (Reset m q)   = RdR $ m `ask` q :!: End
handle (Shift k r q) = RdR $ r /!/ [(k, subQ q)]
handle (Under o)     = RdR $ failure o :!: End

-- Loop

next :: (Eq i, Eq a) => RdTerm i a
     -> Cont i a -> MetaCont i a -> Answer i a
next (UnknownA x) k s = Stuck s x k
next (RdT m)      k s = refocus m k s

resume :: (Eq a, Eq i) => RdResponse i a -> MetaCont i a -> Answer i a
resume (UnknownQ k) s = CoStuck s k
resume (RdR r)      s = delim r s

-- Original

delim :: (Eq a, Eq i)
      => Response i a -> MetaCont i a
      -> Answer i a
-- Refocusing
delim (m :!: r) s     = delim r (m : s)
-- Reduction
delim (End)     (m:s) = refocus m Nop s
-- Terminal
delim (End)     []    = Final Nop
delim (Splat k) s     = resume (handle (FreeCoVar k)) s

refocus :: (Eq i, Eq a)
        => Term i a -> Cont i a -> MetaCont i a
        -> Answer i a
-- Refocusing
refocus (m :*: n)  k s     = refocus m (n :* k) s
refocus (m :@: i)  k s     = refocus m (i :@ k) s 
refocus (o :?: m)  k s     = consider o m k s
-- Reduction
refocus (Dot m)    k s     = next (reduce $ Introspect m) k s
refocus (q :!-> r) k s     = resume (handle (Shift q r k)) s
refocus (Raise)    k (m:s) = resume (handle (Reset m k)) s
-- Terminal
refocus (Raise)    k []    = Final k
refocus (Var x)    k s     = next (reduce $ FreeVar x) k s

-- Extra step `consider` to weigh the given option(s) before copattern-matching
-- on the continuation
consider :: (Eq a, Eq i)
         => Option i a -> Term i a -> Cont i a -> MetaCont i a
         -> Answer i a
-- Reduction
consider (x :?-> n) m = next (reduce $ Try x n m)
-- Refocus
consider (x :*-> o) m = comatch (CoO (Arg x) o m)
consider (i :@-> o) m = comatch (CoO (At i) o m)

comatch :: (Eq i, Eq a) => CoObject i a
        -> Cont i a -> MetaCont i a -> Answer i a
-- Reduction
comatch o (n :* k) = next (reduce $ Pop o n) k
comatch o (j :@ k) = next (reduce $ Get o j) k
comatch o Nop      = resume $ handle (Under o)
