module Copattern.Nest.Subst.Machine where
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
try o = comatch o Raise Nop []

delim :: (Eq a, Eq i)
      => Response i a -> MetaCont i a
      -> Answer i a
delim (Splat k) s     = CoStuck s k
delim (End)     []    = Final Nop
delim (End)     (m:s) = refocus m Nop s
delim (m :!: r) s     = delim r (m : s)

refocus :: (Eq i, Eq a)
        => Term i a -> Cont i a -> MetaCont i a
        -> Answer i a
refocus (Var x)    k s     = Stuck s x k
refocus (Dot m)    k s     = refocus m (m :* k) s
refocus (m :*: n)  k s     = refocus m (n :* k) s
refocus (m :@: i)  k s     = refocus m (i :@ k)s 
refocus (Raise)    k (m:s) = refocus m k s
refocus (Raise)    k []    = Final k
refocus (q :!-> r) k s     = delim (r /!/ [(q, subQ k)]) s
refocus (o :?: m)  k s     = comatch o m k s

comatch :: (Eq a, Eq i)
        => Option i a -> Term i a -> Cont i a -> MetaCont i a
        -> Answer i a
comatch (x :?-> n) m k        = refocus (n // [(x, TSub m)]) k
comatch (x :*-> o) m (n :* k) = comatch (o /?/ [(x, TSub n)]) (m :*: n) k
comatch (i :@-> o) m (j :@ k)
  | i == j                    = comatch o (m :@: i) k
comatch o          m k        = refocus m k
