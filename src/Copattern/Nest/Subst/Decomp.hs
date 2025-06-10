module Copattern.Nest.Subst.Decomp where
import Copattern.Nest.Syntax
import Copattern.Nest.Subst.Reduce

-- Delimited responses

data Delimit i a
  = Around (RxTerm i a) (Question i a) [Term i a]
  | Caught (RxResponse i a) [Term i a]
  | Uncaught (Question i a)

delimit :: Response i a -> Delimit i a
delimit r = delim r []

unwind :: [Term i a] -> Response i a -> Response i a
unwind []    r = r
unwind (m:s) r = m :!: r

delim :: Response i a -> [Term i a] -> Delimit i a
delim (m :!: r) s     = delim r (m : s)
delim (End)     (m:s) = catch (refocus m Nop) s
delim (End)     []    = Uncaught Nop
delim (Splat k) s     = Caught (FreeCoVar k) s

catch :: Decomp i a -> [Term i a] -> Delimit i a
catch (Internal r q) s     = Around r q s
catch (External r)   s     = Caught r s
catch (Raised q)     (m:s) = Caught (Reset m q) s
catch (Raised q)     []    = Uncaught q

-- Undelimited terms

data Decomp i a
  = Internal (RxTerm i a) (Question i a)
  | External (RxResponse i a)
  | Raised   (Question i a)

decomp :: Term i a -> Decomp i a
decomp m = refocus m Nop

recomp :: Question i a -> Term i a -> Term i a
recomp q m = m `ask` q

refocus :: Term i a -> Question i a -> Decomp i a
refocus (m :*: n)  k = refocus m (n :* k)
refocus (m :@: i)  k = refocus m (i :@ k) 
refocus (o :?: m)  k = decide (consider o m) k
refocus (Dot m)    k = Internal (Introspect m) k
refocus (q :!-> r) k = External (Shift q r k)
refocus (Raise)    k = Raised k
refocus (Var x)    k = Internal (FreeVar x) k

-- Weighing options

data Consider i a
  = Inward a (Term i a) (Term i a)
  | Outward (CoObject i a)

only :: Option i a -> Consider i a
only o = consider o Raise

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
