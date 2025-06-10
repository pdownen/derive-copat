module Copattern.Nest.Subst.Reduce where
import Copattern.Nest.Syntax

-- Terms

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

-- Responses

data RxResponse i a
  = FreeCoVar a
  | Reset (Term i a) (Question i a)
  | Shift a (Response i a) (Question i a)
  | Under (CoObject i a)

data RdResponse i a
  = RdR (Response i a)
  | UnknownQ a

handle :: Eq a => RxResponse i a -> RdResponse i a
handle (FreeCoVar k) = UnknownQ k
handle (Reset m q)   = RdR $ m `ask` q :!: End
handle (Shift k r q) = RdR $ r /!/ [(k, subQ q)]
handle (Under o)     = RdR $ failure o :!: End

subQ :: Question i a -> TRSub i a
subQ k = RSub (Raise `ask` k :!: End)
