{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Subst.CPS where
import Copattern.Nest.Syntax

data Answer i a
  = Final  (CPSQuestion i a)
  | Stuck   [CPSTerm i a] a (CPSQuestion i a)
  | CoStuck [CPSTerm i a] a

type CPSQuestion i a = Copattern i (CPSArg i a)
type CPSResponse i a = Answer i a
type CPSTerm     i a = CPSQuestion i a -> Answer  i a
type CPSOption   i a = CPSTerm     i a -> CPSTerm i a

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

data CPSVar i a = Name a | CPST (CPSTerm i a) | CPSQ (CPSQuestion i a)

instance Eq a => Eq (CPSVar i a) where
  Name x == Name y = x == y
  _      == _      = False

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = (response (fmap Name r))

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = (term (fmap Name m)) Nop

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = (option (fmap Name o)) (term Raise) Nop

response :: (Eq i, Eq a) => Response i (CPSVar i a) -> Answer i a
response (Splat (Name k)) = CoStuck [] k
response (Splat (CPSQ q)) = Final q
response (Splat (CPST _)) = error "Illegal expression: using a term as a question"
response (End)            = Final Nop
response (m :!: r)        = (term m) <!> (response r)

(<!>) :: CPSTerm i a -> Answer i a -> Answer i a
f <!> Final q     = f q
f <!> Stuck gs x q = Stuck (f:gs) x q
f <!> CoStuck gs q = CoStuck (f:gs) q

term :: (Eq i, Eq a) => Term i (CPSVar i a)
     -> CPSTerm i a
term (Var (Name x)) = Stuck [] x
term (Var (CPST m)) = m
term (Var (CPSQ _)) = error "Illegal expression: using a question as a term"
term (Dot m)        = \k -> (term m) (Arg (term m) :* k)
term (m :*: n)      = \k -> (term m) (Arg (term n) :* k)
term (m :@: i)      = \k -> (term m) (i :@ k)
term (Raise)        = \k -> Final k
term (q :!-> r)     = \k -> (response (r /!/ [(q, subQ k)]))
term (o :?: m)      = \k -> (option o) (term m) k

option :: (Eq a, Eq i) => Option i (CPSVar i a)
       -> CPSOption i a
option (x :?-> m) = \f -> (term $ m // [(x, subT f)])
option (x :*-> o) = \f -> \case
  (y :* k) -> (option $ o /?/ [(x, subT $ useArg y)]) (f . (y :*)) k
  k        -> f k
option (i :@-> o) = \f -> \case
  (j :@ k) | i == j -> (option o) (f . (i :@)) k
  k                 -> f k

-- Lemma: (option' o) (g k) f k = (option o) (f . g) k
-- Proof: by induction on o and cases on k.

-- Corollary: (option' o) k f k = (option o) f k
-- Proof:
--     (option' o) k f k
--     = (option' o) (id k) f k
--     = (option o) (f . id) k
--     = (option o) f k

type CPSOption' i a = CPSQuestion i a -> CPSTerm i a -> CPSTerm i a

option' :: (Eq a, Eq i) => Option i (CPSVar i a)
        -> CPSOption' i a
option' (x :?-> m) = \_ f -> (term $ m // [(x, subT f)])
option' (x :*-> o) = \q f -> \case
  (y :* k) -> (option' $ o /?/ [(x, subT $ useArg y)]) q f k
  k        -> f q
option' (i :@-> o) = \q f -> \case
  (j :@ k) | i == j -> (option' o) q f k
  k                 -> f q

subT m = TSub (Var (CPST m))

subQ k = RSub (Splat (CPSQ k))
