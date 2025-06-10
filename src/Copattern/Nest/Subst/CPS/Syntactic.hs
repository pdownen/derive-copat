{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Subst.CPS.Syntactic where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (Cont i a)
  | Stuck   (MetaCont i a) a (Cont i a)
  | CoStuck (MetaCont i a) a

type Cont        i a = Question i (CPSVar i a)
type MetaCont    i a = [Term i (CPSVar i a)]
type CPSResponse i a = MetaCont i a        -> Answer i a
type CPSTerm     i a = Cont i a            -> CPSResponse  i a
type CPSOption   i a = Term i (CPSVar i a) -> CPSTerm i a

data CPSVar i a
  = Name a
  | ClosedT (Term i (CPSVar i a))
  | ClosedQ (Cont i a)

instance Eq a => Eq (CPSVar i a) where
  Name x == Name y = x == y
  _      == _      = False

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = response (fmap Name r) []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = term (fmap Name m) Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = option (fmap Name o) Raise Nop []


(<!!>) :: (Eq a, Eq i)
       => MetaCont i a -> Cont i a
       -> Answer i a
[]    <!!> r = Final r
(m:s) <!!> r = term m r s

response :: (Eq a, Eq i)
         => Response i (CPSVar i a)
         -> CPSResponse i a
response (Splat (Name k))    = \s -> CoStuck s k
response (Splat (ClosedQ q)) = \s -> s <!!> q
response (Splat (ClosedT _)) = error "Illegal expression: using a term as a question"
response (End)               = \s -> s <!!> Nop
response (m :!: r)           = \s -> response r (m : s)

term :: (Eq i, Eq a) => Term i (CPSVar i a)
     -> CPSTerm i a
term (Var (Name x))    = \k -> \s -> Stuck s x k
term (Var (ClosedT m)) = term m
term (Var (ClosedQ _)) = error "Illegal expression: using a question as a term"
term (Dot m)           = \k -> term m (m :* k)
term (m :*: n)         = \k -> term m (n :* k)
term (m :@: i)         = \k -> term m (i :@ k)
term (Raise)           = \k -> \s -> s <!!> k
term (q :!-> r)        = \k -> response (r /!/ [(q, subQ k)])
term (o :?: m)         = \k -> option o m k

option :: (Eq a, Eq i) => Option i (CPSVar i a)
       -> CPSOption i a
option (x :?-> n) = \m -> term (n // [(x, subT m)])
option (x :*-> o) = \m -> \case
  (n :* k) -> option (o /?/ [(x, subT n)]) (m :*: n) k
  k        -> term m k
option (i :@-> o) = \m -> \case
  (j :@ k) | i == j -> option o (m :@: i) k
  k                 -> term m k

subT :: Term i (CPSVar i a) -> TRSub b (CPSVar i a)
subT m = TSub (Var (ClosedT m))

subQ :: Cont i a -> TRSub b (CPSVar i a)
subQ k = RSub (Splat (ClosedQ k))
