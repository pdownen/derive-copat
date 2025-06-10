{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Subst.CPS.Fuse where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (Cont i a)
  | Stuck   (MetaCont i a) a (Cont i a)
  | CoStuck (MetaCont i a) a

type Cont        i a = Question i a
type MetaCont    i a = [Term i a]
type CPSResponse i a = MetaCont i a -> Answer i a
type CPSTerm     i a = Question i a -> CPSResponse  i a
type CPSOption   i a = Term i a     -> CPSTerm i a

data CPSVar i a
  = Name a
  | ClosedT (Term i (CPSVar i a))
  | ClosedQ (Question i (CPSVar i a))

instance Eq a => Eq (CPSVar i a) where
  Name x == Name y = x == y
  _      == _      = False

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = response r []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = term m Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = option o Raise Nop []

(<!!>) :: (Eq a, Eq i)
       => MetaCont i a -> Cont i a
       -> Answer i a
[]    <!!> r = Final r
(m:s) <!!> r = term m r s

response :: (Eq a, Eq i)
         => Response i a
         -> CPSResponse i a
response (Splat k) = \s -> CoStuck s k
response (End)     = \s -> s <!!> Nop
response (m :!: r) = \s -> response r (m : s)

term :: (Eq i, Eq a) => Term i a
     -> CPSTerm i a
term (Var x)    = \k -> \s -> Stuck s x k
term (Dot m)    = \k -> term m (m :* k)
term (m :*: n)  = \k -> term m (n :* k)
term (m :@: i)  = \k -> term m (i :@ k)
term (Raise)    = \k -> \s -> s <!!> k
term (q :!-> r) = \k -> response (r /!/ [(q, subQ k)])
term (o :?: m)  = \k -> option o m k

option :: (Eq a, Eq i) => Option i a
       -> CPSOption i a
option (x :?-> n) = \m -> term (n // [(x, subT m)])
option (x :*-> o) = \m -> \case
  (n :* k) -> option (o /?/ [(x, subT n)]) (m :*: n) k
  k        -> term m k
option (i :@-> o) = \m -> \case
  (j :@ k) | i == j -> option o (m :@: i) k
  k                 -> term m k

-- Lemma:
-- 1. inlineQuestion (fmap (fmap Name) q) = q
-- 2. inlineResponse (fmap Name r) = r
-- 1. inlineTerm (fmap Name m) = m
-- 3. inlineOption (fmapName o) = o

subT :: Term i a -> TRSub i a
subT m = TSub m
  -- = TSub (inlineTerm (fmap Name m))
  -- = TSub (inlineTerm (Var (ClosedT (fmap Name m))))

subQ :: Question i a -> TRSub i a
subQ k = RSub (Raise `ask` k :!: End)
  -- = RSub (Raise `askQuestion` inlineQuestion (fmap (fmap Name) k) :!: End)
  -- = RSub (inlineResponse (Splat (ClosedQ (fmap (fmap Name) k))))

inlineQuestion :: Question i (CPSVar i a) -> Question i a
inlineQuestion = fmap inlineTerm

inlineResponse :: Response i (CPSVar i a) -> Response i a
inlineResponse (Splat (Name k))    = Splat k
inlineResponse (Splat (ClosedQ q)) = Raise `ask` inlineQuestion q :!: End
inlineResponse (Splat (ClosedT _)) = error "Illegal expression: using a term as a question"
inlineResponse (End)               = End
inlineResponse (m :!: r)           = inlineTerm m :!: inlineResponse r

inlineTerm :: Term i (CPSVar i a) -> Term i a
inlineTerm (Var (Name x))    = Var x
inlineTerm (Var (ClosedT m)) = inlineTerm m
inlineTerm (Var (ClosedQ _)) = error "Illegal expression: using a question as a term"
inlineTerm (Dot m)           = Dot (inlineTerm m)
inlineTerm (m :*: n)         = inlineTerm m :*: inlineTerm n
inlineTerm (m :@: i)         = inlineTerm m :@: i
inlineTerm (Raise)           = Raise
inlineTerm (Name q :!-> r)   = q :!-> inlineResponse r
inlineTerm (_ :!-> r)        = error "Illegal expression: binding a non-name"
inlineTerm (o :?: m)         = inlineOption o :?: inlineTerm m

inlineOption :: Option i (CPSVar i a) -> Option i a
inlineOption (i :@-> o)      = i :@-> inlineOption o
inlineOption (Name x :*-> o) = x :*-> inlineOption o
inlineOption (_ :*-> o)      = error "Illegal expression: binding a non-name"
inlineOption (Name x :?-> m) = x :?-> inlineTerm m
inlineOption (_ :?-> m)      = error "Illegal expression: binding a non-name"
