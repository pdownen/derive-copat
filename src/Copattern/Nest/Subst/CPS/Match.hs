module Copattern.Nest.Subst.CPS.Match where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (Cont i a)
  | Stuck   (MetaCont i a) a (Cont i a)
  | CoStuck (MetaCont i a) a

type Cont        i a = Question i a
type MetaCont    i a = [Term i a]
type CPSResponse i a = MetaCont i a -> Answer i a
type CPSTerm     i a = Cont i a     -> CPSResponse  i a
type CPSOption   i a = Term i a     -> CPSTerm i a

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = response r []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = term m Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = option o Raise Nop []

-- (<!!>) has been inlined as part of pattern matching

response :: (Eq a, Eq i)
         => Response i a
         -> CPSResponse i a
response (Splat k) s     = CoStuck s k
response (End)     []    = Final Nop
response (End)     (m:s) = term m Nop s
response (m :!: r) s     = response r (m : s)

term :: (Eq i, Eq a) => Term i a
     -> CPSTerm i a
term (Var x)    k s     = Stuck s x k
term (Dot m)    k s     = term m (m :* k) s
term (m :*: n)  k s     = term m (n :* k) s
term (m :@: i)  k s     = term m (i :@ k)s 
term (Raise)    k (m:s) = term m k s
term (Raise)    k []    = Final k
term (q :!-> r) k s     = response (r /!/ [(q, subQ k)]) s
term (o :?: m)  k s     = option o m k s

option :: (Eq a, Eq i) => Option i a
       -> CPSOption i a
option (x :?-> n) m k        = term (n // [(x, subT m)]) k
option (x :*-> o) m (n :* k) = option (o /?/ [(x, subT n)]) (m :*: n) k
option (i :@-> o) m (j :@ k)
  | i == j                   = option o (m :@: i) k
option o m k                 = term m k

subT :: Term i a -> TRSub i a
subT m = TSub m

subQ :: Question i a -> TRSub i a
subQ k = RSub (Raise `ask` k :!: End)
