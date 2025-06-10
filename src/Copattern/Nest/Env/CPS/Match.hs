{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Env.CPS.Match where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (ClosQuestion i a)
  | Stuck   (MetaCont i a) a (ClosQuestion i a)
  | CoStuck (MetaCont i a) a

type MetaCont    i a = [Closure i a]
type CPSResponse i a = MetaCont i a     -> Answer i a
type CPSTerm     i a = ClosQuestion i a -> CPSResponse  i a
type CPSOption   i a = ClosQuestion i a -> Closure i a -> CPSTerm i a

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = response r [] []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = term m [] Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = option o [] Nop (Raise :/: []) Nop []

-- (<!!>) has been inlined as part of pattern matching

response :: (Eq a, Eq i)
         => Response i a -> ClosEnv i a
         -> CPSResponse i a
response (Splat k) env (m:/:e:s)
  | Just (QSub q) <- lookup k env = term m e Nop s
response (Splat k) env []
  | Just (QSub q) <- lookup k env = Final q
response (Splat k) env s          = CoStuck s k
response (End)     env (m:/:e:s)  = term m e Nop s
response (End)     env []         = Final Nop
response (m :!: r) env s          = response r env $ (m :/: env) : s

term :: (Eq a, Eq i)
     => Term i a -> ClosEnv i a
     -> CPSTerm i a
term (Var x)    env k s
  | Just (CSub (m:/:e)) <- lookup x env
                            = term m e k s
term (Var x)    env k s     = Stuck s x k
term (Dot m)    env k s     = term m env ((m :/: env) :* k) s
term (m :*: n)  env k s     = term m env ((n :/: env) :* k) s
term (m :@: i)  env k s     = term m env (i :@ k) s
term (Raise)    env k (m:s) = term (openTerm m) (staticEnv m) k s
term (Raise)    env k []    = Final k
term (q :!-> r) env k s     = response r ((q, QSub k) : env) s
term (o :?: m)  env k s     = option o env k (m :/: env) k s

option :: (Eq i, Eq a)
       => Option i a -> ClosEnv i a
       -> CPSOption i a
option (x :*-> o) env q m (n:*k) s = option o ((x, CSub n) : env) q m k s
option (i :@-> o) env q m (j:@k) s
  | i == j                         = option o env q m k s
option (x :?-> n) env _ m k      s = term n ((x, CSub m) : env) k s
option _          env q m _      s = term (openTerm m) (staticEnv m) q s
