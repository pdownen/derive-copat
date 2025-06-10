{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Env.CPS.Eta where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (ClosQuestion i a)
  | Stuck   (MetaCont i a) a (ClosQuestion i a)
  | CoStuck (MetaCont i a) a

type MetaCont    i a = [Closure i a]
type CPSResponse i a = MetaCont i a     -> Answer i a
type CPSTerm     i a = ClosQuestion i a -> CPSResponse  i a
type CPSOption   i a = ClosQuestion i a -> Closure i a -> CPSTerm i a

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = response r [] []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = term m [] Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = option o [] Nop (Raise :/: []) Nop []

(<!!>) :: (Eq a, Eq i)
       => MetaCont i a -> ClosQuestion i a
       -> Answer i a
[]    <!!> r = Final r
(m:s) <!!> r = term (openTerm m) (staticEnv m) r s

response :: (Eq a, Eq i)
         => Response i a -> ClosEnv i a
         -> CPSResponse i a
response (Splat k) env s = case lookup k env of
  Just (QSub q) -> s <!!> q
  _             -> CoStuck s k 
response (End)     env s = s <!!> Nop
response (m :!: r) env s = response r env $ (m :/: env) : s

term :: (Eq a, Eq i)
     => Term i a -> ClosEnv i a
     -> CPSTerm i a
term (Var x)   env k s = case lookup x env of
  Just (CSub m) -> term (openTerm m) (staticEnv m) k s
  _             -> Stuck s x k
term (Dot m)    env k s = term m env ((m :/: env) :* k) s
term (m :*: n)  env k s = term m env ((n :/: env) :* k) s
term (m :@: i)  env k s = term m env (i :@ k) s
term (Raise)    env k s = s <!!> k
term (q :!-> r) env k s = response r ((q, QSub k) : env) s
term (o :?: m)  env k s = option o env k (m :/: env) k s

option :: (Eq i, Eq a)
       => Option i a -> ClosEnv i a
       -> CPSOption i a
option (x :*-> o) env q m k = case k of
  (n :* k') -> option o ((x, CSub n) : env) q m k'
  _         -> term (openTerm m) (staticEnv m) q
option (i :@-> o) env q m k = case k of
  (j :@ k') | i == j -> option o env q m k'
  _                  -> term (openTerm m) (staticEnv m) q
option (x :?-> n) env _ m k = term n ((x, CSub m) : env) k
