{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Env.CPS where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (CPSQuestion i a)
  | Stuck   [CPSTerm i a] a (CPSQuestion i a)
  | CoStuck [CPSTerm i a] a

type CPSQuestion i a = Copattern i (CPSArg i a)
type CPSResponse i a = Answer i a
type CPSTerm     i a = CPSQuestion i a -> CPSResponse  i a
type CPSOption   i a = CPSQuestion i a -> CPSTerm i a -> CPSTerm i a

data CPSSub i a = CPST (CPSTerm i a) | CPSQ (CPSQuestion i a)

type CPSEnv i a = Env a (CPSSub i a)

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = (response r [])

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = (term m []) Nop

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = (option o []) Nop (term Raise []) Nop

response :: (Eq a, Eq i)
         => Response i a -> CPSEnv i a
         -> Answer i a
response (Splat k) env = case lookup k env of
  Just (CPSQ q) -> Final q
  _             -> CoStuck [] k 
response (End)     env = Final Nop
response (m :!: r) env = (term m env) <!> (response r env)

(<!>) :: CPSTerm i a -> Answer i a -> Answer i a
f <!> (Final r)      = f r
f <!> (Stuck gs x q) = Stuck (f : gs) x q
f <!> (CoStuck gs q) = CoStuck (f : gs) q

term :: (Eq a, Eq i)
     => Term i a -> CPSEnv i a
     -> CPSTerm i a
term (Var x)   env = case lookup x env of
  Just (CPST m) -> m
  _             -> Stuck [] x
term (Dot m)    env = \k -> (term m env) (Arg (term m env) :* k)
term (m :*: n)  env = \k -> (term m env) (Arg (term n env) :* k)
term (m :@: i)  env = \k -> (term m env) (i :@ k)
term (Raise)    env = \k -> Final k
term (q :!-> r) env = \k -> (response r ((q, CPSQ k) : env))
term (o :?: m)  env = \k -> (option o env) k (term m env) k

option :: (Eq i, Eq a)
       => Option i a -> CPSEnv i a
       -> CPSOption i a
option (x :*-> o) env = \q f -> \case
  (y :* k) -> (option o ((x, CPST (useArg y)) : env)) q f k
  _        -> f q
option (i :@-> o) env = \q f -> \case
  (j :@ k) | i == j -> (option o env) q f k
  _                 -> f q
option (x :?-> m) env = \_ f -> (term m ((x, CPST f) : env))
