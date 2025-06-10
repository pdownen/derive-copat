{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Env.Machine.Denote where
import Copattern.Block.Syntax

-- rewrite: `Under lhs rhs ops` -->  `Under (comatch lhs rhs ops)`

data Answer i a
  = Under (CPSTerm i a)
  | Raise (CPSQuestion i a)
  | Stuck a (CPSQuestion i a)

type CPSQuestion i a = Copattern i (CPSArg i a)
type CPSTerm     i a = CPSQuestion i a -> Answer  i a
type CPSOption   i a = CPSTerm     i a -> CPSTerm i a
type CPSCopat    i a = CPSQuestion i a -> CPSOption  i a

type CPSEnv i a = Env a (CPSTerm i a)

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = (refocus m []) Nop

refocus :: (Eq i, Eq a) => Term i a -> CPSEnv i a
        -> CPSTerm i a
refocus (Var x)   env = case lookup x env of
  Nothing -> Stuck x
  Just m  -> m
refocus (Dot m)   env = \k -> (refocus m env) (Arg (refocus m env) :* k)
refocus (Obj ops) env = select ops env
refocus (m :*: n) env = \k -> (refocus m env) (Arg (refocus n env) :* k)
refocus (m :@: i) env = \k -> (refocus m env) (i :@ k)

select :: (Eq i, Eq a) => [Option i a] -> CPSEnv i a
       -> CPSTerm i a
select []         env = Raise
select (op : ops) env = (option op env) (select ops env)

option :: (Eq i, Eq a) => Option i a -> CPSEnv i a
       -> CPSOption i a
option (lhs :-> rhs) env = \ops q -> (comatch lhs rhs [] env) q ops q

comatch :: (Eq a, Eq i)
        => Copattern i a -> Term i a -> CPSEnv i a -> CPSEnv i a
        -> CPSCopat i a
comatch Nop        rhs env' env = \_ _   -> (refocus rhs (env' ++ env))
comatch (x :* lhs) rhs env' env = \q ops -> \case
  (y :* k) -> (comatch lhs rhs ((x, useArg y) : env') env) q ops k
  Nop      -> Under $ (comatch (x :* lhs) rhs env' env) q ops
  _        -> ops q
comatch (i :@ lhs) rhs env' env = \q ops -> \case
  (j :@ k) | i == j -> (comatch lhs rhs env' env) q ops k
  Nop               -> Under $ (comatch (i :@ lhs) rhs env' env) q ops
  _                 -> ops q

