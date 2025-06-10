{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Env.CPS where
import Copattern.Block.Syntax

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
eval m = (term m []) Nop

term :: (Eq i, Eq a) => Term i a -> CPSEnv i a
        -> CPSTerm i a
term (Var x)   env = case lookup x env of
  Nothing -> Stuck x
  Just m  -> m
term (Dot m)   env = \k -> (term m env) (Arg (term m env) :* k)
term (Obj os)  env = options os env
term (m :*: n) env = \k -> (term m env) (Arg (term n env) :* k)
term (m :@: i) env = \k -> (term m env) (i :@ k)

options :: (Eq i, Eq a) => [Option i a] -> CPSEnv i a
       -> CPSTerm i a
options []         env = Raise
options (o : os) env = (option o env) (options os env)

option :: (Eq i, Eq a) => Option i a -> CPSEnv i a
       -> CPSOption i a
option (lhs :-> rhs) env = \os q -> (comatch lhs rhs env) q os q

comatch :: (Eq a, Eq i)
        => Copattern i a -> Term i a -> CPSEnv i a
        -> CPSCopat i a
comatch Nop        rhs env = \_ _   -> (term rhs env)
comatch (x :* lhs) rhs env = \q os -> \case
  (y :* k) -> (comatch lhs rhs ((x, useArg y) : env)) q os k
  Nop      -> Under $ (comatch (x :* lhs) rhs env) q os
  _        -> os q
comatch (i :@ lhs) rhs env = \q os -> \case
  (j :@ k) | i == j -> (comatch lhs rhs env) q os k
  Nop               -> Under $ (comatch (i :@ lhs) rhs env) q os
  _                 -> os q
