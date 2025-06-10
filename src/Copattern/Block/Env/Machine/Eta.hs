{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Env.Machine.Eta where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Closure i a) [Option i a] (ClosEnv i a) (ClosQuestion i a)
  | Raise (ClosQuestion i a)
  | Stuck a (ClosQuestion i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m [] Nop

refocus :: (Eq i, Eq a) => Term i a -> ClosEnv i a
        -> ClosQuestion i a -> Answer i a
refocus (Var x)   env = case lookup x env of
  Nothing           -> Stuck x
  Just (m :/: env)  -> refocus m env
refocus (Dot m)   env = \k -> refocus m env $ (m :/: env) :* k
refocus (Obj ops) env = select ops env
refocus (m :*: n) env = \k -> refocus m env $ (n :/: env) :* k
refocus (m :@: i) env = \k -> refocus m env $ i :@ k

select :: (Eq i, Eq a) => [Option i a] -> ClosEnv i a
       -> ClosQuestion i a -> Answer i a
select []         env = Raise
select (op : ops) env = option op env ops

option :: (Eq i, Eq a) => Option i a -> ClosEnv i a
       -> [Option i a] -> ClosQuestion i a -> Answer i a
option (lhs :-> rhs) env = \ops q -> comatch lhs rhs [] env q ops q

comatch :: (Eq a, Eq i)
        => Copattern i a -> Term i a -> ClosEnv i a -> ClosEnv i a
        -> ClosQuestion i a -> [Option i a]
        -> ClosQuestion i a -> Answer i a
comatch Nop        rhs env' env = \_ _   -> refocus rhs (env' ++ env)
comatch (x :* lhs) rhs env' env = \q ops -> \case
  (y :* k) -> comatch lhs rhs ((x,y):env') env q ops k
  Nop      -> Under (x :* lhs) (rhs :/: env') ops env q
  _        -> select ops env q
comatch (i :@ lhs) rhs env' env = \q ops -> \case
  (j :@ k) | i == j -> comatch lhs rhs env' env q ops k
  Nop               -> Under (i :@ lhs) (rhs :/: env') ops env q
  _                 -> select ops env q

