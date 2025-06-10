{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Machine.Eta where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

refocus :: (Eq i, Eq a) => Term i a
        -> Question i a -> Answer i a
refocus (Var x)   = Stuck x
refocus (Dot m)   = \k -> refocus m $ m :* k
refocus (Obj ops) = select ops
refocus (m :*: n) = \k -> refocus m $ n :* k
refocus (m :@: i) = \k -> refocus m $ i :@ k

select :: (Eq i, Eq a) => [Option i a]
       -> Question i a -> Answer i a
select []         = Raise
select (op : ops) = option op ops

option :: (Eq i, Eq a) => Option i a
       -> [Option i a] -> Question i a -> Answer i a
option (lhs :-> rhs) = \ops q -> comatch lhs rhs q ops q

comatch :: (Eq i, Eq a) => Copattern i a -> Term i a
        -> Question i a -> [Option i a]
        -> Question i a -> Answer i a
comatch Nop        rhs = \_ _   -> refocus rhs
comatch (x :* lhs) rhs = \q ops -> \case
  (y :* k) -> comatch lhs (rhs // [(x,y)]) q ops k
  Nop      -> Under (x :* lhs) rhs ops q
  _        -> select ops q
comatch (i :@ lhs) rhs = \q ops -> \case
  (j :@ k) | i == j -> comatch lhs rhs q ops k
  Nop               -> Under (i :@ lhs) rhs ops q
  _                 -> select ops q
