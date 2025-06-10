{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Machine.Denote where
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

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

data CPSVar i a = Name a | Subs (CPSTerm i a)

instance Eq a => Eq (CPSVar i a) where
  Name x == Name y = x == y
  _      == _      = False

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = (refocus (fmap Name m)) Nop

refocus :: (Eq i, Eq a) => Term i (CPSVar i a) -> CPSTerm i a
refocus (Var (Name x)) = Stuck x
refocus (Var (Subs m)) = m
refocus (Dot m)        = \k -> (refocus m) (Arg (refocus m) :* k)
refocus (Obj ops)      = select ops
refocus (m :*: n)      = \k -> (refocus m) (Arg (refocus n) :* k)
refocus (m :@: i)      = \k -> (refocus m) (i :@ k)

select :: (Eq i, Eq a) => [Option i (CPSVar i a)] -> CPSTerm i a
select []         = Raise
select (op : ops) = (option op) (select ops)

option :: (Eq i, Eq a) => Option i (CPSVar i a) -> CPSOption i a
option (lhs :-> rhs) = \ops q -> (comatch lhs rhs) q ops q

comatch :: (Eq i, Eq a)
        => Copattern i (CPSVar i a) -> Term i (CPSVar i a)
        -> CPSCopat i a
comatch Nop        rhs = \_ _   -> (refocus rhs)
comatch (x :* lhs) rhs = \q ops -> \case
  (y :* k) -> (comatch lhs (rhs // [(x, n)])) q ops k
    where n = Var (Subs (useArg y))
  Nop      -> Under $ (comatch (x :* lhs) rhs) q ops
  _        -> ops q
comatch (i :@ lhs) rhs = \q ops -> \case
  (j :@ k) | i == j -> (comatch lhs rhs) q ops k
  Nop               -> Under $ (comatch (i :@ lhs) rhs) q ops
  _                 -> ops q
