{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.CPS.Repeat where
import Copattern.Block.Syntax

data Answer i a
  = Under (CPSTerm i a)
  | Raise (CPSQuestion i a)
  | Stuck a (CPSQuestion i a)

type CPSQuestion i a = Copattern i (CPSArg i a)
type CPSTerm     i a = CPSQuestion i a -> Answer       i a
type CPSOption   i a = CPSTerm     i a -> CPSTerm      i a
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
select []                  = Raise
select (lhs :-> rhs : ops) = (comatch lhs rhs) (select ops)

-- Lemma:
--    (Comp.comatch lhs rhs) (q <> k) ops k
--    =
--    (Redup.comatch lhs rhs) (\k' -> ops (q <> k')) k
-- Proof: By induction on `lhs`, then cases on `k`.

-- Corollary: (Comp.comatch lhs rhs) k ops k = (Redup.comatch lhs hrs) ops k

comatch :: (Eq i, Eq a)
        => Copattern i (CPSVar i a) -> Term i (CPSVar i a)
        -> CPSOption i a
comatch Nop        rhs = \_   -> (refocus rhs)
comatch (x :* lhs) rhs = \ops -> \case
  (y :* k) -> (comatch lhs (rhs // [(x, n)])) (\k' -> ops (y :* k')) k
    where n = Var (Subs (useArg y))
  Nop      -> Under $ (comatch (x :* lhs) rhs) ops
  k        -> ops k
comatch (i :@ lhs) rhs = \ops -> \case
  (j :@ k) | i == j -> (comatch lhs rhs) (\k' -> ops (i :@ k')) k
  Nop               -> Under $ (comatch (i :@ lhs) rhs) ops
  k                 -> ops k
