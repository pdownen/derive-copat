{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.CPS where
import Copattern.Block.Syntax

data Answer i a
  = Under (CPSTerm i a)
  | Raise (CPSQuestion i a)
  | Stuck a (CPSQuestion i a)

type CPSQuestion i a = Copattern i (CPSArg i a)
type CPSTerm     i a = CPSQuestion i a -> Answer    i a
type CPSOption   i a = CPSTerm     i a -> CPSTerm   i a
type CPSCopat    i a = CPSQuestion i a -> CPSOption i a

newtype CPSArg i a = Arg { useArg :: CPSTerm i a }

data CPSVar i a = Name a | Subs (CPSTerm i a)

instance Eq a => Eq (CPSVar i a) where
  Name x == Name y = x == y
  _      == _      = False

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = (term (fmap Name m)) Nop

term :: (Eq i, Eq a) => Term i (CPSVar i a) -> CPSTerm i a
term (Var (Name x)) = Stuck x
term (Var (Subs m)) = m
term (Dot m)        = \k -> (term m) (Arg (term m) :* k)
term (Obj os)       = options os
term (m :*: n)      = \k -> (term m) (Arg (term n) :* k)
term (m :@: i)      = \k -> (term m) (i :@ k)

options :: (Eq i, Eq a) => [Option i (CPSVar i a)] -> CPSTerm i a
options []                 = Raise
options (lhs :-> rhs : os) = \q -> (comatch lhs rhs) q (options os) q

comatch :: (Eq i, Eq a)
        => Copattern i (CPSVar i a) -> Term i (CPSVar i a)
        -> CPSCopat i a
comatch Nop        rhs = \_ _   -> (term rhs)
comatch (x :* lhs) rhs = \q os -> \case
  (y :* k) -> (comatch lhs (rhs // [(x, n)])) q os k
    where n = Var (Subs (useArg y))
  Nop      -> Under $ (comatch (x :* lhs) rhs) q os
  _        -> os q
comatch (i :@ lhs) rhs = \q os -> \case
  (j :@ k) | i == j -> (comatch lhs rhs) q os k
  Nop               -> Under $ (comatch (i :@ lhs) rhs) q os
  _                 -> os q
