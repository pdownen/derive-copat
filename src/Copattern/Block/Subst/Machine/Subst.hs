{-# LANGUAGE LambdaCase #-}
module Copattern.Block.Subst.Machine.Subst where
import Copattern.Block.Syntax

data Answer i a
  = Under (TermEnv i a) (Copattern i a) (Term i a) [Option i a]
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval = flip refocus Nop

refocus :: (Eq i, Eq a) => Term i a
        -> Question i a -> Answer i a
refocus (Var x)   = Stuck x
refocus (Dot m)   = \k -> refocus m $ m :* k
refocus (Obj eqs) = select eqs
refocus (m :*: n) = \k -> refocus m $ n :* k
refocus (m :@: i) = \k -> refocus m $ i :@ k

select :: (Eq i, Eq a) => [Option i a]
       -> Question i a -> Answer i a
select []         = Raise
select (eq : eqs) = equate eq eqs

equate :: (Eq i, Eq a) => Option i a
       -> [Option i a] -> Question i a -> Answer i a
equate (lhs :-> rhs) = \eqs q -> comatch lhs [] rhs q eqs q

comatch :: (Eq i, Eq a) => Copattern i a -> TermEnv i a -> Term i a
        -> Question i a -> [Option i a]
        -> Question i a -> Answer i a
comatch Nop        env rhs = \_ _   -> refocus (rhs // env)
comatch (x :* lhs) env rhs = \q eqs -> \case
  (y :* k) -> comatch lhs ((x,y) : env) rhs q eqs k
  Nop      -> Under env lhs rhs eqs
  _        -> select eqs q
comatch (i :@ lhs) env rhs = \q eqs -> \case
  (j :@ k) | i == j -> comatch lhs env rhs q eqs k
  Nop               -> Under env lhs rhs eqs
  _                 -> select eqs q
