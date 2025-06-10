module Copattern.Block.Subst.Step.Corridor where
import Copattern.Block.Syntax

data Answer i a
  = Under (Copattern i a) (Term i a) [Option i a] (Question i a)
  | Raise (Question i a)
  | Stuck a (Question i a)
  deriving (Show)

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m Nop

iter :: (Eq i, Eq a) => Decomp i a -> Answer i a
iter (Asked r q) = reduce r q

continue :: (Eq i, Eq a) => Followup i a -> Answer i a
continue (Next (Reduced m) k) = refocus m k
continue (Next (Unknown x) k) = Stuck x k
continue (Next Unhandled   k) = Raise k
continue (More lhs rhs eqs k) = Under lhs rhs eqs k



data Decomp i a
  = Asked (Redex i a) (Question i a)
  deriving (Show)

refocus :: (Eq i, Eq a)
        => Term i a -> Copattern i (Term i a)
        -> Answer i a
refocus (Var x)   k = Stuck x k
refocus (Dot m)   k = refocus m $ m :* k
refocus (Obj eqs) k = reduce (Respond eqs) k
refocus (m :*: n) k = refocus m $ n :* k
refocus (m :@: i) k = refocus m $ i :@ k



data Redex i a
  = Introspect (Term i a)
  | Respond [Option i a]
  | FreeVar a
  deriving (Show)

data Reduct i a
  = Reduced (Term i a)
  | Unhandled
  | Unknown a
  deriving (Show)

data Followup i a
  = Next (Reduct i a) (Question i a)
  | More (Copattern i a) (Term i a) [Option i a] (Question i a)
  deriving (Show)

reduce :: (Eq i, Eq a) => Redex i a -> Question i a -> Answer i a
reduce (Introspect m)                q = refocus m $ m :* q
reduce (FreeVar x)                   q = Stuck x q
reduce (Respond (lhs :-> rhs : eqs)) q = comatch lhs q $ ComatchCxt [] (rhs, eqs, q)
reduce (Respond [])                  q = Raise q

data CoMatchCxt i a
  = ComatchCxt { bind :: TermEnv i a,
                 base :: (Term i a, [Option i a], Question i a) }

comatch :: (Eq i, Eq a)
        => Copattern i a -> Question i a
        -> CoMatchCxt i a -> Answer i a
comatch Nop        cxt        k = refocus (rhs // env) cxt
  where (ComatchCxt env (rhs, _, _)) = k 
comatch lhs        Nop        k = Under lhs (rhs // env) eqs q
  where (ComatchCxt env (rhs, eqs, q)) = k
comatch (x :* lhs) (y :* cxt) k = comatch lhs cxt $ k{ bind = (x,y) : bind k }
comatch (i :@ lhs) (j :@ cxt) k
  | i == j                      = comatch lhs cxt k
comatch lhs        cxt        k = reduce (Respond eqs) q
  where (ComatchCxt env (_, eqs, q)) = k
