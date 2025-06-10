module Copattern.Block.Env.Decomp where
import Copattern.Block.Syntax
import Copattern.Block.Env.Reduce

data Decomp i a
  = Asked (Redex i a) (ClosQuestion i a)
  deriving (Show)

recomp :: Term i a -> Question i a -> Term i a
recomp = ask

-- Lemma:
--
--     decomp (m :/: env) = Ask r (fmap (:/: env) q)
--       where (Ask r q) = Subst.Decomp.decomp m
--
--     Subst.Decomp.decomp m = Ask r (fmap openTerm q)
--       where (Ask r q) = decomp (m :/: _)

decomp :: Closure i a -> Decomp i a
decomp m = refocus m Nop

refocus :: Closure i a -> ClosQuestion i a -> Decomp i a
refocus (Var x :/: env)   k = Asked (FreeVar x env) k
refocus (Dot m :/: env)   k = Asked (Introspect m env) k
refocus (Obj ops :/: env) k = Asked (Respond ops env) k
refocus (m :*: n :/: env) k = refocus (m :/: env) $ (n :/: env) :* k
refocus (m :@: i :/: env) k = refocus (m :/: env) $ i :@ k
