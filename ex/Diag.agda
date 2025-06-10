module Diag where

record _&_ A B : Set where
  constructor _,_
  field
    Fst : A
    Snd : B
open _&_

{-
ERROR:

Cannot split into projections because not all clauses have a
projection copattern
when checking the definition of diag

diag : ∀ {A B C D} → A → D
     → (A & B) & (C & D) → (A & B) & (C & D)
diag x y z .Fst .Fst = x
diag x y z .Snd .Snd = y
diag x y z = z
-}

diag' : ∀ {A B C D D'} → A → D
      → (A & B) & (C & D) → (A & B) & (C & D)
diag' x y z .Fst .Fst = x
diag' x y z .Snd .Snd = y
diag' x y z .Fst .Snd = z .Fst .Snd
diag' x y z .Snd .Fst = z .Snd .Fst
