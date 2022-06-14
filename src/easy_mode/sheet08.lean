/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet07

/-

# A general way to produce equivalence relations

There is some general way to produce an equivalence relation from a function: Given a 
function `f : X → Y`, one can define `x_1 ≈ x_2` iff `f (x_1) = f(x_2)`. One can even 
assume the function `f` to be surjective, i.e. there exists a `Z` and a surjective 
function `g : X → Z` such that `x_1 ≈ x_2` iff `g (x_1) = g(x_2)`. Let's try to prove 
this in Lean.

-/

def function.to_rel {X Y : Type} (f : X → Y) (x_1 x_2 : X) : Prop :=
f x_1 = f x_2

lemma function.to_rel_def {X Y : Type} (f : X → Y) (x_1 x_2 : X) :
(function.to_rel f) x_1 x_2 ↔ f x_1 = f x_2 :=
begin
  sorry
end

lemma function.to_rel_refl {X Y : Type} (f : X → Y) : reflexive (function.to_rel f) :=
begin
  sorry
end

lemma function.to_rel_symm {X Y : Type} (f : X → Y) : symmetric (function.to_rel f) :=
begin
  sorry
end

lemma function.to_rel_trans {X Y : Type} (f : X → Y) : transitive (function.to_rel f) :=
begin
  sorry
end

lemma function.to_rel_equiv {X Y : Type} (f : X → Y) : equivalence (function.to_rel f) :=
begin
  sorry
end

instance function.to_setoid {X Y : Type} (f : X → Y) : setoid X :=
{ r := function.to_rel f,
  iseqv := function.to_rel_equiv f }

lemma exists_surjective {X Y : Type} (f : X → Y) : ∃ (Z : Type) (g : X → Z), 
function.surjective g ∧ ∀ x x' : X, f x = f x' ↔ g x = g x' :=
begin
  sorry
end

