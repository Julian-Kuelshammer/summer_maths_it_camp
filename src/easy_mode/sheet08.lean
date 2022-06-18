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

/-

If you need a bit more practice, here is a slightly more general situation. Given an 
equivalence relation on a type Y and a function f : X → Y, there is an equivalence relation 
on X, pulled back from Y, given by two elements of X being related iff there images under 
f are related. What we did up until now on this sheet is a special case where the equivalence 
relation on Y is given by equality. 

-/

def fun_rel.to_rel {X Y : Type} (S : Y → Y → Prop) (f : X → Y) 
  (x1 x2 : X) : Prop :=
S (f x1) (f x2)

lemma fun_rel.to_rel_def {X Y : Type} (S : Y → Y → Prop) (f : X → Y) 
(x_1 x_2 : X) : (fun_rel.to_rel S f) x_1 x_2 ↔ S (f x_1) (f x_2) :=
begin
  refl,
end

lemma fun_rel.to_rel_refl {X Y : Type} {S : Y → Y → Prop} (hS : reflexive S) (f : X → Y) : 
  reflexive (fun_rel.to_rel S f) :=
begin
  intro x,
  rw fun_rel.to_rel_def,
  exact hS (f x),
end

lemma fun_rel.to_rel_symm {X Y : Type} {S : Y → Y → Prop} (hS : symmetric S) (f : X → Y) : 
  symmetric (fun_rel.to_rel S f) :=
begin
  intros x x' hxx',
  rw fun_rel.to_rel_def at *,
  exact hS hxx',
end

lemma fun_rel.to_rel_trans {X Y : Type} {S : Y → Y → Prop} (hS : transitive S) (f : X → Y) : 
  transitive (fun_rel.to_rel S f) :=
begin
  intros x x' x'' hxx' hx'x'',
  rw fun_rel.to_rel_def at *,
  exact hS hxx' hx'x'',
end

lemma fun_rel.to_rel_equiv {X Y : Type} {S : Y → Y → Prop} (hS : equivalence S) (f : X → Y) : 
  equivalence (fun_rel.to_rel S f) :=
begin
  exact ⟨fun_rel.to_rel_refl hS.1 f, fun_rel.to_rel_symm hS.2.1 f, fun_rel.to_rel_trans hS.2.2 f⟩,
end

instance fun_rel.to_setoid {X Y : Type} {S : Y → Y → Prop} (hS : equivalence S) (f : X → Y) : 
  setoid X :=
{ r := fun_rel.to_rel S f,
  iseqv := fun_rel.to_rel_equiv hS f }


/- 

And here is another situation which we will encounter soon. Given an equivalence relation R on 
X and an equivalence relation S on Y, there is an equivalence relation on X × Y in which 
two pairs are related if and only if there first and second entry are related. 


-/

def prod_rel {X Y : Type} (R : X → X → Prop) (S : Y → Y → Prop) 
  (u v : X × Y) : Prop :=
R u.1 v.1 ∧ S u.2 v.2

lemma prod_rel_def {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop} (u v : X × Y) :
  prod_rel R S u v ↔ R u.1 v.1 ∧ S u.2 v.2 := 
begin 
  sorry
end

lemma prod_rel_refl {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop} (hR : reflexive R)
  (hS : reflexive S) : reflexive (prod_rel R S) :=
begin 
  sorry
end

lemma prod_rel_symm {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop} (hR : symmetric R)
  (hS : symmetric S) : symmetric (prod_rel R S) :=
begin
  sorry
end

lemma prod_rel_trans {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop} (hR : transitive R)
  (hS : transitive S) : transitive (prod_rel R S) :=
begin
  sorry
end

lemma prod_rel_equiv {X Y : Type} {R : X → X → Prop} {S : Y → Y → Prop} (hR : equivalence R)
  (hS : equivalence S) : equivalence (prod_rel R S) :=
begin
  sorry 
end
