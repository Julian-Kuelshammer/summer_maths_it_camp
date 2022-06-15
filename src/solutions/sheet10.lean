/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import solutions.sheet09

/-

# Induced functions on quotients

The quotient comes with what one would call a universal property in advanced courses: Given a type `X`, an 
equivalence relation `≈` on `X`, then for every other type `Y` and every function `h : X → Y` such that 
`x ≈ x' → f x = f x'` there is a unique function `h : X/≈  → Y` such that `f = h ∘ q`. In standard maths courses 
the existence of such `h` in examples is often justified as follows: For each equivalence class `⟦x⟧` of 
the quotient, choose a representative `x : X` and define `h(⟦x⟧) := f(x)`. One has to then prove that this 
is well-defined by invoking the assumption `x ≈ x' → f x = f x'`. In Lean, the function `h` can be produced 
automatically using `quotient.lift` applied to the assumption `x ≈ x' → f x = f x'`, one doesn't have to go 
through the steps. 

On this sheet we will see how this works, first starting with the example of negation, which is easier than 
addition as it only has one input, not two. 
-/



lemma neg_well_defined (x y : nat_plane) (h : x ≈ y) : ⟦(⟨x.2,x.1⟩ : nat_plane)⟧ = ⟦⟨y.2, y.1⟩⟧ :=
begin
  apply quotient.sound,
  rw [equiv_def, R_def] at *,
  rw [add_comm, ← h, add_comm],
end

def neg : myint → myint := quotient.lift (λ (x : nat_plane), ⟦(⟨x.2, x.1⟩ : nat_plane)⟧) (neg_well_defined)

instance : has_neg myint :=
{ neg := neg }

/- 

There is an alternative way, which is in fact a special case of the first. Suppose `Y = Z/≈₂` and we are given 
a function `g : X → Z`. Consider the function `f = q₂ ∘ g` where `q₂ : Z → Z/≈₂` is the surjection.  
Then `x ≈ x' → f x = f x'` can be checked on `Z` instead, i.e. it can be checked that `x ≈ x' → g x ≈₂ g x'`
in order to reach the conclusion for `f`. Since this is a common situation, there is a special name for it: 
`quotient.map`, which takes the assumption `x ≈ x' → g x ≈₂ g x'` and defines a function `X/≈ → Z/≈₂`.

-/

def neg2 : myint → myint := quotient.map (λ x, ⟨x.2, x.1⟩) 
begin 
  intros x y hxy,
  rw [equiv_def, R_def] at *,
  rw [add_comm, ← hxy, add_comm],
end

/- Why do the two definitions just defined agree? -/
lemma defn_neg_agree : neg = neg2 :=
begin
  sorry
end

