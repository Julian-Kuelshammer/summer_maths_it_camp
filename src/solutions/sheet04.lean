/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import solutions.sheet03

/- Showing minimality

This sheet is a bonus sheet. Its purpose is to provide a formalisation of the fact
that you can write down structures which satisfy only five out of the six minimal vector space axioms. 
I give a blueprint for the easiest of the six options. Feel free to try as many as you like. 
Doing this more seriously could even be a project. 

In case you want some hints here, take a look at: https://doi.org/10.2307/3615171

-/

class almost_minimal_wo_one_smul (V : Type)
  extends has_add V, has_scalar ℝ V : Type :=
(add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w))
(zero_smul_eq : ∀ v w : V, (0 : ℝ) • v = (0 : ℝ) • w)
(smul_assoc : ∀ (a b : ℝ) (v : V), (a * b) • v = a • (b • v))
(add_smul : ∀ (a b : ℝ) (v : V), (a + b) • v = a • v + b • v)
(smul_add : ∀ (a : ℝ) (v w : V), a • (v + w) = a • v + a • w)

instance : almost_minimal_wo_one_smul ℝ :=
{ add := λ v w, v + w,
  smul := λ a v, (0 : ℝ),
  add_assoc := add_assoc,
  zero_smul_eq := begin simp end,
  smul_assoc := begin intros a b v, refl,  end,
  add_smul := begin intros a b v, simp only [add_zero],  end,
  smul_add := begin intros a v w, simp only [add_zero], end }
