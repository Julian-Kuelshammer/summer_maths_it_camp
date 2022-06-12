/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet01

/-! Two-by-two matrices

This file defines two-by-two matrices and shows that they form a vector space.
-/

/- What do you want to be a 2x2-matrix. There are several possible approaches. I put some non-answer here to 
  make Lean stop complaining, replace it with a correct answer. -/
structure two_matrix : Type :=
(x : ℝ)

namespace two_matrix

notation `Mat₂` := two_matrix

/- Again we want to be able to write `A + B` if `A` and `B` are matrices without too complicated notation. -/
instance : has_add Mat₂ := sorry

lemma add_assoc (A B C : Mat₂) : A + B + C = A + (B + C) :=
begin
  sorry
end

lemma add_comm (A B : Mat₂) : A + B = B + A :=
begin
  sorry
end

def zero_matrix : Mat₂ := sorry

/- We even want to be able to write `0` for the zero matrix.-/
instance : has_zero Mat₂ := ⟨zero_matrix⟩ 

@[simp] lemma add_zero (A : Mat₂) : A + 0 = A :=
begin
  sorry
end

@[simp] lemma zero_add (A : Mat₂) : 0 + A = A :=
begin
  sorry
end

/- We want to define the negation of a matrix. -/
instance : has_neg Mat₂ := sorry

@[simp] lemma add_neg_self (A : Mat₂) : A + -A = 0 :=
begin
  sorry
end 

@[simp] lemma neg_add_self (A : Mat₂) : -A + A = 0 :=
begin
  sorry
end

/- Finally we set up subtraction and scalar multiplication of matrices. -/
instance : has_sub Mat₂ := sorry

instance : has_scalar ℝ Mat₂ := sorry

lemma smul_assoc (a b : ℝ) (A : Mat₂) : (a * b) • A = a • (b • A) :=
begin
  sorry
end 

@[simp] lemma one_smul (A : Mat₂) : (1 : ℝ) • A = A :=
begin
  sorry
end   

@[simp] lemma smul_add (a : ℝ) (A B : Mat₂) : a • (A + B) = a • A + a • B :=
begin
  sorry
end 

@[simp] lemma add_smul (a b : ℝ) (A : Mat₂) : (a + b) • A = a • A + b • A :=
begin
  sorry
end

end two_matrix