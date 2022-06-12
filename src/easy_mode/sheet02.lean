/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet01

/-! Two-by-two matrices

This file defines two-by-two matrices and shows that they form a vector space.
-/

/- Here is one way to define a 2x2 matrix, via specifying its two rows. In hard mode you could try to take a 
  different approach (either as its two columns or as its four entries and see what gets easier and what gets 
  harder). -/
structure two_matrix : Type :=
(fst_row : ℝ²) 
(snd_row : ℝ²)

namespace two_matrix

notation `Mat₂` := two_matrix

/-- Two matrices are equal if and only if their first and second rows coincide. -/
@[ext] theorem ext {A B : Mat₂}
  (h_first_row : A.fst_row = B.fst_row ) 
  (h_second_row : A.snd_row = B.snd_row ) : 
  A = B :=
begin
  sorry
end

/- Again we want to be able to write `A + B` if `A` and `B` are matrices without too complicated notation. -/
instance : has_add Mat₂ := ⟨λ A B, ⟨A.fst_row + B.fst_row, A.snd_row + B.snd_row⟩⟩

@[simp] lemma add_fst_row (A B : Mat₂) : (A + B).fst_row = A.fst_row + B.fst_row := sorry
@[simp] lemma add_snd_row (A B : Mat₂) : (A + B).snd_row = A.snd_row + B.snd_row := sorry

lemma add_assoc (A B C : Mat₂) : A + B + C = A + (B + C) :=
begin
  sorry
end

lemma add_comm (A B : Mat₂) : A + B = B + A :=
begin
  sorry
end

def zero_matrix : Mat₂ := ⟨0,0⟩

/- We even want to be able to write `0` for the zero matrix.-/
instance : has_zero Mat₂ := ⟨zero_matrix⟩ 

/- The following lemmas have each two zeros in them, see which is which. -/
@[simp] lemma zero_fst_row : (0 : Mat₂).fst_row = 0 := sorry
@[simp] lemma zero_snd_row : (0 : Mat₂).snd_row = 0 := sorry

@[simp] lemma add_zero (A : Mat₂) : A + 0 = A :=
begin
  sorry
end

@[simp] lemma zero_add (A : Mat₂) : 0 + A = A :=
begin
  sorry
end

/- We want to define the negation of a matrix. -/
instance : has_neg Mat₂ := ⟨λ A, ⟨-A.fst_row, -A.snd_row⟩⟩

@[simp] lemma neg_fst_row (A : Mat₂) : (-A).fst_row = -A.fst_row := sorry
@[simp] lemma neg_snd_row (A : Mat₂) : (-A).snd_row = -A.snd_row := sorry


@[simp] lemma add_neg_self (A : Mat₂) : A + -A = 0 :=
begin
  sorry
end 

@[simp] lemma neg_add_self (A : Mat₂) : -A + A = 0 :=
begin
  sorry
end

/- Finally we set up subtraction and scalar multiplication of matrices. -/
instance : has_sub Mat₂ := ⟨λ A B, A + (-B)⟩

instance : has_scalar ℝ Mat₂ := ⟨λ a A, ⟨a • A.fst_row, a • A.snd_row⟩⟩ 

@[simp] lemma smul_fst_row (a : ℝ) (A : Mat₂) : (a • A).fst_row = a • A.fst_row := sorry
@[simp] lemma smul_snd_row (a : ℝ) (A : Mat₂) : (a • A).snd_row = a • A.snd_row := sorry

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