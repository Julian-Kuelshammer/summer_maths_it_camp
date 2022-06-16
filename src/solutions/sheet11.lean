/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import solutions.sheet10


notation `myrat` := quotient t

attribute [instance] t

namespace «myrat»

lemma equiv_def (r s : int_plane_non_zero) : 
r ≈ s ↔ r.1 * s.2 = s.1 * r.2 := 
begin
  refl
end 

def neg : myrat → myrat := quotient.map (λ (r : int_plane_non_zero), (⟨-r.1, r.2, r.non_zero⟩ : int_plane_non_zero)) 
begin
  intros r s hrs,
  rw [equiv_def] at *,
  dsimp,
  linarith,
end

instance : has_neg myrat :=
{ neg := neg }

def add : myrat → myrat → myrat := quotient.map₂ (λ (r s : int_plane_non_zero), 
(⟨r.1*s.2+r.2*s.1, r.2*s.2, mul_ne_zero r.non_zero s.non_zero⟩: int_plane_non_zero))
begin
  rintros ⟨r1, r2, _⟩ ⟨s1, s2, _⟩ hrs,
  rintros ⟨u1, u2, _⟩ ⟨v1, v2, _⟩ huv,
  rw [equiv_def] at *,
  dsimp at *,
  clear a_non_zero b_non_zero a_non_zero_1 b_non_zero_1,
  rw [add_mul, add_mul],
  rw [← mul_assoc, mul_assoc r1, mul_comm u2, ← mul_assoc, hrs],
  rw [← mul_assoc, mul_assoc r2, mul_comm u1, mul_assoc r2, mul_assoc s2, huv],
  linarith,
end

instance : has_add myrat :=
{ add := add }

def mul : myrat → myrat → myrat := quotient.map₂ (λ (r s : int_plane_non_zero), 
(⟨r.1*s.1, r.2*s.2, mul_ne_zero r.non_zero s.non_zero⟩ : int_plane_non_zero))
begin
  rintros ⟨r1, r2, _⟩ ⟨s1, s2, _⟩ hrs,
  rintros ⟨u1, u2, _⟩ ⟨v1, v2, _⟩ huv,
  rw [equiv_def] at *,
  dsimp at *,
  clear a_non_zero b_non_zero a_non_zero_1 b_non_zero_1,
  rw [← mul_assoc, mul_assoc r1, mul_comm u1, ← mul_assoc, hrs, mul_assoc, mul_assoc, huv],
  linarith,
end

instance : has_mul myrat :=
{ mul := mul }

instance : has_inv myrat :=
{ inv := neg }

instance : has_div myrat := 
{ div := λ x y, x * y⁻¹}

instance : field myrat :=
{ add := has_add.add,
  add_assoc := begin sorry end,
  zero := ⟦⟨0,1,by linarith⟩⟧,
  zero_add := begin sorry end,
  add_zero := begin sorry end,
  neg := has_neg.neg,
  add_left_neg := begin sorry end,
  add_comm := begin sorry end,
  mul := has_mul.mul,
  mul_assoc := begin sorry end,
  one := ⟦⟨1,1,by linarith⟩⟧,
  one_mul := begin sorry end,
  mul_one := begin sorry end,
  left_distrib := begin sorry end,
  right_distrib := begin sorry end,
  mul_comm := begin sorry end,
  inv := has_inv.inv,
  div := has_div.div,
  exists_pair_ne := begin sorry end,
  mul_inv_cancel := begin sorry end,
  inv_zero := begin sorry end,
}


end «myrat»



