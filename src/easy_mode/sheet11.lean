/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet10


notation `myrat` := quotient t

attribute [instance] t

namespace «myrat»

lemma equiv_def (r s : int_plane_non_zero) : 
r ≈ s ↔ r.1 * s.2 = s.1 * r.2 := 
begin
  sorry
end 

def neg : myrat → myrat := quotient.map (λ (r : int_plane_non_zero), (⟨-r.1, r.2, r.non_zero⟩ : int_plane_non_zero)) 
begin
  sorry
end

instance : has_neg myrat :=
{ neg := neg }

def add : myrat → myrat → myrat := quotient.map₂ (λ (r s : int_plane_non_zero), 
(⟨r.1*s.2+r.2*s.1, r.2*s.2, mul_ne_zero r.non_zero s.non_zero⟩: int_plane_non_zero))
begin
  sorry
end

instance : has_add myrat :=
{ add := add }

def mul : myrat → myrat → myrat := quotient.map₂ (λ (r s : int_plane_non_zero), 
(⟨r.1*s.1, r.2*s.2, mul_ne_zero r.non_zero s.non_zero⟩ : int_plane_non_zero))
begin
  sorry
end

instance : has_mul myrat :=
{ mul := mul }

/- Let's try to prove that `myrat` together with these operations forms a commutative ring. -/
instance comm_ring : comm_ring myrat :=
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
}

lemma one_def : (1 : myrat) = ⟦⟨1,1,by linarith⟩⟧ := rfl 

lemma zero_def : (0 : myrat) = ⟦⟨0,1,by linarith⟩⟧ := rfl

/- But we know that even better, the non-zero rational numbers have an inverse, i.e. the rational numbers 
  form a field. Let's try to prove that. -/

instance : has_inv myrat :=
{ inv := quotient.map (λ x : int_plane_non_zero, (if h : x.1 = 0 then (⟨0,1,by linarith⟩) else ⟨x.2, x.1, h⟩ : int_plane_non_zero)) 
begin
sorry
/- `split_ifs` could be a convenient tactic to use at some point -/ ,
end }

instance : field myrat :=
{ inv := has_inv.inv,
  exists_pair_ne := begin sorry end,
  mul_inv_cancel := begin sorry end,
  inv_zero := begin sorry end, 
  .. myrat.comm_ring }



end «myrat»



