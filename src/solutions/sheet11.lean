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
  linear_combination u2 * v2 * hrs + s2 * r2 * huv,
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

/- Let's try to prove that `myrat` together with these operations forms a commutative ring. -/
instance comm_ring : comm_ring myrat :=
{ add := has_add.add,
  add_assoc := begin intros r s t, apply quotient.induction_on₃ r s t, clear r s t, 
    rintros ⟨x1, x2, _⟩ ⟨y1, y_2, _⟩ ⟨z1, z2, _⟩, apply quotient.sound, rw equiv_def, dsimp, nlinarith, end,
  zero := ⟦⟨0,1,by linarith⟩⟧,
  zero_add := begin intro r, apply quotient.induction_on r, clear r, rintro ⟨x1, x2, _⟩, apply quotient.sound, 
    rw equiv_def, simp, end,
  add_zero := begin intro r, apply quotient.induction_on r, clear r, rintro ⟨x1, x2, _⟩, apply quotient.sound, 
    rw equiv_def, simp, end,
  neg := has_neg.neg,
  add_left_neg := begin intro r, apply quotient.induction_on r, clear r, rintro ⟨x1, x2, _⟩, 
    apply quotient.sound, rw equiv_def, dsimp, ring, end,
  add_comm := begin intros r s, apply quotient.induction_on₂ r s, clear r s, rintros ⟨x1, x2, _⟩
    ⟨y1, y2, _⟩, apply quotient.sound, rw equiv_def, ring_nf, end,
  mul := has_mul.mul,
  mul_assoc := begin intros r s t, apply quotient.induction_on₃ r s t, clear r s t, 
    rintros ⟨x1, x2, _⟩ ⟨y1, y2, _⟩ ⟨z1, z2, _⟩, apply quotient.sound, rw equiv_def, dsimp, ring, end,
  one := ⟦⟨1,1,by linarith⟩⟧,
  one_mul := begin intro r, apply quotient.induction_on r, clear r, rintro ⟨x1, x2, _⟩, apply quotient.sound,
    rw equiv_def, simp, end,
  mul_one := begin intro r, apply quotient.induction_on r, clear r, rintro ⟨x1, x2, _⟩, apply quotient.sound,
    rw equiv_def, simp, end,
  left_distrib := begin intros r s t, apply quotient.induction_on₃ r s t, clear r s t, rintros ⟨x1, x2, _⟩ 
    ⟨y1, y2, _⟩ ⟨z1, z2, _⟩, apply quotient.sound, rw equiv_def, ring_nf, end,
  right_distrib := begin intros r s t, apply quotient.induction_on₃ r s t, clear r s t, rintros ⟨x1, x2, _⟩ 
    ⟨y1, y2, _⟩ ⟨z1, z2, _⟩, apply quotient.sound, rw equiv_def, ring_nf, end,
  mul_comm := begin intros r s, apply quotient.induction_on₂ r s, clear r s, rintros ⟨x1, x2, _⟩ 
    ⟨y1, y2, _⟩, apply quotient.sound, rw equiv_def, ring_nf, end,
}

lemma one_def : (1 : myrat) = ⟦⟨1,1,by linarith⟩⟧ := rfl 

lemma zero_def : (0 : myrat) = ⟦⟨0,1,by linarith⟩⟧ := rfl

/- But we know that even better, the non-zero rational numbers have an inverse, i.e. the rational numbers 
  form a field. Let's try to prove that. -/

instance : has_inv myrat :=
{ inv := quotient.map (λ x : int_plane_non_zero, (if h : x.1 = 0 then (⟨0,1,by linarith⟩) else ⟨x.2, x.1, h⟩ : int_plane_non_zero)) 
begin
rintros ⟨r1, r2, r_non_zero⟩ ⟨s1, s2, s_non_zero⟩ hrs,
rw equiv_def at hrs,
dsimp at *,
split_ifs,
{ refl },
{ exfalso, 
  simp [h] at hrs,
  cases hrs,
  { apply h_1, exact hrs, },
  { apply r_non_zero, exact hrs } },
{ exfalso, 
  simp [h_1] at hrs,
  cases hrs,
  { apply h, exact hrs, },
  { apply s_non_zero, exact hrs } },
{ rw equiv_def,
  dsimp,
  rw [mul_comm, ← hrs, mul_comm] },
end }

instance : field myrat :=
{ inv := has_inv.inv,
  exists_pair_ne := begin use ⟦⟨0,1,by linarith⟩⟧, use ⟦⟨1,1,by linarith⟩⟧, by_contradiction, rw quotient.eq at h, rw equiv_def at h, simp at h, exact h end,
  mul_inv_cancel := begin rintros r hr, cases quotient.exists_rep r, rw ← h at *, rw zero_def at hr,
    apply quotient.sound, dsimp, split_ifs,
    { rw equiv_def, exfalso, apply hr, apply quotient.sound, rw equiv_def, simp [h_1] },
    { rw equiv_def, simp only [mul_one, one_mul], exact mul_comm _ _, }, end,
  inv_zero := rfl, 
  .. myrat.comm_ring }



end «myrat»



