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

def neg : myrat → myrat := _
begin
  sorry
end

instance : has_neg myrat :=
{ neg := neg }

def add : myrat → myrat → myrat := _

instance : has_add myrat :=
{ add := add }

def mul : myrat → myrat → myrat := _

instance : has_mul myrat :=
{ mul := mul }

/- Let's try to prove that `myrat` together with these operations forms a commutative ring. -/
instance comm_ring : comm_ring myrat :=
_
/- But we know that even better, the non-zero rational numbers have an inverse, i.e. the rational numbers 
  form a field. Let's try to prove that. -/

instance : has_inv myrat :=
_

instance : field myrat :=
_



end «myrat»



