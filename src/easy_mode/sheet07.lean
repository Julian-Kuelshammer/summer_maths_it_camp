/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import data.int.basic

/- 
# Quotients in Lean 

Upon request, let's try to see how to construct number systems like the integers or the 
rational numbers in Lean. Note that this is again some mathematical way to do this, not the 
actual way, e.g. integers are defined as the disjoint union of ℕ with itself, where the first 
copy is interpreted as the usual natural numbers while the second copy is interpreted as the 
numbers `1-n` where `n : ℕ`. Similarly, ℚ is contructed as pairs of coprime integers (p,q). 
This makes them computationally a bit better behaved than our quotient way. 

## Equivalence relations in Lean

Lean knows what an equivalence relation is. It is a reflexive, symmetric and transitive relation. 
A relation on a set `X` is a function `X → X → Prop`, i.e. a function that takes two elements 
of a set `X` and outputs a truth value depending whether they are related or not. 

```
def reflexive := ∀ x, x ∼ x

def symmetric := ∀ ⦃x y⦄, x ∼ y → y ∼ x

def transitive := ∀ ⦃x y z⦄, x ∼ y → y ∼ m z → x ∼ z

def equivalence := reflexive r ∧ symmetric r ∧ transitive r
```

-/

def R (r s : ℕ × ℕ) : Prop := 
r.1+s.2=s.1+r.2

lemma R_def (r s : ℕ × ℕ) :
R r s ↔ r.1 + s.2 = s.1 + r.2 := 
begin
  sorry
end

lemma R_refl : reflexive R :=
begin
  sorry
end

lemma R_symm : symmetric R :=
begin
  sorry
end 

lemma R_trans : transitive R :=
begin
  /- The lemma add_right_inj could be helpful at some point. -/
  sorry
end 

lemma R_equiv : equivalence R :=
begin 
  sorry
end


/- A setoid on a Type is a relation together with the fact that 
  this relation is an equivalence relation. -/
instance s : setoid (ℕ × ℕ) :=
_

structure int_plane_non_zero :=
(fst : ℤ) (snd : ℤ) (non_zero : snd ≠ 0)

def S (r s : int_plane_non_zero) : Prop :=
r.1 * s.2 = s.1 * r.2

lemma S_def (r s : int_plane_non_zero) : 
S r s ↔ r.1 * s.2 = s.1 * r.2 :=
begin
  sorry
end

lemma S_refl : reflexive S :=
begin
  sorry
end

lemma S_symm : symmetric S :=
begin
  sorry
end

lemma S_trans : transitive S :=
begin
  /- The following lemma would be helpful at some point: mul_right_inj' -/
  sorry
end 

lemma S_equiv : equivalence S := 
begin 
  sorry
end

instance t : setoid (int_plane_non_zero) :=
_