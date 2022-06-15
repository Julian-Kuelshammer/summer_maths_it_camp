/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet02


/-! Real vector spaces

This file defines the concept of a real vector space (as is discussed in the first lecture of Linear Algebra II
and proves that ℝ² and Mat₂ are instances of it.)

One further ingredient could be useful: 

calc expr_1 = expr_2 : begin sorry end
       ...  = expr_3 : begin sorry end
       ...  = expr_4 : begin sorry end

Fun fact: If you only work with calc, you don't have to switch to tactic mode, i.e. you can leave out the 
begin ... end

rw : rewrite one expression by another using a lemma. 

apply : Apply a statement to reduce the goal. In ordinary mathematics you would read this as. By this theorem, 
        it suffices to prove the following ... 

exact : The goal that is to show is exactly the following lemma/theorem. 

nth_rewrite i _ : If you use rw, it will change the every occurrence of the term. Sometimes you only want to
                  do that on a certain occurrence, that you can use nth_rewrite i to change it on the ith 
                  occurrence (starting counting with 0). 

conv_lhs begin ... end 
conv_rhs begin ... end : Solve a similar problem to the one before, they allow you to only rewrite the left or 
                         the right hand side of an equation. 

norm_num : Similar to ring, but only calculates explicit expressions (with actual numbers.)
-/

/-- `real_vector_space V` is the type of real vector space structures on the type `V`. -/
class real_vector_space (V : Type)
  extends has_zero V, has_add V, has_neg V, has_scalar ℝ V : Type :=
(add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w))
(add_comm : ∀ u v : V, u + v = v + u)
(add_zero : ∀ v : V, v + 0 = v)
(zero_add : ∀ v : V, 0 + v = v)
(add_neg : ∀ v : V, v + (-v) = 0)
(neg_add : ∀ v : V, (-v) + v = 0)
(smul_assoc : ∀ (a b : ℝ) (v : V), (a * b) • v = a • (b • v))
(one_smul : ∀ v : V, (1 : ℝ) • v = v)
(add_smul : ∀ (a b : ℝ) (v : V), (a + b) • v = a • v + b • v)
(smul_add : ∀ (a : ℝ) (v w : V), a • (v + w) = a • v + a • w)

namespace real_vector_space

/- We can also add the simp attribute to statements later. -/
attribute [simp] add_assoc add_zero zero_add add_neg neg_add smul_assoc one_smul add_smul smul_add

variables {V : Type} [real_vector_space V] {u v w : V} {a b : ℝ}

/- 
Let's first let Lean know that the plane and the 2x2-matrices are real vector spaces. We have proved 
everything on the previous two sheets, we just have to package it nicely.
-/

instance : real_vector_space ℝ² := 
_

instance : real_vector_space Mat₂ :=
_

/- 
We continue by proving some well-known properties which hold in (real) vector spaces.
-/

lemma zero_unique_right_neutral (h : v + w = v)  :  w = 0 :=
begin
  sorry
end

lemma zero_unique_left_neutral (h : w + v = v) : w = 0 :=
begin
  sorry
end


@[simp] lemma zero_smul_eq_zero_vector (v : V) : (0 : ℝ) • v = 0 :=
begin
  sorry
end

lemma neg_unique_right_add_inv (h : v + w = 0) :  w = -v :=
begin
  sorry
end

lemma neg_unique_left_add_inv (h : w + v = 0) : w = -v :=
begin
  sorry
end

lemma minus_one_smul_eq_neg : (-1 : ℝ) • v = -v :=
begin
  sorry
end

end real_vector_space

/- It has been realised that the vector space axioms are not minimal, you can remove some of them and still 
  get the same structure. Here is a minimal list that has been found (which is quite similar to the standard 
  list, only the second axiom seems kind of weird.)-/
class minimal_vector_space_axioms (V : Type)
  extends has_add V, has_scalar ℝ V : Type :=
(add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w))
(zero_smul_eq : ∀ v w : V, (0 : ℝ) • v = (0 : ℝ) • w)
(one_smul : ∀ v : V, (1 : ℝ) • v = v)
(smul_assoc : ∀ (a b : ℝ) (v : V), (a * b) • v = a • (b • v))
(add_smul : ∀ (a b : ℝ) (v : V), (a + b) • v = a • v + b • v)
(smul_add : ∀ (a : ℝ) (v w : V), a • (v + w) = a • v + a • w)

/- Note that in contrast to the vector space axioms, the axiom about the zero vector is omitted from these 
  minimal vector space axioms. However this means that there is no reason for any vector at all to exist 
  in `V`. So let's prove that the empty set satisfies these axioms. -/
instance : minimal_vector_space_axioms empty :=
_

/- Let's prove that any real_vector_space satisfies the minimal vector space axioms, which is not too difficult, '
  there is only one axiom which is already included in the axioms and that is immediately true. -/
def to_minimal_vector_space_axioms (V : Type) [real_vector_space V] : minimal_vector_space_axioms V :=
{ add := λ v w, v+w,
  smul := λ a v, a • v,
  add_assoc := sorry,
  zero_smul_eq := sorry,
  one_smul := sorry,
  smul_assoc := sorry,
  add_smul := sorry,
  smul_add := sorry }

/- In the other direction, the difference seems larger, so let's try to prove some of the axioms which are missing. -/

lemma minimal_vector_space_axioms.add_zero (V : Type) [minimal_vector_space_axioms V] (v w : V) : v + (0 : ℝ) • w = v :=
begin 
  sorry
end

lemma minimal_vector_space_axioms.zero_add (V : Type) [minimal_vector_space_axioms V] (v w : V) : (0 : ℝ) • w + v = v :=
begin 
  sorry
end

lemma minimal_vector_space_axioms.add_neg (V : Type) [minimal_vector_space_axioms V] (v : V) : v + (-1 : ℝ) • v = (0 : ℝ) • v :=
begin 
  sorry
end

lemma minimal_vector_space_axioms.neg_add (V : Type) [minimal_vector_space_axioms V] (v : V) : (-1 : ℝ) • v + v = (0 : ℝ) • v :=
begin 
  sorry
end

/- The following is probably the most challenging one. Consider trying to prove it on paper first. -/
lemma minimal_vector_space_axioms.add_comm (V : Type) [minimal_vector_space_axioms V] (v w : V) : v + w = w + v :=
begin
  sorry
end

/- However if we demand that the set V is nonempty, the axioms are in fact equivalent as we show with the 
  following two results. These are `definitions` as they transport data. Often in a maths lecture we would 
  instead say `proposition` for this, or if one is very careful `definition-proposition`. The definition is 
  marked as `noncomputable` as it relies on choosing an arbitrary element `v` from the nonempty type `V`, 
  for which there might not be an algorithm. -/
noncomputable def to_real_vector_space (V : Type) [minimal_vector_space_axioms V] (h : nonempty V) : real_vector_space V :=
{ zero := begin let v := h.some, exact ((0 : ℝ) • v) end,
  neg := begin intro v, exact ((-1 : ℝ) • v) end, 
  add_assoc := sorry,
  add_comm := sorry,
  add_zero := sorry, 
  zero_add := sorry,
  add_neg := sorry,
  neg_add := sorry,
  smul_assoc := sorry,
  one_smul := sorry,
  add_smul := sorry,
  smul_add := sorry }



 
