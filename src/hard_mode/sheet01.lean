/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import data.real.basic 

/-! Defining the plane ℝ² 

This file defines the plane and equips it with the usual addition and scalar multiplication. 

Some tactics that would be useful in the remainder:

cases : splits a structure into its component, e.g. if v is a pair of real numbers, cases v will split it 
        into its first component v_x and its second component v_y. 
simp : The simplifyer. Can be very good in simplifying things it is trained on. The challenge is to train it 
       correctly. (Part of tidy.)
ext : The standard tactic to prove more complicated things are equal by splitting it into components. For 
      example, it is already trained to prove that two functions f and g are equal if and only if they agree 
      whenever applied to elements, i.e. f x = g x for all x, or that two subsets U and V of a set X are equal
      if and only if they have the same elements. (Part of tidy.)
ring : Let's you solve standard equations in rings. 
-/

structure plane : Type :=
(x : ℝ) (y : ℝ) 

namespace plane

/- We want to use the standard notation ℝ² for the real plane. -/
notation `ℝ²` := plane

/- Now let's define the addition on ℝ² like we are used to. This is done so we can write v + w for vectors v 
  and w in ℝ² without having to specify how they are actually defined. -/
instance has_add_plane : has_add ℝ² := sorry

lemma add_assoc (u v w : ℝ²) : u + v + w = u + (v + w) :=
begin
  sorry
end

lemma add_comm (v w : ℝ²) : v + w = w + v :=
begin
  sorry
end

/- We want to give at least one example of a vector in ℝ², the zero vector. -/
def zero_vector : ℝ² := sorry

/- In mathematics, it is common to write 0_V for the zero vector of a vector space V, sometimes one even 
  omits the subscript V. We want to be able to use the same abuse of notation in Lean. (With the difference 
  that it should always be clear to Lean what specific 0 we are talking about.)-/
instance : has_zero ℝ² := sorry

@[simp] lemma add_zero (v : ℝ²) : v + 0 = v :=
begin
  sorry
end

@[simp] lemma zero_add (v : ℝ²) : 0 + v = v :=
begin
  sorry
end

/- Let's define the negation of a vector. -/
instance : has_neg ℝ² := sorry

@[simp] lemma add_neg_self (v : ℝ²) : v + -v = 0 :=
begin
  sorry
end 

@[simp] lemma neg_add_self (v : ℝ²) : -v + v = 0 :=
begin
  sorry
end

/- We also want to define subtraction and scalar multiplication. -/
instance : has_sub ℝ² := sorry

instance : has_scalar ℝ ℝ² := sorry

lemma smul_assoc (a b : ℝ) (v : ℝ²) : (a * b) • v = a • (b • v) :=
begin
  sorry
end 

@[simp] lemma one_smul (v : ℝ²) : (1 : ℝ) • v = v :=
begin
  sorry
end   

@[simp] lemma smul_add (a : ℝ) (v w : ℝ²) : a • (v + w) = a • v + a • w :=
begin
  sorry
end 

@[simp] lemma add_smul (a b : ℝ) (v : ℝ²) : (a + b) • v = a • v + b • v :=
begin
  sorry
end

end plane