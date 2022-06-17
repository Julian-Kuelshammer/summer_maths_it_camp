/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import easy_mode.sheet09
import tactic.ring
import tactic.linarith

/-

# Induced functions on quotients

The quotient comes with what one would call a universal property in advanced courses: Given a type `X`, an 
equivalence relation `≈` on `X`, then for every other type `Y` and every function `h : X → Y` such that 
`x ≈ x' → f x = f x'` there is a unique function `h : X/≈  → Y` such that `f = h ∘ q`. In standard maths courses 
the existence of such `h` in examples is often justified as follows: For each equivalence class `⟦x⟧` of 
the quotient, choose a representative `x : X` and define `h(⟦x⟧) := f(x)`. One has to then prove that this 
is well-defined by invoking the assumption `x ≈ x' → f x = f x'`. In Lean, the function `h` can be produced 
automatically using `quotient.lift` applied to the assumption `x ≈ x' → f x = f x'`, one doesn't have to go 
through the steps. 

On this sheet we will see how this works, first starting with the example of negation, which is easier than 
addition as it only has one input, not two. 
-/



lemma neg_well_defined (x y : ℕ × ℕ) (h : x ≈ y) : ⟦(x.2,x.1)⟧ = ⟦(y.2, y.1)⟧ :=
begin
  sorry
end

def neg : myint → myint := quotient.lift (λ (x : ℕ × ℕ), ⟦(x.2, x.1)⟧) (neg_well_defined)

instance : has_neg myint :=
{ neg := neg }

/- 

There is an alternative way, which is in fact a special case of the first. Suppose `Y = Z/≈₂` and we are given 
a function `g : X → Z`. Consider the function `f = q₂ ∘ g` where `q₂ : Z → Z/≈₂` is the surjection.  
Then `x ≈ x' → f x = f x'` can be checked on `Z` instead, i.e. it can be checked that `x ≈ x' → g x ≈₂ g x'`
in order to reach the conclusion for `f`. Since this is a common situation, there is a special name for it: 
`quotient.map`, which takes the assumption `x ≈ x' → g x ≈₂ g x'` and defines a function `X/≈ → Z/≈₂`.

-/

def neg2 : myint → myint := quotient.map (λ x, (x.2, x.1)) 
begin 
  sorry
end

/- Why do the two definitions just defined agree? -/
lemma defn_neg_agree : neg = neg2 :=
begin
  sorry
end

/- 

Our next step will be to provide an addition and a multiplication on `myint` and prove that `myint` 
with these operations forms a commutative ring. To recall, a commutative ring is a set `R` 
together with operations `+: R×R → R` and `*: R×R → R` such that the following axioms hold:
(R1) `(x+y)+z=x+(y+z)` for all `x y z : R`
(R2) `x+y=y+x` for all `x y : R`
(R3) `∃ 0 : x+0=x=0+x` for all `x : R`
(R4) `∀ x ∃ -x : x + (-x) = (-x) + x = 0`
(R5) `(x * y) * z = x * (y * z)`
(R6) `∃ 1 : 1 * x = x`
(R7) `x * y = y * x` for all `x y : R`
(R8) `x * (y + z) = x * y + x * z` for all `x y z : R`

In fact, for lean addition is not a function `R×R → R`, but rather a function `R → (R → R)`, or 
`R → R → R` as in contrast to addition and multiplication, `→` is right associative in Lean.  
The function `R → (R → R)` takes a ring element `x : R` and sends it to the function `R → R` 
which sends `y : R` to `x + y`, in λ-notation `λ y, x+y`. In computer science, the correspondence 
between functions `R×R → R` and `R → (R → R)` is called currying after Haskell Curry. For 
mathematicians (using category theory), it is just a special case of the concept of an adjunction,
i.e. the functors of taking cartesian product  `- × R` and taking Hom in the category of sets 
`Hom(R,-)` are adjoint to each other.    

We want to define addition `myint × myint → myint` or equivalently `myint → myint → myint`. 
If we think about the first incarnation, we could do that as follows: First we prove that 
given an equivalence relation on `X` and an equivalence relation on `Y` we prove that there 
is an equivalence relation on `X × Y` given by `(x,y) ≈ (x',y')` iff `x ≈ x'` and `y ≈ y'`. 
Then we do the same steps as before. Applying currying, in the other way of thinking, 
we would have to do a two-step process of constructing a function from the quotient `myint` to 
the set of functions from the quotient `myint` to `myint`. Luckily, we don't have to think in 
detail about what this entails - binary operations are a common enough thing that Lean has a 
special construction that does all in one step, namely `quotient.map₂`. 

-/

def add : myint → myint → myint := quotient.map₂ (λ r s, (r.1+s.1, r.2+s.2)) 
begin 
  sorry
end 

instance : has_add myint :=
{ add := add }

def mul : myint → myint → myint := quotient.map₂ (λ r s, (r.1*s.1+r.2*s.2, r.1*s.2+r.2*s.1))
begin
  sorry
end

instance : has_mul myint :=
{ mul := mul }

/- Now we have to prove the ring axioms. For this, we have to prove something for all equivalence 
classes `r s t : myint`. We would rather like to check this on representatives. Then it becomes 
easy. To do this (depending on the number of inputs) you can apply the lemmas 
`quotient.induction_on r`, `quotient.induction_on₂ r s`, `quotient.induction_on₃ r s t`. To 
simplify the goal view, after that you can put `clear r s t` but that is not strictly necessary. -/

instance : comm_ring myint :=
{ add := has_add.add,
  add_assoc := begin sorry end,
  zero := ⟦(0,0)⟧,
  zero_add := begin sorry end,
  add_comm := begin sorry end,
  add_zero := begin sorry end, 
  neg := has_neg.neg,
  add_left_neg := begin sorry end,
  mul := has_mul.mul,
  mul_assoc := begin sorry end,
  one := ⟦(1,0)⟧,
  one_mul := begin sorry end,
  mul_one := begin sorry end,
  left_distrib := begin sorry end,
  right_distrib := begin sorry end,
  mul_comm := begin sorry end, }





