/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/

import solutions.sheet08

/-

# The other way round, a function from an equivalence relation

On the previous sheet we saw that given a (surjective) function `f : X → Y` we can produce 
an equivalence relation `∼` on `X` such that `x ≈ x'` iff `f (x) = f (x')`. On this sheet 
we will see that Lean can go the other way round. For every type `X` and any 
equivalence relation `≈` there exists a type `Y` and 

- a surjective function `q : X → Y` such that 
- `x ≈ x'` iff `q (x) = q (x')`. 

There are different ways to construct such a `Y`, depending on the situation some are 
easier than others. Lean (and that seems to be special compared to other interactive 
theorem provers) has an inbuilt construction `quotient s` for a setoid `s` (recall that 
a setoid is just a fancy way of saying a set together with an equivalence relation on it).
What is important here is not how Lean's choice of implementation of such a `Y` and `g` 
is, but the API connected to it is. 
-/



/- Let's set notation for our model of the integers as the quotient of the setoid s 
  we defined on sheet07. -/

notation `myint` := quotient s

-- `setoid` is a class, so `s` should not just be a definition, we should
-- make it an instance by tagging it with the `instance` attribute
attribute [instance] s t

-- Now we can use the notation `≈` for the equivalence relations `R`  
-- and `⟦x⟧` for the element of `myint` corresponding to the pair `(a,b)` in `ℕ²`.

-- For a type `X` and a setoid structure `s` on `X` there is a function 
-- `quotient.mk : X → quotient s`, the function `q` we were after. The brackets ⟦ ⟧ we 
-- were using before are just notation for this function, i.e. `quotient.mk x = ⟦x⟧`. 
-- Let's see that this is true by definition. 

example (x : nat_plane) : quotient.mk x = ⟦x⟧ :=
begin
  refl
end 

-- Furthermore, `≈` is just notation for `R`
-- (this is handy to know; let's give it a name so we can rewrite it)
lemma equiv_def (r s : nat_plane) : r ≈ s ↔ R r s :=
begin
  refl
end

-- One of our demands was that the function `q` is surjective. Let's try to prove that. 

lemma q_surj : function.surjective (λ (r : nat_plane), quotient.mk r) :=
begin
  exact surjective_quotient_mk nat_plane,
end



