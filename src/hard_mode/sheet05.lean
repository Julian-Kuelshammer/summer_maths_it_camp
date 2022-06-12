/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/


import hard_mode.sheet04


/-! Linear maps

In this section, we give the definition of a linear map, show that a 2x2-matrix gives rise to a linear map, 
and that every linear map from ℝ² to ℝ² is given by a matrix. 
-/

/-- `linear_map V W` is the type of linear maps from `V` to `W`. -/
@[ext] structure linear_map (V W : Type) [real_vector_space V] [real_vector_space W] :=
(to_fun : V → W)
(map_add' (v v' : V) : to_fun (v + v') = to_fun v + to_fun v')
(map_smul' (a : ℝ) (v : V) : to_fun (a • v) = a • to_fun v)

namespace linear_map

-- throughout this sheet, `V` and `W` will be real vector spaces.
variables {V W : Type} [real_vector_space V] [real_vector_space W]

-- We use notation `V →ₗᵢₙ H` for the type of linear maps from `V` to `W`.
notation V ` →ₗᵢₙ ` W := linear_map V W

-- A linear map is a function, and so we set up a "coercion"
-- so that a linear map can be regarded as a function (even
-- though it's actually a pair consisting of a function and two axioms)
instance : has_coe_to_fun (V →ₗᵢₙ W) (λ _, V → W) :=
{ coe := linear_map.to_fun }

@[simp] lemma simplify_coercion (f : V →ₗᵢₙ W) (v : V) : f.to_fun v = f v := rfl 

-- Notice that we can now write `f (v + v')` and `f (a • v)` even though `f` isn't actually a
-- function, it's a pair consisting of a function `f.to_fun` and the axioms `f.map_add'` and `f.map_smul`.
-- The below lemma is how we want to use it as mathematicians though.
lemma map_add (f : V →ₗᵢₙ W) (v v' : V) : 
  f (v + v') = f v + f v' :=
begin
  sorry
end

lemma map_smul (f : V →ₗᵢₙ W) (a : ℝ) (v : V) : 
  f (a • v) = a • f v :=
begin 
  sorry
end

end linear_map

def two_matrix.to_linear_map (A : Mat₂) : ℝ² →ₗᵢₙ ℝ² :=
{ to_fun := sorry,
  map_add' := sorry,
  map_smul' := sorry, }

instance : has_coe_to_fun (two_matrix) (λ _, ℝ² → ℝ²) :=
{ coe := λ A, (A.to_linear_map).to_fun }

/- Now an expression like the following makes sense.-/
#check two_matrix.zero_matrix plane.zero_vector

/- Or even the following, which might seem a bit confusing.-/
#check (0 : two_matrix) 0 = 0

/- Let's generalise this to the zero matrix applied to an arbitrary vector.-/
lemma zero_matrix_apply (v : ℝ²) : (0 : two_matrix) v = 0 :=
begin
  sorry
end 

/- The other way round. -/
lemma matrix_apply_zero_vector (A : Mat₂) : A 0 = 0 :=
begin
  sorry
end

/- Now the other way round, associating a matrix to a linear map. -/
def linear_map.to_two_matrix (f : ℝ² →ₗᵢₙ ℝ²) : Mat₂ :=
sorry

/- And now we show that there is a 1-1 correspondence between 2x2-matrices and linear maps from the plane to itself. -/
def matrix_linear_correspondence : (ℝ² →ₗᵢₙ ℝ²) ≃ Mat₂ :=
{ to_fun := linear_map.to_two_matrix,
  inv_fun := two_matrix.to_linear_map,
  left_inv := sorry,
  right_inv := sorry, 
}

/- As a bonus you could even think about putting a vector space structure on (ℝ² →ₗᵢₙ ℝ²) and proving that it is 
  linearly isomorphic to Mat₂. -/