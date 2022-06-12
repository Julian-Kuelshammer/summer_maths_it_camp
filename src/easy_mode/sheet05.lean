/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Julian Kuelshammer
-/


import easy_mode.sheet04


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
  -- the point is that f.map_add and f.map_add' are *definitionally equal*
  -- but *syntactically different*, and the primed version looks uglier.
  -- The point of this lemma is that `f.map_add` looks nicer.
  exact f.map_add' v v'
end

lemma map_smul (f : V →ₗᵢₙ W) (a : ℝ) (v : V) : 
  f (a • v) = a • f v :=
begin 
  sorry
end


@[simp] lemma map_zero (f : V →ₗᵢₙ W) : f 0 = 0 :=
begin
  sorry
end

/- The following could be important later on. See if you use it. -/
lemma expand_two_linear (f : ℝ² →ₗᵢₙ ℝ²) (v : ℝ²) : (f v) = v.x • f ⟨1,0⟩ + v.y • f ⟨0,1⟩ :=
begin 
  sorry
end

end linear_map

def two_matrix.to_linear_map (A : Mat₂) : ℝ² →ₗᵢₙ ℝ² :=
{ to_fun := λ v, ⟨v.1 * A.fst_row.1 + v.2 * A.fst_row.2, v.1 * A.snd_row.1 + v.2 * A.snd_row.2⟩,
  map_add' := sorry,
  map_smul' := sorry, }

instance : has_coe_to_fun (two_matrix) (λ _, ℝ² → ℝ²) :=
{ coe := λ A, (A.to_linear_map).to_fun }

/- The following seems self-evident if you think what it means, but it is not immediately 
  clear to the simplifyer. If you want, you can comment it out and see what stops working 
  in later proofs. -/
@[simp] lemma to_linear_map_to_fun_eq_to_fun  (A : Mat₂) (v : ℝ²) :
A.to_linear_map v = A v := rfl

/- Now an expression like the following makes sense.-/
#check two_matrix.zero_matrix plane.zero_vector

/- Or even the following, which might seem a bit confusing.-/
#check (0 : two_matrix) 0 = 0

/- The following two simp-lemmas will help us actually prove such statements. -/
@[simp] lemma matrix_multiplication_x (A : Mat₂) (v : ℝ²) : 
(A v).1 = v.1 * A.fst_row.1 + v.2 * A.fst_row.2 := sorry

@[simp] lemma matrix_multiplication_y (A : Mat₂) (v : ℝ²) : 
(A v).2 = v.1 * A.snd_row.1 + v.2 * A.snd_row.2 := sorry
 
/- The zero matrix applied to the zero vector is equal to zero ...amazing.-/
example : (0 : two_matrix) 0 = 0 :=
begin
  sorry
end

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
{ fst_row := ⟨(f ⟨1,0⟩).1, (f ⟨0,1⟩).1⟩,
  snd_row := ⟨(f ⟨1,0⟩).2, (f ⟨0,1⟩).2⟩ }

@[simp] lemma linear_map.to_two_matrix_fst_row_x (f : ℝ² →ₗᵢₙ ℝ²) : f.to_two_matrix.fst_row.x = (f ⟨1,0⟩).1 := sorry
@[simp] lemma linear_map.to_two_matrix_fst_row_y  (f : ℝ² →ₗᵢₙ ℝ²) : f.to_two_matrix.fst_row.y = (f ⟨0,1⟩).1 := sorry
@[simp] lemma linear_map.to_two_matrix_snd_row_x (f : ℝ² →ₗᵢₙ ℝ²) : f.to_two_matrix.snd_row.x = (f ⟨1,0⟩).2 := sorry
@[simp] lemma linear_map.to_two_matrix_snd_row_y  (f : ℝ² →ₗᵢₙ ℝ²) : f.to_two_matrix.snd_row.y = (f ⟨0,1⟩).2 := sorry

@[simp] lemma to_two_matrix_to_fun_eq_to_fun (f : ℝ² →ₗᵢₙ ℝ²) (v : ℝ²) : f.to_two_matrix v = f.to_fun v := 
begin 
  sorry
end

/- And now we show that there is a 1-1 correspondence between 2x2-matrices and linear maps from the plane to itself. -/
def matrix_linear_correspondence : (ℝ² →ₗᵢₙ ℝ²) ≃ Mat₂ :=
{ to_fun := linear_map.to_two_matrix,
  inv_fun := two_matrix.to_linear_map,
  left_inv := sorry,
  right_inv := sorry, 
}

/- As a bonus you could even think about putting a vector space structure on (ℝ² →ₗᵢₙ ℝ²) and proving that it is 
  linearly isomorphic to Mat₂. -/