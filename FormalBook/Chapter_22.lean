/-
Copyright 2024 the Amsterdam Lean seminar

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching,
Maris Ozols,
Jan Hendriks,
Casper,
Pjotr Buys,
Giacomo Grevink,
Dion Leijnse,
Thijs Maessen,
Thomas Koopman,
Jonas van der Schaaf,
Lenny Taelman,
Dhyan Aranha.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Valuation.Basic
open BigOperators

/-!
# One square and an odd number of triangles
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)


-- First we define the inductive type Rainbow, which will be the the target type of the painter
-- function. The painter function will take a point in ℝ² and return a color from Rainbow (eg. Red
-- Blue or Green).

inductive Rainbow
| Red
| Green
| Blue

--Now we define the painter function as appears in the Book.

def painter (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀) :
ℝ² → Rainbow
| X => if v (X 0) < v 1 ∧ v (X 1) < v 1 then Rainbow.Red
  else if v (X 0) < v (X 1) ∧ v (X 1) ≥ v 1 then Rainbow.Green
  else Rainbow.Blue



-- The next two lemmas below basically unravel the definition of the painter function which will
-- be of use in the proof of the lemma on the boundedness of the determinant.

lemma painted_green1 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
 (X : ℝ²) : painter Γ₀ locg v X = Rainbow.Green → v (X 1) ≥  v (1) := by
  intro h
  simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
  -- I want to get rid of this simp with an unfold but if I do this then split_ifs stops working.
  split_ifs at h with h1 h2
  rcases h2 with ⟨p,  q⟩
  rw [v.map_one]
  exact q

lemma painted_green2  (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
 (X : ℝ²) : painter Γ₀ locg v X = Rainbow.Green → v (X 0) < v (X 1) := by
  intro h
  simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1 h2
  rcases h2 with ⟨p,  q⟩
  exact p



-- the next lemma should be a cousin? of push_neg but I couldn't get what was in mathlib to work so
-- I just did it by hand.

lemma dist_negation_over_and (P Q : Prop): ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ


lemma painted_blue1 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X : ℝ²) : painter Γ₀ locg v X = Rainbow.Blue → v (X 0) ≥ v (1) := by
intro h
simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
--again here we want to get rid of the simp with an unfold but then split_ifs stops working.
split_ifs at h with h1 h2
rw [dist_negation_over_and] at h1
rw [dist_negation_over_and] at h2
cases' h1 with p q
rw [not_lt] at p
rw [v.map_one]
apply p
cases' h2 with m n
·  rw [not_lt] at m
   rw [not_lt, ← v.map_one] at q
   exact le_trans q m

·  rw [not_lt] at q
   contradiction

lemma painted_blue2 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X : ℝ²) : painter Γ₀ locg v X = Rainbow.Blue → v (X 0) ≥ v (X 1) := by
intro h
simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
split_ifs at h with h1 h2
rw [dist_negation_over_and] at h1
rw [dist_negation_over_and] at h2
cases' h2 with p q
rw [not_lt] at p
apply p

cases' h1 with m n
rw [not_lt] at m
rw [not_le] at q
have q' : v (X 1) ≤ 1 := by
  exact le_of_lt q
exact le_trans q' m

rw [not_lt] at n
contradiction

lemma painted_red1 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X : ℝ²) : painter Γ₀ locg v X = Rainbow.Red → v (X 0) < v 1 := by
intro h
simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
split_ifs at h with h1
rcases h1 with ⟨p,  q⟩
rw [v.map_one]
exact p



lemma painted_red2 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X : ℝ²) : painter Γ₀ locg v X = Rainbow.Red → v (X 1) < v 1 := by
intro h
simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
split_ifs at h with h1
rcases h1 with ⟨p,  q⟩
rw [v.map_one]
exact q

-- We now record our definition of a rainbow triangle

def rainbow_triangle  (T : Fin 3 → ℝ²) (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀)
(v : Valuation ℝ Γ₀) : Prop :=
Function.Surjective (painter Γ₀ locg v ∘ T)


-- Before the first main lemma we need a few lemmas that will be used in its proof.
-- Essentially we are just establishing bounds on valuations of the terms that appear in the
-- definition of the area of a triangle.



lemma val_bound1 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y: ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green) :
v (X 0 * Y 1) ≥ 1 := by

have h1 : v (X 0) ≥ v 1 := painted_blue1 Γ₀ locg v X hb
have h2 : v (Y 1) ≥ v 1 := painted_green1 Γ₀ locg v Y hg
have h3: v (X 0 * Y 1) ≥ v 1 * v 1 := by
  rw [v.map_mul]
  apply mul_le_mul' h1 h2
rw [v.map_mul]
rw [v.map_one, one_mul, v.map_mul] at h3
exact h3



lemma val_bound2 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red) :
v (X 1 * Z 0) < v (X 0 * Y 1) := by

have h1 : v (X 1) ≤  v (X 0) := painted_blue2 Γ₀ locg v X hb
have h2 : v (Z 0) < v 1 := painted_red1 Γ₀ locg v Z hr
have h3 : v (X 1 * Z 0) < v (X 0) * v 1 := by
  rw [v.map_mul]
  apply mul_lt_mul' h1 h2
  apply zero_le'
  have h4: v (X 0) ≥  v 1 := painted_blue1 Γ₀ locg v X hb
  have h5: v 1 > 0 := by
    rw [v.map_one]
    apply zero_lt_one
  exact lt_of_lt_of_le h5 h4
have h6 : v (Y 1) ≥ v 1 := painted_green1 Γ₀ locg v Y hg
have h7 : v (X 0) * v 1 ≤ v (X 0) * v (Y 1) :=
  mul_le_mul' (le_refl (v (X 0))) h6
rw [← map_mul, ← map_mul] at h7
rw [← map_mul] at h3
exact lt_of_lt_of_le h3 h7



lemma val_bound3 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red):
v (Y 0 * Z 1) < v (X 0 * Y 1) := by

have h1 : v (Y 0) < v (Y 1) := painted_green2  Γ₀ locg v Y hg
have h2 : v (Z 1) < v 1 := painted_red2 Γ₀ locg v Z hr
have h3:  v (Y 0 * Z 1) < v (Y 1) * v 1 := by
 rw [v.map_mul]
 apply mul_lt_mul'' h1 h2
 apply zero_le'
 apply zero_le'
have h4 : v (X 0) ≥ v 1 := painted_blue1 Γ₀ locg v X hb
have h5 : v (Y 1) * v 1 ≤ v (Y 1) * v (X 0) :=
  mul_le_mul' (le_refl (v (Y 1))) h4
rw [← map_mul] at h5
rw [← map_mul] at h3
rw [← map_mul] at h5
have h6: v (X 0 * Y 1) = v (Y 1 * X 0) := by
  rw [mul_comm]
rw [h6]
exact lt_of_lt_of_le h3 h5



lemma val_bound4 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red):
v (Y 1 * Z 0) < v (X 0 * Y 1) := by

have h1 : v (Z 0 ) < v 1 := painted_red1 Γ₀ locg v Z hr
have h2 : v (Z 0 * Y 1) < v 1 * v (Y 1) := by
  rw [v.map_mul]
  apply mul_lt_mul
  apply h1
  apply refl
  have h3: v (Y 1) ≥ v 1 := painted_green1 Γ₀ locg v Y hg
  have h4: v 1 > 0 := by
    rw [v.map_one]
    apply zero_lt_one
  exact lt_of_lt_of_le h4 h3
  apply zero_le'
have h5: v (X 0) ≥ v 1 := painted_blue1 Γ₀ locg v X hb
have h6:  v (Y 1) * v 1 ≤  v (Y 1) * v (X 0):=
  mul_le_mul' (le_refl (v (Y 1))) h5
rw [mul_comm] at h6
have h7: v (Y 1) * v (X 0) = v (X 0 * Y 1) := by
 rw [mul_comm, v.map_mul]
rw [h7] at h6
rw [mul_comm] at h2
exact lt_of_lt_of_le h2 h6



lemma val_bound5 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red):
v (X 1 * Y 0) < v (X 0 * Y 1) := by

have h1 : v (X 1) ≤ v (X 0) := painted_blue2 Γ₀ locg v X hb
have h2 : v (Y 0) < v (Y 1) := painted_green2 Γ₀ locg v Y hg
have h3: v (X 1 * Y 0) < v (X 0) * v (Y 1) := by
  rw [v.map_mul]
  apply mul_lt_mul' h1 h2
  apply zero_le'
  have h4: v (Y 1) ≥ v 1 := painted_green1 Γ₀ locg v Y hg
  have h5: v (X 0) ≥ v 1 := painted_blue1 Γ₀ locg v X hb
  rw [v.map_one] at h5
  have h6: v 1 > 0 := by
    rw [v.map_one]
    apply zero_lt_one
  rw [← v.map_one] at h5
  exact lt_of_lt_of_le h6 h5
rw [← v.map_mul] at h3
apply h3



lemma val_bound6 (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red):
v (X 0 * Z 1) < v (X 0 * Y 1) := by

have h1 : v (Z 1) < v 1 := painted_red2 Γ₀ locg v Z hr
have h2 : v (X 0) * v 1 ≤  v (X 0) * v (Y 1) :=
  mul_le_mul' (le_refl (v (X 0))) (painted_green1 Γ₀ locg v Y hg)
have h3 : v (X 0 * Z 1) < v (X 0) * v 1 := by
  rw [v.map_mul]
  apply mul_lt_mul' (le_refl (v (X 0))) h1
  apply zero_le'
  have h4: v (X 0) ≥ v 1 := painted_blue1 Γ₀ locg v X hb
  have h5: v 1 > 0 := by
    rw [v.map_one]
    apply zero_lt_one
  exact lt_of_lt_of_le h5 h4
rw [← v.map_mul] at h3
rw [← v.map_mul, ← v.map_mul] at h2
exact lt_of_lt_of_le h3 h2



-- Now we come the first main lemma of the chapter.


lemma bounded_det (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red) (h: ∀ x y : ℝ, v x ≠ v y → v (x + y) = max (v x) (v y)):
v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) ≥ 1 := by

have h1 : v (X 0 * Y 1 + X 1 * Z 0) = v (X 0 * Y 1) := by
  have h2: v (X 0 * Y 1) ≠ v (X 1 * Z 0) := by
    intro h
    have h3 := val_bound2 Γ₀ locg v X Y Z hb hg hr
    rw [h] at h3
    exact lt_irrefl _ h3
  have h4: v (X 0 * Y 1 + X 1 * Z 0) = max (v (X 0 * Y 1)) (v (X 1 * Z 0)) := by exact h _ _ h2
  have h5: max (v (X 0 * Y 1)) (v (X 1 * Z 0)) = v (X 0 * Y 1) := by
    rw [max_eq_left]
    exact le_of_lt (val_bound2 Γ₀ locg v X Y Z hb hg hr)
  rw [h5] at h4
  exact h4

have w1 : v (X 0 * Y 1 + X 1 * Z 0 + Y 0 *Z 1) = v (X 0 * Y 1) := by
  have w2: v (X 0 * Y 1) ≠ v (Y 0 * Z 1) := by
    intro h
    have w3 := val_bound3 Γ₀ locg v X Y Z hb hg hr
    rw [h] at w3
    exact lt_irrefl _ w3
  have w3: v (X 0 * Y 1 + X 1 * Z 0) ≠ v (Y 0 * Z 1) := by
    rw [h1]
    apply w2
  have w4: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1) = max (v (X 0 * Y 1 + X 1 * Z 0)) (v (Y 0 * Z 1)) := by
    exact h _ _ w3
  have w5: max (v (X 0 * Y 1 + X 1 * Z 0)) (v (Y 0 * Z 1)) = v (X 0 * Y 1) := by
    rw [h1]
    rw [max_eq_left]
    exact le_of_lt (val_bound3 Γ₀ locg v X Y Z hb hg hr)
  rw [w5] at w4
  exact w4

have q1 : v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0) = v (X 0 * Y 1) := by
  have q2: v (X 0 * Y 1) ≠ v (Y 1 * Z 0) := by
    intro h
    have q3 := val_bound4 Γ₀ locg v X Y Z hb hg hr
    rw [h] at q3
    exact lt_irrefl _ q3
  have q4: v (Y 1 * Z 0) = v (- Y 1 * Z 0) := by
    rw [← v.map_neg, neg_mul_eq_neg_mul]
  have q5: v (X 0 * Y 1 + X 1 * Z 0 ) ≠ v (Y 1 * Z 0) := by
    rw [h1]
    apply q2
  have q6: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1) ≠ v (Y 1 * Z 0) := by
    rw [w1]
    apply q2
  rw [q4] at q6
  have q7: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0) = max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1)) (v (-Y 1 * Z 0)) := by
    rw [sub_eq_neg_add, add_comm, ← neg_mul]
    exact h _ _ q6
  have q8: max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1)) (v (-Y 1 * Z 0)) = v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1) := by
    rw [w1]
    rw [max_eq_left]
    rw [← v.map_neg, neg_mul_eq_neg_mul, neg_neg]
    exact le_of_lt (val_bound4 Γ₀ locg v X Y Z hb hg hr)
  rw [q8] at q7
  rw [w1] at q7
  exact q7



have r1 : v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0) = v (X 0 * Y 1) := by
  have r2: v (X 0 * Y 1) ≠ v (X 1 * Y 0) := by
    intro h
    have r3 := val_bound5 Γ₀ locg v X Y Z hb hg hr
    rw [h] at r3
    exact lt_irrefl _ r3
  have r4: v (X 0 * Y 1 + X 1 * Z 0) ≠ v (X 1 * Y 0) := by
    rw [h1]
    apply r2
  have r5: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1) ≠ v (X 1 * Y 0) := by
    rw [w1]
    apply r2
  have r6: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0) ≠ v (X 1 * Y 0) := by
    rw [q1]
    apply r2
  have r7: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0) = max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0)) (v (-X 1 * Y 0)) := by
    rw [sub_eq_neg_add, add_comm, ← neg_mul]
    have neg: v (X 1 * Y 0) = v (- X 1 * Y 0) := by
     rw [← v.map_neg, neg_mul_eq_neg_mul]
    rw [neg] at r6
    exact h _ _ r6
  have r8: max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0)) (v (-X 1 * Y 0)) = v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0) := by
    rw [q1]
    rw [max_eq_left]
    rw [← v.map_neg, neg_mul_eq_neg_mul, neg_neg]
    exact le_of_lt (val_bound5 Γ₀ locg v X Y Z hb hg hr)
  rw [r8] at r7
  rw [q1] at r7
  exact r7


have s1 : v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) = v (X 0 * Y 1) := by
  have s2: v (X 0 * Y 1) ≠ v (X 0 * Z 1) := by
    intro h
    have s3 := val_bound6 Γ₀ locg v X Y Z hb hg hr
    rw [h] at s3
    exact lt_irrefl _ s3
  have s4: v (X 0 * Y 1 + X 1 * Z 0) ≠ v (X 0 * Z 1) := by
    rw [h1]
    apply s2
  have s5: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1) ≠ v (X 0 * Z 1) := by
    rw [w1]
    apply s2
  have s6: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0) ≠ v (X 0 * Z 1) := by
    rw [q1]
    apply s2
  have s7: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0) ≠ v (X 0 * Z 1) := by
    rw [r1]
    apply s2
  have s8: v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) = max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0)) (v (-X 0 * Z 1)) := by
    rw [sub_eq_neg_add, add_comm, ← neg_mul]
    have neg: v (X 0 * Z 1) = v (- X 0 * Z 1) := by
     rw [← v.map_neg, neg_mul_eq_neg_mul]
    rw [neg] at s7
    exact h _ _ s7
  have s9: max (v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0)) (v (-X 0 * Z 1)) = v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0) := by
    rw [r1]
    rw [max_eq_left]
    rw [← v.map_neg, neg_mul_eq_neg_mul, neg_neg]
    exact le_of_lt (val_bound6 Γ₀ locg v X Y Z hb hg hr)
  rw [s9] at s8
  rw [r1] at s8
  exact s8
have e: v (X 0 * Y 1) ≥ 1 := val_bound1 Γ₀ locg v X Y hb hg
rw [← s1] at e
apply e











/-## TODO
  - Monsky's Theorem
    - proof
inducrtive
      - Lemma 1
        - proof
      - Corollary
        - proof
      - Lemma 2
        - proof
          - (A)
          - (B)
  - Appendix: Extending valuations
    - definition
    - Theorem
      - proof
    - Lemma
      - proof
    - Claim
    - Zorn's Lemma
-/
