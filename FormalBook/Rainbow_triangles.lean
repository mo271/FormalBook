import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs
import Mathlib.Data.Real.Sign
--import FormalBook.Chapter_22.lean



/-!
# One square and an odd number of triangles
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Classical
open Finset





-- First we define the inductive type Rainbow, which will be the the target type of the painter
-- function. The painter function will take a point in ℝ² and return a color from Rainbow (eg. Red
-- Blue or Green).

inductive Rainbow
| Red
| Green
| Blue

--Now we define the painter function as appears in the Book.

def painter (Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀) :
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



--The next definition and lemma relate things to matrices more like in the book.
--But they are not needed.

def rainbow_matrix (X Y Z : ℝ²): Matrix (Fin 3) (Fin 3) ℝ :=
![![X 0, X 1, 1], ![Y 0, Y 1, 1], ![Z 0, Z 1, 1]]

lemma det_of_rainbow_matrix (X Y Z : ℝ²) :
  Matrix.det (rainbow_matrix X Y Z) =
   (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) := by
rw [Matrix.det_fin_three, rainbow_matrix]
simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
     Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
     Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.tail_val',
     Matrix.head_val', Matrix.head_fin_const, mul_one, one_mul]
ring_nf

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



-- We now prove that for any line segment in ℝ² contains at most 2 colors.


lemma det_triv_triangle (X Y : ℝ² ) : det (fun | 0 => X | 1 => X | 2 => Y) = 0 := by
  simp [det]

lemma Lhull_equals_Thull (L:Segment) :
closed_hull L = closed_hull (fun | 0 => L 0 | 1 => L 0 | 2 => L 1: Fin 3 → ℝ²) := by

ext x
constructor
intro ⟨α, hα, hαx⟩
use fun | 0 => 0 | 1 => α 0| 2 => α 1
refine ⟨⟨?_,?_⟩, ?_⟩
intro i;  fin_cases i <;> simp [hα.1]
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three];
intro ⟨α, hα, hαx⟩
use fun | 0  => α 0 + α 1| 1 => α 2
refine ⟨⟨?_,?_⟩, ?_⟩
intro i; fin_cases i <;> (simp; linarith [hα.1 0, hα.1 1, hα.1 2])
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three, add_smul]



lemma Lhull_equals_Thull' (L:Segment) (T: Triangle) (Tseg : T =  fun| 0 => L 0 | 1 => L 0 | 2 => L 1) :
closed_hull L = closed_hull T := by

ext x
constructor
unfold closed_hull
rintro ⟨α, hα, hx⟩
have h1: ∃ α : Fin 2 → ℝ, (∑ (i : Fin 2), α i = 1) ∧ x = ∑ (i : Fin 2), α i • L i := by
  use α
  exact ⟨hα.2, hx.symm⟩
cases' h1 with α hα
cases' hα with hα1 hα2
let α' : Fin 3 → ℝ := fun | 0 => α (0) | 1 => 0 | 2 => α (1)
have h2: ∃ α : Fin 3 → ℝ, (∑ (i : Fin 3), α i = 1) ∧ x = ∑ (i : Fin 3), α i • T i := by
  use α'
  constructor
  rw [Fin.sum_univ_three]




lemma no_three_colors_on_a_line (L : Segment) (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀)
(v : Valuation ℝ Γ₀) (max: ∀ x y : ℝ, v x ≠ v y → v (x + y) = max (v x) (v y)) :
 ∃ c : Rainbow, ∀ P ∈ closed_hull L, painter Γ₀ locg v P ≠ c := by

by_contra h
push_neg at h
have hr : ∃ z ∈ closed_hull L , painter Γ₀ locg v z = Rainbow.Red := by
  apply h
have hb : ∃ x ∈ closed_hull L , painter Γ₀ locg v x = Rainbow.Blue := by
  apply h
have hg : ∃ y ∈ closed_hull L , painter Γ₀ locg v y = Rainbow.Green := by
  apply h
rcases hr with ⟨z, hz, hzr⟩
rcases hb with ⟨x, hx, hxb⟩
rcases hg with ⟨y, hy, hyg⟩

let Tseg : Fin 3 → ℝ² := fun | 0 => L 0 | 1 => L 0 | 2 => L 1
have hTseg : det Tseg = 0 := det_triv_triangle (L 0) (L 1)
have rain1: det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  rw [Lhull_equals_Thull L] at hx hy hz
  exact det_0_triangle_imp_triv hTseg x y z hx hy hz
have vrain1 : v (det (fun | 0 => x | 1 => y | 2 => z)) = v 0 := by
  rw [rain1]
rw [v.map_zero] at vrain1
have rain2: v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  have h_det : det (fun | 0 => x | 1 => y | 2 => z) =
    (x 0 * y 1 + x 1 * z 0 + y 0 * z 1 - y 1 * z 0 - x 1 * y 0 - x 0 * z 1) := by
    simp [det]
    ring_nf
  rw [h_det]
  apply bounded_det
  exact hxb
  exact hyg
  exact hzr
  apply max
have contra: v (det (fun | 0 => x | 1 => y | 2 => z)) = 0 ∧
v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  exact ⟨vrain1, rain2⟩
have ⟨h1, h2⟩ := contra
have h3 : (0 : Γ₀) ≥ 1 := by
  rw [h1] at h2
  exact h2
exact not_le_of_gt (zero_lt_one) h3
