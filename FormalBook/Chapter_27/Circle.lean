/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The circular needle in Barbier's argument

A circle has diameter `d`, lower height `u * d`, and center height `(u + 1/2) * d`.
For `0 < u < 1`, only the ruled line at height `d` meets it, in two distinct points.
Boundary offsets are null, so the count is two almost everywhere.
-/

@[expose] public section

open MeasureTheory Set Real

namespace Chapter27

/-- Horizontal coordinates of the intersections of the circular needle and the `k`th line. -/
def circleSection (d u : ℝ) (k : ℤ) : Set ℝ :=
  {x | x ^ 2 + ((k : ℝ) * d - (u + 1 / 2) * d) ^ 2 = (d / 2) ^ 2}

/-- The squared half-width of the circular needle at the line of height `d`. -/
noncomputable def circleRadicand (d u : ℝ) : ℝ :=
  (d / 2) ^ 2 - (d - (u + 1 / 2) * d) ^ 2

lemma circleRadicand_pos {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1) :
    0 < circleRadicand d u := by
  have h : 0 < d ^ 2 * u * (1 - u) :=
    mul_pos (mul_pos (sq_pos_of_pos hd) hu.1) (sub_pos.mpr hu.2)
  dsimp [circleRadicand]
  nlinarith

/-- The line at height `d` cuts the circle in exactly the two square-root coordinates. -/
theorem circleSection_one {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1) :
    circleSection d u 1 =
      {Real.sqrt (circleRadicand d u), -Real.sqrt (circleRadicand d u)} := by
  have hs := Real.sq_sqrt (circleRadicand_pos hd hu).le
  ext x
  simp only [circleSection, mem_ofPred_eq, Int.cast_one, one_mul,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hx
    have hsq : x ^ 2 = (Real.sqrt (circleRadicand d u)) ^ 2 := by
      rw [hs]
      dsimp [circleRadicand]
      nlinarith
    have hprod : (x - Real.sqrt (circleRadicand d u)) *
        (x + Real.sqrt (circleRadicand d u)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · rw [hs]
      dsimp [circleRadicand]
      ring
    · rw [neg_sq, hs]
      dsimp [circleRadicand]
      ring

theorem circleSection_one_distinct {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1) :
    Real.sqrt (circleRadicand d u) ≠ -Real.sqrt (circleRadicand d u) := by
  have := Real.sqrt_pos.mpr (circleRadicand_pos hd hu)
  linarith

/-- All other ruled lines miss the circular needle at an interior offset. -/
theorem circleSection_eq_empty {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1)
    {k : ℤ} (hk : k ≠ 1) : circleSection d u k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  change x ^ 2 + ((k : ℝ) * d - (u + 1 / 2) * d) ^ 2 = (d / 2) ^ 2 at hx
  rcases (show k ≤ 0 ∨ 2 ≤ k by omega) with hk0 | hk2
  · have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have ha : (k : ℝ) * d - (u + 1 / 2) * d < -(d / 2) := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hk0' hd.le, mul_pos hu.1 hd]
    have hp : 0 < (((k : ℝ) * d - (u + 1 / 2) * d) - d / 2) *
        (((k : ℝ) * d - (u + 1 / 2) * d) + d / 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith [sq_nonneg x]
  · have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have ha : d / 2 < (k : ℝ) * d - (u + 1 / 2) * d := by
      nlinarith [mul_le_mul_of_nonneg_right hk2' hd.le,
        mul_pos (sub_pos.mpr hu.2) hd]
    have hp : 0 < (((k : ℝ) * d - (u + 1 / 2) * d) - d / 2) *
        (((k : ℝ) * d - (u + 1 / 2) * d) + d / 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg x]

/-- The exact two-point section and empty remaining sections, in one geometric statement. -/
theorem circle_intersections {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1) :
    (∃ a b : ℝ, a ≠ b ∧ circleSection d u 1 = {a, b}) ∧
      ∀ k : ℤ, k ≠ 1 → circleSection d u k = ∅ := by
  constructor
  · exact ⟨_, _, circleSection_one_distinct hd hu, circleSection_one hd hu⟩
  · intro k hk
    exact circleSection_eq_empty hd hu hk

/-- The actual intersection points, indexed by their ruled line and horizontal coordinate. -/
def circleIntersectionPoints (d u : ℝ) : Set (ℤ × ℝ) :=
  {p | p.2 ∈ circleSection d u p.1}

/-- The number of distinct intersection points of the circular needle and all ruled lines. -/
noncomputable def circleCrossings (d u : ℝ) : ℕ :=
  (circleIntersectionPoints d u).ncard

theorem circleIntersectionPoints_eq_pair {d u : ℝ} (hd : 0 < d)
    (hu : u ∈ Ioo 0 1) :
    circleIntersectionPoints d u =
      {(1, Real.sqrt (circleRadicand d u)), (1, -Real.sqrt (circleRadicand d u))} := by
  ext p
  rcases p with ⟨k, x⟩
  by_cases hk : k = 1
  · subst k
    simp only [circleIntersectionPoints, mem_ofPred_eq, circleSection_one hd hu,
      mem_insert_iff, mem_singleton_iff, Prod.mk.injEq, true_and]
  · simp only [circleIntersectionPoints, mem_ofPred_eq, circleSection_eq_empty hd hu hk,
      mem_empty_iff_false, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq, hk,
      false_and, or_self]

theorem circleCrossings_eq_two {d u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1) :
    circleCrossings d u = 2 := by
  rw [circleCrossings, circleIntersectionPoints_eq_pair hd hu]
  apply Set.ncard_pair
  intro h
  exact circleSection_one_distinct hd hu (congrArg Prod.snd h)

/-- The tangent endpoint offset has probability zero under the uniform position law. -/
theorem circleCrossings_eq_two_ae {d : ℝ} (hd : 0 < d) :
    ∀ᵐ u ∂volume.restrict (Ico (0 : ℝ) 1), circleCrossings d u = 2 := by
  filter_upwards [ae_restrict_mem measurableSet_Ico,
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with u hu hne
  exact circleCrossings_eq_two hd ⟨lt_of_le_of_ne hu.1 (Ne.symm hne), hu.2⟩

/-- Averaging the genuine geometric intersection count over a uniform offset gives two. -/
theorem integral_circleCrossings {d : ℝ} (hd : 0 < d) :
    (∫ u in (0 : ℝ)..1, (circleCrossings d u : ℝ)) = 2 := by
  calc
    (∫ u in (0 : ℝ)..1, (circleCrossings d u : ℝ)) = ∫ _ in (0 : ℝ)..1, (2 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro u hu
      simp only [circleCrossings_eq_two hd hu, Nat.cast_ofNat]
    _ = 2 := by simp

/-- Lazzarini's reported experiment gives exactly the classical rational approximation. -/
theorem lazzarini_identity : (2 : ℚ) * (5 / 6) * 3408 / 1808 = 355 / 113 := by
  norm_num

end Chapter27
