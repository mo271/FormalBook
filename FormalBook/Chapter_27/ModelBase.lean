/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

/-!
# Buffon's uniform position model

The lower endpoint has offset `u * d`, where `u` is uniform on `[0, 1)`. For a
nonnegative vertical displacement `r * d`, the number of ruled lines crossed is
`floor (u + r)`. Endpoints are counted at the upper end; changing this convention
on boundary alignments does not affect the integrals.
-/

@[expose] public section

open MeasureTheory Set Real Classical

namespace Chapter27

/-- Number of lines reached by a segment with normalized vertical displacement `r`.
The lower endpoint has normalized offset `u ∈ [0, 1)`. -/
noncomputable def offsetCrossings (r u : ℝ) : ℤ := ⌊u + r⌋

lemma intervalIntegrable_offsetCrossings (r a b : ℝ) :
    IntervalIntegrable (fun u => (offsetCrossings r u : ℝ)) volume a b := by
  apply Monotone.intervalIntegrable
  intro u v huv
  change ((⌊u + r⌋ : ℤ) : ℝ) ≤ ((⌊v + r⌋ : ℤ) : ℝ)
  exact_mod_cast Int.floor_mono (show u + r ≤ v + r by linarith)

/-- The crossing event for the next ruled line. -/
def hitsLine (r u : ℝ) : Prop := 1 ≤ u + r

lemma offsetCrossings_nonneg {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    0 ≤ offsetCrossings r u := Int.floor_nonneg.mpr (by linarith)

/-- The integer count agrees with the geometric criterion for reaching the `n`th line. -/
theorem le_offsetCrossings_iff (r u : ℝ) (n : ℤ) :
    n ≤ offsetCrossings r u ↔ (n : ℝ) ≤ u + r := Int.le_floor

theorem hitsLine_iff (r u : ℝ) : hitsLine r u ↔ 1 ≤ offsetCrossings r u := by
  simp only [hitsLine, le_offsetCrossings_iff, Int.cast_one]

/-- Integrating the indicator of an upper subinterval is its length. -/
lemma integral_offset_step {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u in (0 : ℝ)..1, if t < u then (1 : ℝ) else 0) = 1 - t := by
  have heq : (fun u : ℝ => if t < u then (1 : ℝ) else 0) =
      (Ioi t).indicator (fun _ => (1 : ℝ)) := by
    funext u
    simp only [Set.indicator, mem_Ioi]
  rw [heq, intervalIntegral.integral_of_le zero_le_one,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi t ∩ Ioc (0 : ℝ) 1 = Ioc t 1 := by
    rw [inter_comm, Ioc_inter_Ioi, max_eq_right ht0]
  rw [hs, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith :
    0 ≤ 1 - t), smul_eq_mul, mul_one]

/-- The same formula includes the threshold itself, which has measure zero. -/
lemma integral_offset_step_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u in (0 : ℝ)..1, if t ≤ u then (1 : ℝ) else 0) = 1 - t := by
  rw [← integral_offset_step ht0 ht1]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne t] with u hu
  intro _
  simp only [le_iff_lt_or_eq, Ne.symm hu, or_false]

/-- Averaging the number of crossings over a uniformly random offset gives the
normalized vertical displacement, including for long needles. -/
theorem integral_offsetCrossings (r : ℝ) :
    (∫ u in (0 : ℝ)..1, (offsetCrossings r u : ℝ)) = r := by
  let k : ℤ := ⌊r⌋
  let t : ℝ := (k : ℝ) + 1 - r
  have hk : (k : ℝ) ≤ r := Int.floor_le r
  have hk' : r < (k : ℝ) + 1 := Int.lt_floor_add_one r
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have heq : ∀ u ∈ Ioo (0 : ℝ) 1, (offsetCrossings r u : ℝ) =
      (k : ℝ) + if t ≤ u then 1 else 0 := by
    intro u hu
    by_cases htu : t ≤ u
    · have hf : offsetCrossings r u = k + 1 := by
        apply Int.floor_eq_iff.mpr
        constructor <;> push_cast <;> dsimp [t] at htu <;> linarith [hu.2]
      rw [hf, ite_eq_left htu]
      push_cast
      rfl
    · have hf : offsetCrossings r u = k := by
        apply Int.floor_eq_iff.mpr
        constructor <;> dsimp [t] at htu <;> linarith [hu.1]
      rw [hf, ite_eq_right htu, add_zero]
  have hi : IntervalIntegrable (fun u : ℝ => if t ≤ u then (1 : ℝ) else 0)
      volume 0 1 := by
    apply Monotone.intervalIntegrable
    intro a b hab
    dsimp only
    split_ifs <;> try norm_num
    linarith
  calc
    (∫ u in (0 : ℝ)..1, (offsetCrossings r u : ℝ))
        = ∫ u in (0 : ℝ)..1, (k : ℝ) + if t ≤ u then 1 else 0 :=
      intervalIntegral.integral_congr_Ioo_of_le zero_le_one heq
    _ = (k : ℝ) + (1 - t) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hi,
        intervalIntegral.integral_const, integral_offset_step_le ht0 ht1]
      simp
    _ = r := by dsimp [t]; ring

/-- Averaging the crossing event gives the height ratio clipped at one. -/
theorem integral_hitsLine {r : ℝ} (hr : 0 ≤ r) :
    (∫ u in (0 : ℝ)..1, if hitsLine r u then (1 : ℝ) else 0) = min 1 r := by
  by_cases hr1 : r ≤ 1
  · have heq : (fun u => if hitsLine r u then (1 : ℝ) else 0) =
        fun u => if 1 - r ≤ u then (1 : ℝ) else 0 := by
      funext u
      have h : hitsLine r u ↔ 1 - r ≤ u := by
        unfold hitsLine
        constructor <;> intro h <;> linarith
      simp only [h]
    rw [heq, integral_offset_step_le (by linarith) (by linarith), min_eq_right hr1]
    ring
  · rw [min_eq_left (le_of_not_ge hr1)]
    calc
      (∫ u in (0 : ℝ)..1, if hitsLine r u then (1 : ℝ) else 0)
          = ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le zero_le_one] at hu
        rw [ite_eq_left]
        dsimp [hitsLine]
        linarith [hu.1]
      _ = 1 := by simp

/-- For a short vertical projection, there cannot be more than one crossing. -/
theorem offsetCrossings_eq_indicator {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hu : u ∈ Ico (0 : ℝ) 1) :
    offsetCrossings r u = if hitsLine r u then 1 else 0 := by
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    simp only [Int.cast_one]
    exact ⟨h, by linarith [hu.2]⟩
  · apply Int.floor_eq_iff.mpr
    simp only [Int.cast_zero, zero_add]
    exact ⟨by linarith [hu.1], lt_of_not_ge h⟩

end Chapter27
