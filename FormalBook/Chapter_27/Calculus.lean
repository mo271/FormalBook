/-
Copyright 2026. Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Buffon's needle: the calculus proof

The conditional crossing probability is capped at one and averaged over inclination.
The short-needle formula, the long-needle formula, and the chapter's three exercises
are proved from this integral model.
-/

open Real Set MeasureTheory
open scoped Interval

@[expose] public section

noncomputable section

namespace Chapter27

/-- Conditional crossing probability at a fixed acute inclination. -/
def conditionalCrossingProbability (l d a : ℝ) : ℝ := min 1 (l / d * sin a)

/-- Average over a uniformly distributed acute inclination. -/
def crossingProbability (l d : ℝ) : ℝ :=
  (2 / π) * ∫ a in 0..π / 2, conditionalCrossingProbability l d a

theorem continuous_conditionalCrossingProbability (l d : ℝ) :
    Continuous (conditionalCrossingProbability l d) :=
  continuous_const.min (continuous_const.mul continuous_sin)

theorem crossingProbability_short {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d)
    (hld : l ≤ d) : crossingProbability l d = (2 / π) * (l / d) := by
  unfold crossingProbability
  have hratio : 0 ≤ l / d := div_nonneg hl hd.le
  have hratio' : l / d ≤ 1 := (div_le_one hd).2 hld
  have heq : (∫ a in 0..π / 2, conditionalCrossingProbability l d a) =
      ∫ a in 0..π / 2, l / d * sin a := by
    apply intervalIntegral.integral_congr
    intro a ha
    exact min_eq_right ((mul_le_mul_of_nonneg_left (sin_le_one a) hratio).trans
      (by simpa using hratio'))
  rw [heq, intervalIntegral.integral_const_mul, integral_sin]
  simp

theorem crossingProbability_boundary {d : ℝ} (hd : 0 < d) :
    crossingProbability d d = 2 / π := by
  simpa [ne_of_gt hd] using crossingProbability_short hd.le hd le_rfl

/-- The integral split at the critical angle for a long needle. -/
theorem crossingProbability_split {l d : ℝ} (hd : 0 < d) (hdl : d ≤ l) :
    crossingProbability l d = (2 / π) *
      ((l / d) * (1 - cos (arcsin (d / l))) + π / 2 - arcsin (d / l)) := by
  have hl : 0 < l := lt_of_lt_of_le hd hdl
  have hr : 0 ≤ d / l := div_nonneg hd.le hl.le
  have hr1 : d / l ≤ 1 := (div_le_one hl).2 hdl
  have ht : 0 ≤ arcsin (d / l) := arcsin_nonneg.2 hr
  have ht' : arcsin (d / l) ≤ π / 2 := arcsin_le_pi_div_two _
  have hsin : sin (arcsin (d / l)) = d / l := sin_arcsin (by linarith) hr1
  have hcancel : (l / d) * (d / l) = 1 := by
    field_simp [ne_of_gt hd, ne_of_gt hl]
  have hi (a b : ℝ) :=
    (continuous_conditionalCrossingProbability l d).intervalIntegrable (μ := volume) a b
  unfold crossingProbability
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (arcsin (d / l))) (hi (arcsin (d / l)) (π / 2))]
  have hleft : (∫ a in 0..arcsin (d / l), conditionalCrossingProbability l d a) =
      ∫ a in 0..arcsin (d / l), (l / d) * sin a := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le ht] at ha
    unfold conditionalCrossingProbability
    apply min_eq_right
    calc
      (l / d) * sin a ≤ (l / d) * sin (arcsin (d / l)) :=
        mul_le_mul_of_nonneg_left
          (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ht' ha.2)
          (div_nonneg hl.le hd.le)
      _ = 1 := by rw [hsin, hcancel]
  have hright : (∫ a in arcsin (d / l)..π / 2, conditionalCrossingProbability l d a) =
      ∫ a in arcsin (d / l)..π / 2, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le ht'] at ha
    unfold conditionalCrossingProbability
    apply min_eq_left
    calc
      1 = (l / d) * sin (arcsin (d / l)) := by rw [hsin, hcancel]
      _ ≤ (l / d) * sin a := mul_le_mul_of_nonneg_left
        (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ha.2 ha.1)
        (div_nonneg hl.le hd.le)
  rw [hleft, hright, intervalIntegral.integral_const_mul, integral_sin,
    intervalIntegral.integral_const]
  simp only [cos_zero, smul_eq_mul, mul_one]
  ring

/-- The closed formula from the chapter for long needles. -/
theorem crossingProbability_long {l d : ℝ} (hd : 0 < d) (hdl : d ≤ l) :
    crossingProbability l d = 1 + (2 / π) *
      ((l / d) * (1 - sqrt (1 - d ^ 2 / l ^ 2)) - arcsin (d / l)) := by
  rw [crossingProbability_split hd hdl, cos_arcsin, div_pow]
  field_simp [Real.pi_ne_zero]
  ring

/-- Longer needles have strictly greater crossing probability. -/
theorem crossingProbability_strictMono {d : ℝ} (hd : 0 < d) :
    StrictMonoOn (fun l => crossingProbability l d) (Ici 0) := by
  intro x hx y hy hxy
  have hypos : 0 < y := lt_of_le_of_lt hx hxy
  have hrpos : 0 < d / (2 * (y + d)) := div_pos hd (by positivity)
  have hr1 : d / (2 * (y + d)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  let a := arcsin (d / (2 * (y + d)))
  have hapos : 0 < a := arcsin_pos.2 hrpos
  have ha : a ≤ π / 2 := arcsin_le_pi_div_two _
  have hs : sin a = d / (2 * (y + d)) := sin_arcsin (by linarith) hr1
  have hspos : 0 < sin a := by rw [hs]; exact hrpos
  have hy1 : y / d * sin a < 1 := by
    rw [hs]
    calc
      y / d * (d / (2 * (y + d))) = y / (2 * (y + d)) := by
        field_simp [ne_of_gt hd, ne_of_gt (show 0 < y + d by positivity)]
      _ < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hxy' : x / d * sin a < y / d * sin a :=
    mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hd).2 hxy) hspos
  unfold crossingProbability
  apply mul_lt_mul_of_pos_left _ (div_pos (by norm_num) pi_pos)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity) (continuous_conditionalCrossingProbability x d).continuousOn
    (continuous_conditionalCrossingProbability y d).continuousOn
  · intro b hb
    apply min_le_min_left
    apply mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hd).2 hxy.le)
    exact sin_nonneg_of_nonneg_of_le_pi hb.1.le (by linarith [hb.2, pi_pos])
  · refine ⟨a, ⟨hapos.le, ha⟩, ?_⟩
    unfold conditionalCrossingProbability
    rw [min_eq_right hy1.le, min_eq_right (hxy'.le.trans hy1.le)]
    exact hxy'

/-- Every conditional probability is at most one, hence so is its average. -/
theorem crossingProbability_le_one (l d : ℝ) : crossingProbability l d ≤ 1 := by
  have hp : (0 : ℝ) ≤ π / 2 := by positivity
  have hi :=
    (continuous_conditionalCrossingProbability l d).intervalIntegrable (μ := volume) 0 (π / 2)
  have h := intervalIntegral.integral_mono_on hp hi
    (continuous_const.intervalIntegrable (μ := volume) 0 (π / 2))
    (fun a _ => min_le_left (1 : ℝ) (l / d * sin a))
  have hh := mul_le_mul_of_nonneg_left h (div_nonneg (by norm_num) pi_pos.le)
  unfold crossingProbability
  convert hh using 1
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  field_simp [Real.pi_ne_zero]

/-- The probability tends to one as needle length tends to infinity. -/
theorem crossingProbability_tendsto_one {d : ℝ} (hd : 0 < d) :
    Filter.Tendsto (fun l => crossingProbability l d) Filter.atTop (nhds 1) := by
  have hr : Filter.Tendsto (fun l : ℝ => d / l) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul d
  have ha := (continuous_arcsin.tendsto 0).comp hr
  have hlo : Filter.Tendsto (fun l : ℝ => 1 - (2 / π) * arcsin (d / l))
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (ha.const_mul (2 / π))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop d] with l hld
    have hl : 0 < l := lt_of_lt_of_le hd hld
    have hn : 0 ≤ (l / d) * (1 - cos (arcsin (d / l))) :=
      mul_nonneg (div_nonneg hl.le hd.le) (sub_nonneg.2 (cos_le_one _))
    rw [crossingProbability_split hd hld]
    have hp : (2 / π) * (π / 2) = (1 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    have hm := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) pi_pos.le) hn
    nlinarith
  · exact Filter.Eventually.of_forall (fun l => crossingProbability_le_one l d)

end Chapter27
