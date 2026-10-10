/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalBook.Chapter_27.Model
public import FormalBook.Chapter_27.Distribution
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The natural-valued crossing count in the needle probability space

The natural count is measurable and integrable under the independent uniform law.
Its ordinary Bochner expectation equals the iterated average in `Model`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace Chapter27

/-- Number of reached ruled lines, expressed as a natural-valued random variable. -/
noncomputable def needleCount (l d : ℝ) (p : ℝ × ℝ) : ℕ :=
  (offsetCrossings (heightRatio l d p.1) p.2).toNat

lemma measurable_needleCount (l d : ℝ) : Measurable (needleCount l d) := by
  unfold needleCount offsetCrossings heightRatio
  exact (measurable_of_countable Int.toNat).comp ((by fun_prop :
    Measurable (fun p : ℝ × ℝ => p.2 + l / d * sin p.1)).floor)

lemma positionAngleMeasure_mem_ae :
    ∀ᵐ p ∂positionAngleMeasure, p ∈ Ioc (0 : ℝ) (π / 2) ×ˢ Ioc (0 : ℝ) 1 := by
  rw [positionAngleMeasure, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

lemma needleCount_cast_eq {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d)
    {p : ℝ × ℝ} (hp : p ∈ Ioc (0 : ℝ) (π / 2) ×ˢ Ioc (0 : ℝ) 1) :
    (needleCount l d p : ℝ) = (offsetCrossings (heightRatio l d p.1) p.2 : ℝ) := by
  have hs : 0 ≤ sin p.1 := sin_nonneg_of_nonneg_of_le_pi hp.1.1.le
    (by linarith [hp.1.2])
  have hr : 0 ≤ heightRatio l d p.1 := mul_nonneg (div_nonneg hl hd.le) hs
  have hn := offsetCrossings_nonneg hr hp.2.1.le
  have heq : (needleCount l d p : ℤ) = offsetCrossings (heightRatio l d p.1) p.2 :=
    Int.toNat_of_nonneg hn
  exact_mod_cast heq

lemma needleCount_bound {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d)
    {p : ℝ × ℝ} (hp : p ∈ Ioc (0 : ℝ) (π / 2) ×ˢ Ioc (0 : ℝ) 1) :
    ‖(needleCount l d p : ℝ)‖ ≤ l / d + 1 := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (needleCount l d p) : (0 : ℝ) ≤ needleCount l d p),
    needleCount_cast_eq hl hd hp]
  have hf := Int.floor_le (p.2 + heightRatio l d p.1)
  have hr := mul_le_mul_of_nonneg_left (sin_le_one p.1) (div_nonneg hl hd.le)
  dsimp [offsetCrossings, heightRatio] at *
  linarith [hp.2.2]

theorem integrable_needleCount_position {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    Integrable (fun p => (needleCount l d p : ℝ)) positionAngleMeasure := by
  have hm : Measurable (fun p => (needleCount l d p : ℝ)) := by
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_needleCount l d)
  apply (integrable_const (l / d + 1)).mono' hm.aestronglyMeasurable
  filter_upwards [positionAngleMeasure_mem_ae] with p hp
  exact needleCount_bound hl hd hp

theorem integrable_needleCount {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    Integrable (fun p => (needleCount l d p : ℝ)) needleLaw := by
  exact (integrable_needleCount_position hl hd).smul_measure ENNReal.ofReal_ne_top

/-- The actual count's Bochner expectation is the iterated independent average. -/
theorem integral_needleCount {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    (∫ p, (needleCount l d p : ℝ) ∂needleLaw) = expectedCrossings l d := by
  have heq : (fun p => (needleCount l d p : ℝ)) =ᵐ[positionAngleMeasure]
      (fun p => (offsetCrossings (heightRatio l d p.1) p.2 : ℝ)) := by
    filter_upwards [positionAngleMeasure_mem_ae] with p hp
    exact needleCount_cast_eq hl hd hp
  have hi := (integrable_needleCount_position hl hd).congr heq
  rw [needleLaw, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / π), smul_eq_mul]
  unfold expectedCrossings
  congr 1
  rw [integral_congr_ae heq, positionAngleMeasure, integral_prod _ hi]
  simp only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2),
    intervalIntegral.integral_of_le zero_le_one]

/-- The chapter's weighted count distribution formula instantiated in the needle experiment. -/
theorem expectedCrossings_distribution {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    expectedCrossings l d =
      ∑' n : ℕ, (n : ℝ) * needleLaw.real {p | needleCount l d p = n} := by
  rw [← integral_needleCount hl hd]
  exact count_expectation_sum (measurable_needleCount l d) (integrable_needleCount hl hd)

theorem expectedCrossings_distribution_summable {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    Summable (fun n : ℕ => (n : ℝ) * needleLaw.real {p | needleCount l d p = n}) :=
  count_expectation_summable (measurable_needleCount l d) (integrable_needleCount hl hd)

lemma crossingEvent_eq_positive_count (l d : ℝ) :
    crossingEvent l d = {p | 1 ≤ needleCount l d p} := by
  ext p
  change hitsLine (heightRatio l d p.1) p.2 ↔
    1 ≤ (offsetCrossings (heightRatio l d p.1) p.2).toNat
  rw [hitsLine_iff]
  omega

/-- The chapter's unweighted count distribution formula for the crossing probability. -/
theorem needleProbability_distribution (l d : ℝ) :
    needleProbability l d = ∑' n : ℕ, needleLaw.real {p | needleCount l d p = n + 1} := by
  rw [needleProbability, crossingEvent_eq_positive_count]
  exact count_probability_real_sum (measurable_needleCount l d)

theorem needleProbability_distribution_summable (l d : ℝ) :
    Summable (fun n : ℕ => needleLaw.real {p | needleCount l d p = n + 1}) :=
  count_probability_summable (measurable_needleCount l d)

end Chapter27
