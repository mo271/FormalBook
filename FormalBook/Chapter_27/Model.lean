/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalBook.Chapter_27.Calculus
public import FormalBook.Chapter_27.ModelBase

/-!
# Probability and expected crossings of a randomly dropped needle

The sample consists of an independent uniform acute inclination and a uniform
lower-end offset modulo the line spacing. The event below is the actual event of
reaching a horizontal ruled line, rather than a probability assigned by formula.
-/

@[expose] public section

open MeasureTheory Set Real

namespace Chapter27

/-- Lebesgue measure on the rectangle of folded inclinations and normalized offsets. -/
noncomputable def positionAngleMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc 0 (π / 2))).prod (volume.restrict (Ioc 0 1))

/-- The normalized independent uniform position and inclination law. -/
noncomputable def needleLaw : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (2 / π) • positionAngleMeasure

/-- The vertical displacement divided by the line spacing. -/
noncomputable def heightRatio (l d a : ℝ) : ℝ := l / d * sin a

/-- At least one ruled line is reached. The first coordinate is inclination and
the second is the lower endpoint's position as a fraction of the line spacing. -/
def crossingEvent (l d : ℝ) : Set (ℝ × ℝ) :=
  {p | hitsLine (heightRatio l d p.1) p.2}

/-- Probability of a crossing, measured in the independent uniform sample space. -/
noncomputable def needleProbability (l d : ℝ) : ℝ := (needleLaw).real (crossingEvent l d)

/-- Expected number of crossings, including for needles longer than the line spacing. -/
noncomputable def expectedCrossings (l d : ℝ) : ℝ :=
  (2 / π) * ∫ a in 0..π / 2, ∫ u in (0 : ℝ)..1,
    (offsetCrossings (heightRatio l d a) u : ℝ)

lemma measurableSet_crossingEvent (l d : ℝ) : MeasurableSet (crossingEvent l d) := by
  unfold crossingEvent hitsLine heightRatio
  exact measurableSet_le measurable_const (by fun_prop)

instance finite_angleMeasure : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (π / 2))) :=
  isFiniteMeasure_restrict.mpr (by simp)

instance finite_offsetMeasure : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp)

instance finite_positionAngleMeasure : IsFiniteMeasure positionAngleMeasure := by
  unfold positionAngleMeasure
  infer_instance

lemma positionAngleMeasure_univ : positionAngleMeasure univ = ENNReal.ofReal (π / 2) := by
  simp [positionAngleMeasure, Measure.prod_apply, Real.volume_Ioc]

instance probability_needleLaw : IsProbabilityMeasure needleLaw where
  measure_univ := by
    rw [needleLaw, Measure.smul_apply, smul_eq_mul, positionAngleMeasure_univ,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 / π)]
    have h : (2 / π) * (π / 2) = 1 := by field_simp
    rw [h, ENNReal.ofReal_one]

/-- A line intersects the vertical projection of the segment exactly when the
normalized crossing criterion holds. Boundary offsets are excluded here. -/
theorem ruled_line_intersection_iff {l d a u : ℝ} (hd : 0 < d) (hu : u ∈ Ioo 0 1)
    :
    (∃ n : ℤ, (n : ℝ) * d ∈ Icc (u * d) (u * d + l * sin a)) ↔
      hitsLine (heightRatio l d a) u := by
  have heq : u + heightRatio l d a = (u * d + l * sin a) / d := by
    unfold heightRatio
    field_simp
  have hiff : hitsLine (heightRatio l d a) u ↔ d ≤ u * d + l * sin a := by
    unfold hitsLine
    rw [heq, le_div_iff₀ hd, one_mul]
  constructor
  · rintro ⟨n, hlo, hhi⟩
    have hnpos : (0 : ℝ) < n := by
      have : 0 < (n : ℝ) * d := lt_of_lt_of_le (mul_pos hu.1 hd) hlo
      exact pos_of_mul_pos_right this hd.le
    have hn : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnline : d ≤ (n : ℝ) * d := by nlinarith
    exact hiff.mpr (hnline.trans hhi)
  · intro h
    refine ⟨1, ?_, ?_⟩
    · simp only [Int.cast_one, one_mul]
      nlinarith [hu.2]
    · simp only [Int.cast_one, one_mul]
      exact hiff.mp h

/-- Fubini's theorem turns the geometric event probability into the angle average. -/
theorem needleProbability_eq_crossingProbability {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) :
    needleProbability l d = crossingProbability l d := by
  have hevent := measurableSet_crossingEvent l d
  have hi : Integrable ((crossingEvent l d).indicator (fun _ => (1 : ℝ)))
      positionAngleMeasure := integrable_const.indicator hevent
  rw [needleProbability, needleLaw, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / π)]
  rw [← integral_indicator_one (μ := positionAngleMeasure) hevent]
  rw [positionAngleMeasure, integral_prod _ hi]
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  unfold crossingProbability
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at ha
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hsin : 0 ≤ sin a := sin_nonneg_of_nonneg_of_le_pi ha.1 (by linarith [ha.2])
  have hh : 0 ≤ heightRatio l d a := mul_nonneg (div_nonneg hl hd.le) hsin
  change (∫ u in (0 : ℝ)..1, if hitsLine (heightRatio l d a) u then 1 else 0) =
    conditionalCrossingProbability l d a
  rw [integral_hitsLine hh]
  rfl

/-- The expected crossing count is linear in length for every nonnegative length. -/
theorem expectedCrossings_eq (l d : ℝ) : expectedCrossings l d = 2 * l / (π * d) := by
  unfold expectedCrossings
  simp_rw [integral_offsetCrossings]
  unfold heightRatio
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [cos_zero, cos_pi_div_two, sub_zero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem expectedCrossings_add (x y d : ℝ) :
    expectedCrossings (x + y) d = expectedCrossings x d + expectedCrossings y d := by
  simp only [expectedCrossings_eq]
  ring

theorem expectedCrossings_nat_mul (n : ℕ) (l d : ℝ) :
    expectedCrossings (n * l) d = n * expectedCrossings l d := by
  simp only [expectedCrossings_eq]
  ring

theorem expectedCrossings_mono {x y d : ℝ} (hd : 0 < d) (hxy : x ≤ y) :
    expectedCrossings x d ≤ expectedCrossings y d := by
  simp only [expectedCrossings_eq]
  exact div_le_div_of_nonneg_right (by linarith) (mul_pos pi_pos hd).le

end Chapter27
