/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-!
# Crossing-count distribution identities

These are general identities for a measurable natural-valued crossing count.
Integrability and finiteness are explicit; no divergent real series is interpreted
as its default `tsum` value.
-/

@[expose] public section

open MeasureTheory Set

namespace Chapter27

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Ω → ℕ}

/-- The expectation of an integrable count is its probability-weighted count sum. -/
theorem count_expectation_sum (hN : Measurable N)
    (hI : Integrable (fun ω => (N ω : ℝ)) μ) :
    (∫ ω, (N ω : ℝ) ∂μ) = ∑' n : ℕ, (n : ℝ) * μ.real {ω | N ω = n} := by
  have hm : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (μ.map N) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable
  have hi : Integrable (fun n : ℕ => (n : ℝ)) (μ.map N) :=
    (integrable_map_measure hm hN.aemeasurable).2 hI
  rw [← integral_map hN.aemeasurable hm, integral_countable hi]
  apply tsum_congr
  intro n
  rw [map_measureReal_apply hN (measurableSet_singleton n)]
  simp only [smul_eq_mul, mul_comm]
  rfl

/-- The count weights are summable whenever the count is integrable. -/
theorem count_expectation_summable (hN : Measurable N)
    (hI : Integrable (fun ω => (N ω : ℝ)) μ) :
    Summable (fun n : ℕ => (n : ℝ) * μ.real {ω | N ω = n}) := by
  have hm : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (μ.map N) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable
  have hi : Integrable (fun n : ℕ => (n : ℝ)) (μ.map N) :=
    (integrable_map_measure hm hN.aemeasurable).2 hI
  rw [← Measure.sum_smul_dirac (μ.map N)] at hi
  have hs := hi.summable_of_dirac
  convert hs using 1
  funext n
  rw [← measureReal_def, map_measureReal_apply hN (measurableSet_singleton n)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    mul_comm]
  rfl

/-- Positive-count events partition into the disjoint events of counts `1,2,3,...`. -/
theorem count_probability_sum (hN : Measurable N) :
    μ {ω | 1 ≤ N ω} = ∑' n : ℕ, μ {ω | N ω = n + 1} := by
  have heq : {ω | 1 ≤ N ω} = ⋃ n : ℕ, {ω | N ω = n + 1} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨N ω - 1, by omega⟩
    · rintro ⟨n, hn⟩
      omega
  rw [heq]
  apply measure_iUnion
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    simp only [mem_ofPred_eq] at hi hj
    omega
  · intro n
    exact hN (measurableSet_singleton (n + 1))

/-- In a finite probability experiment the unweighted crossing probabilities are summable. -/
theorem count_probability_summable [IsFiniteMeasure μ] (hN : Measurable N) :
    Summable (fun n : ℕ => μ.real {ω | N ω = n + 1}) := by
  apply ENNReal.summable_toReal
  rw [← count_probability_sum hN]
  exact measure_ne_top μ _

/-- The real-valued probability of a positive count is the sum of positive count masses. -/
theorem count_probability_real_sum [IsFiniteMeasure μ] (hN : Measurable N) :
    μ.real {ω | 1 ≤ N ω} = ∑' n : ℕ, μ.real {ω | N ω = n + 1} := by
  simp only [measureReal_def]
  rw [count_probability_sum hN]
  exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ _)

/-- If at most one crossing can occur almost surely, expectation equals hit probability. -/
theorem count_expectation_eq_probability [IsFiniteMeasure μ] (hN : Measurable N)
    (hshort : ∀ᵐ ω ∂μ, N ω ≤ 1) :
    (∫ ω, (N ω : ℝ) ∂μ) = μ.real {ω | 1 ≤ N ω} := by
  have hevent : MeasurableSet {ω | 1 ≤ N ω} := hN (measurableSet_Ici (a := (1 : ℕ)))
  rw [← integral_indicator_one (μ := μ) hevent]
  apply integral_congr_ae
  filter_upwards [hshort] with ω hω
  by_cases hz : N ω = 0
  · simp [Set.indicator, hz]
  · have ho : N ω = 1 := by omega
    simp [Set.indicator, ho]

end Chapter27
