import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import FormalBook.Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import FormalBook.Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real Set

@[simp]
theorem intervalIntegral.integral_inv_sqrt_one_sub_sq {a b : ℝ} :
    ∫ x : ℝ in a..b, (√(1 - x ^ 2))⁻¹ = (arcsin b - arcsin a) := by
  convert_to (∫ x : ℝ in a..-1, (√(1 - x ^ 2))⁻¹) + ∫ x : ℝ in -1..b, (√(1 - x ^ 2))⁻¹ =
      (arcsin (-1) - arcsin a) + (arcsin b - arcsin (-1)) using 1
  · simp [integral_add_adjacent_intervals]
  · ring
  suffices ∀ t, ∫ x : ℝ in -1..t, (√(1 - x ^ 2))⁻¹ = arcsin t - arcsin (-1) by
    congr 2
    · rw [integral_symm, this a, neg_sub]
    · rw [this b]
  clear a b
  intro t
  wlog ht : t ≤ 1
  · replace ht := le_of_not_ge ht
    calc
      _ = (∫ x : ℝ in -1..1, (√(1 - x ^ 2))⁻¹) + ∫ x : ℝ in 1..t, (√(1 - x ^ 2))⁻¹ := by
        simp [integral_add_adjacent_intervals]
      _ = π + ∫ x : ℝ in 1..t, 0 := by
        congr 1
        · simpa using this 1 (by norm_num)
        · refine integral_congr fun x hx => ?_
          rw [inv_eq_zero, sqrt_eq_zero']
          suffices x ≤ -1 ∨ x ≥ 1 by rcases this with this | this <;> nlinarith only [this]
          simp [uIcc] at hx
          grind only
      _ = _ := by simp [←pi_div_two_eq_arcsin.mpr ht]
  calc
    _ = ∫ x : ℝ in -1..t, deriv arcsin x := by simp [deriv_arcsin]
    _ = _ := by
      apply intervalIntegral.integral_deriv_eq_sub_uIoo
      · apply continuous_arcsin.continuousOn
      · intro x hx
        simp [uIoo] at hx
        rw [differentiableAt_arcsin]
        grind only
      · simp

@[simp]
theorem intervalIntegral.integral_inv_sq_add_sq {a b c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, (c ^ 2 + x ^ 2)⁻¹ = c⁻¹ * (arctan (b / c) - arctan (a / c)) := calc
  _ = ∫ x : ℝ in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [intervalIntegral.integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp
