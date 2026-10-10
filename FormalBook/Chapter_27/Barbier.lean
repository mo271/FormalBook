/-
Copyright 2026 The FormalBook Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The algebra and limiting argument in Barbier's proof

The expectation and polygon comparison assumptions in this file are explicit.
The geometric containment and almost-sure crossing counts are not asserted here.
-/

@[expose] public section

open Filter Topology

namespace Chapter27

/-- The properties of the expected crossing count used by Barbier. -/
structure BarbierExpectation (E : ℝ → ℝ) : Prop where
  add : ∀ x y, 0 ≤ x → 0 ≤ y → E (x + y) = E x + E y
  monotone : MonotoneOn E (Set.Ici 0)

namespace BarbierExpectation

variable {E : ℝ → ℝ} (h : BarbierExpectation E)

theorem zero : E 0 = 0 := by
  have := h.add 0 0 (by norm_num) (by norm_num)
  simp only [zero_add] at this
  linarith

theorem nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ E x := by
  simpa [h.zero] using h.monotone (by norm_num : 0 ∈ Set.Ici (0 : ℝ)) hx hx

theorem nat_mul (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : E (n * x) = n * E x := by
  induction n with
  | zero => simp [h.zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      h.add _ _ (mul_nonneg (Nat.cast_nonneg n) hx) hx, ih]
    ring

theorem nat_div (m n : ℕ) (hn : 0 < n) :
    E ((m : ℝ) / n) = ((m : ℝ) / n) * E 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm := h.nat_mul m (x := 1) (by norm_num)
  have he := h.nat_mul n (x := (m : ℝ) / n) (by positivity)
  rw [mul_div_cancel₀ _ hn'] at he
  simp only [mul_one] at hm
  rw [hm] at he
  apply (mul_left_cancel₀ hn')
  calc
    (n : ℝ) * E ((m : ℝ) / n) = m * E 1 := he.symm
    _ = n * ((m : ℝ) / n * E 1) := by field_simp [hn']

/-- Nonnegative additivity and monotonicity force a linear expectation. -/
theorem linear {x : ℝ} (hx : 0 ≤ x) : E x = E 1 * x := by
  have hf := (tendsto_nat_floor_mul_div_atTop hx).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := (tendsto_nat_ceil_mul_div_atTop hx).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply le_antisymm
  · apply ge_of_tendsto (hc.const_mul (E 1))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hp := h.monotone hx (by positivity)
      ((le_div_iff₀ hn').2 (by simpa [mul_comm] using Nat.le_ceil (x * n)))
    simpa [h.nat_div ⌈x * (n : ℝ)⌉₊ n (by omega), mul_comm] using hp

  · apply le_of_tendsto (hf.const_mul (E 1))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hp := h.monotone (by positivity) hx
      ((div_le_iff₀ hn').2 (by
        simpa [mul_comm] using Nat.floor_le (mul_nonneg hx hn'.le)))
    simpa [h.nat_div ⌊x * (n : ℝ)⌋₊ n (by omega), mul_comm] using hp

/-- The rational scaling equation stated in the chapter, on its nonnegative domain. -/
theorem rational_mul (r : ℚ) (hr : 0 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    E ((r : ℝ) * x) = (r : ℝ) * E x := by
  rw [h.linear (mul_nonneg (by exact_mod_cast hr) hx), h.linear hx]
  ring

/-- A polygonal needle's sum of piece expectations depends only on total length. -/
theorem polygon {ι : Type*} (s : Finset ι) (length : ι → ℝ)
    (hlen : ∀ i ∈ s, 0 ≤ length i) :
    ∑ i ∈ s, E (length i) = E 1 * ∑ i ∈ s, length i := by
  simp_rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => h.linear (hlen i hi)

end BarbierExpectation

/-- Perimeter of the regular `n`-gon inscribed in a circle of diameter `d`. -/
def inscribedPerimeter (d : ℝ) (n : ℕ) : ℝ := n * d * Real.sin (Real.pi / n)

/-- Perimeter of the regular `n`-gon circumscribed about that circle. -/
def circumscribedPerimeter (d : ℝ) (n : ℕ) : ℝ := n * d * Real.tan (Real.pi / n)

/-- The inscribed regular polygon's perimeter is at most the circumference. -/
theorem inscribedPerimeter_le {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : 3 ≤ n) :
    inscribedPerimeter d n ≤ d * Real.pi := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp := mul_le_mul_of_nonneg_left
    (Real.sin_le (by positivity : 0 ≤ Real.pi / (n : ℝ)))
    (mul_nonneg (Nat.cast_nonneg n) hd)
  have he : (n : ℝ) * d * (Real.pi / n) = d * Real.pi := by
    field_simp [hn']
    <;> ring
  simpa only [inscribedPerimeter, he] using hp

/-- The circumscribed regular polygon's perimeter is at least the circumference. -/
theorem le_circumscribedPerimeter {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : 3 ≤ n) :
    d * Real.pi ≤ circumscribedPerimeter d n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hangle : Real.pi / n < Real.pi / 2 := by
    rw [div_lt_iff₀ hn']
    nlinarith [mul_le_mul_of_nonneg_left hn3 Real.pi_pos.le, Real.pi_pos]
  have hp := mul_le_mul_of_nonneg_left
    (Real.le_tan (by positivity : 0 ≤ Real.pi / (n : ℝ)) hangle)
    (mul_nonneg (Nat.cast_nonneg n) hd)
  have he : (n : ℝ) * d * (Real.pi / n) = d * Real.pi := by
    field_simp [hn'.ne']
    <;> ring
  simpa only [circumscribedPerimeter, he] using hp

private theorem polygonAngle_tendsto :
    Tendsto (fun n : ℕ => Real.pi / n) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_const_div_atTop_nhds_zero_nat Real.pi, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact div_ne_zero Real.pi_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))

theorem inscribedPerimeter_tendsto (d : ℝ) :
    Tendsto (inscribedPerimeter d) atTop (𝓝 (d * Real.pi)) := by
  have ht := (Real.tendsto_sin_div_nhdsNE_zero.comp polygonAngle_tendsto).const_mul
    (d * Real.pi)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [inscribedPerimeter]
  field_simp [Real.pi_ne_zero, hn']
  <;> ring

theorem circumscribedPerimeter_tendsto (d : ℝ) :
    Tendsto (circumscribedPerimeter d) atTop (𝓝 (d * Real.pi)) := by
  have ht := (Real.tendsto_tan_div_nhdsNE_zero.comp polygonAngle_tendsto).const_mul
    (d * Real.pi)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [circumscribedPerimeter]
  field_simp [Real.pi_ne_zero, hn']
  <;> ring

/-- Barbier's squeeze argument, conditional on the geometric polygon comparisons. -/
theorem barbier_calibration {c d : ℝ} (hd : 0 < d)
    (hins : ∀ n : ℕ, 3 ≤ n → c * inscribedPerimeter d n ≤ 2)
    (hcirc : ∀ n : ℕ, 3 ≤ n → 2 ≤ c * circumscribedPerimeter d n) :
    c = 2 / (Real.pi * d) := by
  have hle : c * (d * Real.pi) ≤ 2 :=
    le_of_tendsto ((inscribedPerimeter_tendsto d).const_mul c)
      (by filter_upwards [eventually_ge_atTop 3] with n hn using hins n hn)
  have hge : 2 ≤ c * (d * Real.pi) :=
    ge_of_tendsto ((circumscribedPerimeter_tendsto d).const_mul c)
      (by filter_upwards [eventually_ge_atTop 3] with n hn using hcirc n hn)
  apply (eq_div_iff (mul_ne_zero Real.pi_ne_zero hd.ne')).2
  nlinarith

/-- The final expectation formula from the explicitly assumed polygon comparisons. -/
theorem barbier_expectation {E : ℝ → ℝ} (h : BarbierExpectation E)
    {d : ℝ} (hd : 0 < d)
    (hins : ∀ n : ℕ, 3 ≤ n → E 1 * inscribedPerimeter d n ≤ 2)
    (hcirc : ∀ n : ℕ, 3 ≤ n → 2 ≤ E 1 * circumscribedPerimeter d n)
    {length : ℝ} (hlen : 0 ≤ length) :
    E length = 2 * length / (Real.pi * d) := by
  rw [h.linear hlen, barbier_calibration hd hins hcirc]
  ring

end Chapter27
