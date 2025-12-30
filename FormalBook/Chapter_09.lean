/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Julien Michel
-/
import FormalBook.Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import FormalBook.Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Four times $π^2/6$

## TODO
  - statement
    - first proof
    - second proof
    - The Substitution Formula
    - third proof
    - fourth proof
  - Appendix: The Riemann zeta function
    - (1)
    - (2)
    - (3)
    - (4)
-/

open Real

local notation "ofReal" => ENNReal.ofReal

open Set ENNReal MeasureTheory Filter intervalIntegral

set_option maxHeartbeats 1000000 in
theorem euler_series : ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ = π ^ 2 / 6 := by
  convert_to ∑' n : ℕ, (n : ℝ)⁻¹ ^ 2 = _ using 3 with n
  · simp
  -- Change the index from n to n + 1 to avoid division by zero
  convert_to ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 = _ using 1
  . apply tsum_eq_tsum_of_ne_zero_bij fun n => n.1 + 1
    · simp [Function.Injective]
    · simp; norm_cast; simp; omega
    · simp
  convert_to ∑' n : ℕ, (∫ x : ℝ in 0..1, x ^ n) ^ 2 = _ using 1
  · simp
  -- As every term is nonnegative, we will use ℝ≥0∞ Lebesgue integrals to
  -- facilitate the exchange of sum and integral later with Tonelli's theorem.
  convert_to (∑' n : ℕ, ofReal (∫ x : ℝ in 0..1, x ^ n) ^ 2).toReal = _ using 1
  . rw [tsum_toReal_eq]
    · congr 1 with n
      rw [← ofReal_pow, toReal_ofReal]
      · positivity
      · exact intervalIntegral.integral_nonneg (by norm_num) fun x hx => pow_nonneg hx.1 n
    · finiteness
  convert_to _ = (ofReal (π ^ 2 / 6)).toReal using 1
  · rw [toReal_ofReal]
    positivity
  congr 1
  convert_to ∑' n : ℕ, (∫⁻ x : ℝ in Ioo 0 1, ofReal (x ^ n)) ^ 2 = _ using 4 with n
  . rw [intervalIntegral_eq_integral_uIoc]
    norm_num
    rw [← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · apply IntegrableOn.integrable
      rw [←intervalIntegrable_iff_integrableOn_Ioo_of_le]
      · exact intervalIntegrable_pow n
      · norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact pow_nonneg hx.1.le n
  convert_to ∑' n : ℕ, (∫⁻ x : ℝ in Ioo 0 1, ofReal x ^ n) ^ 2 = _ using 4 with n
  . refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [ofReal_pow hx.1.le]
  -- Introduce indicator functions to extend the integral to all ℝ.
  -- This will facilitate later uses of Tonelli's theorem.
  convert_to ∑' n : ℕ, (∫⁻ x : ℝ, (Ioo 0 1).indicator 1 x * ofReal x ^ n) ^ 2 = _
    using 4 with n
  · simp [←lintegral_indicator, indicator]
  convert_to ∑' n : ℕ, (∫⁻ x : ℝ, (Ioo 0 1).indicator 1 x * ofReal x ^ n) *
    (∫⁻ y : ℝ, (Ioo 0 1).indicator 1 y * ofReal y ^ n) = _ using 3 with n
  · ring_nf
  convert_to ∑' n : ℕ, ∫⁻ x : ℝ, (Ioo 0 1).indicator 1 x * ofReal x ^ n *
    ∫⁻ y : ℝ, (Ioo 0 1).indicator 1 y * ofReal y ^ n = _ using 3 with n
  . rw [lintegral_mul_const _ (by clear * -; measurability)]
  convert_to ∑' n : ℕ, ∫⁻ x : ℝ, ∫⁻ y : ℝ,
    (Ioo 0 1).indicator 1 x * (Ioo 0 1).indicator 1 y * (ofReal x * ofReal y) ^ n = _
      using 5 with n x
  . rw [←lintegral_const_mul _ (by clear * -; measurability)]
    ring_nf
    -- Now we exchange the sum and the integrals using Tonelli's theorem twice.
    -- Using ℝ≥0∞ integrals saves us from checking integrability conditions.
  convert_to ∫⁻ x : ℝ, ∑' n : ℕ, ∫⁻ y : ℝ,
    (Ioo 0 1).indicator 1 x * (Ioo 0 1).indicator 1 y * (ofReal x * ofReal y) ^ n = _
      using 1
  . rw [lintegral_tsum (by clear * -; measurability)]
  convert_to ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∑' n : ℕ,
    (Ioo 0 1).indicator 1 x * (Ioo 0 1).indicator 1 y * (ofReal x * ofReal y) ^ n = _
      using 3 with x
  . rw [lintegral_tsum (by clear * -; measurability)]
  convert_to ∫⁻ x : ℝ, ∫⁻ y : ℝ, (Ioo 0 1).indicator 1 x * (Ioo 0 1).indicator 1 y *
    ((1 - ofReal x * ofReal y)⁻¹) = _ using 5 with x y
  · rw [ENNReal.tsum_mul_left, tsum_geometric]
  -- The integration set in xy-coordinates
  let T := {xy : ℝ × ℝ | xy.1 ∈ Ioo 0 1 ∧ xy.2 ∈ Ioo 0 1}
  -- the 2D change of variables function x = u - v, y = u + v
  let f (uv : ℝ × ℝ) : ℝ × ℝ := (uv.1 - uv.2, uv.1 + uv.2)
  -- the inverse of the 2D change of variables function u = (x + y) / 2, v = (y - x) / 2
  let finv (xy : ℝ × ℝ) : ℝ × ℝ := ((xy.1 + xy.2) / 2, (xy.2 - xy.1) / 2)
  -- The jacobian matrix of the change of variables
  let J : Matrix (Fin 2) (Fin 2) ℝ := ![![1, -1], ![1, 1]]
  -- The linear map associated to the jacobian matrix
  let f' (_ : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    let i := LinearEquiv.finTwoArrow ℝ ℝ
    (i ∘ₗ J.toLin' ∘ₗ i.symm).toContinuousLinearMap
  -- First region of integration in uv-coordinates
  let S1 := {uv : ℝ × ℝ | uv.1 ∈ Ioo 0 2⁻¹ ∧ uv.2 ∈ Ioo (-uv.1) (uv.1)}
  -- Second region of integration in uv-coordinates
  let S2 := {uv : ℝ × ℝ | uv.1 ∈ Ioo 2⁻¹ 1 ∧ uv.2 ∈ Ioo (-(1 - uv.1)) (1 - uv.1)}
  -- Separating line of measure zero in uv-coordinates, to ensure symmetry
  let S3 : Set (ℝ × ℝ) := {2⁻¹} ×ˢ Ioo (-2⁻¹) 2⁻¹
  -- The full integration set in uv-coordinates
  let S := S1 ∪ S2 ∪ S3
  have bijective_f : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ?_
    use finv
    unfold Function.RightInverse Function.LeftInverse f finv
    split_ands
    · simp
    · intro a; ext <;> linarith only
  have fS_eq_T : f '' S = T := by
    ext xy
    simp only [mem_setOf_eq, mem_image, T, f, S]
    constructor
    · intro ⟨uv, h1, h2⟩
      set u := uv.1
      set v := uv.2
      have hx : xy.1 = u - v := by simp [←h2]
      have hy : xy.2 = u + v := by simp [←h2]
      simp [S1, S2, S3] at h1 ⊢
      grind only
    · intro h1
      let u := (xy.1 + xy.2) / 2
      let v := (xy.2 - xy.1) / 2
      use (u, v)
      split_ands
      · simp [S1, S2, S3] at h1 ⊢
        grind only
      · ext <;> simp [u, v] <;> linarith only
  have isOpen_T : IsOpen T := by
    refine IsOpen.and (IsOpen.and ?_ ?_) (IsOpen.and ?_ ?_) <;> apply isOpen_lt <;> fun_prop
  have isOpen_S : IsOpen S := by
    convert_to IsOpen (f ⁻¹' T) using 1
    · have : f ⁻¹' T = S := ((eq_preimage_iff_image_eq bijective_f).mpr fS_eq_T).symm
      rw [this]
    refine IsOpen.preimage ?_ ?_
    · unfold f; fun_prop
    · exact isOpen_T
  have measurableSet_S : MeasurableSet S := by
    unfold S S1 S2 S3
    clear * -; measurability
  convert_to ∫⁻ x : ℝ, ∫⁻ y : ℝ, T.indicator 1 (x, y) * ((1 - ofReal x * ofReal y)⁻¹) = _
    using 6 with x y
  . simp [T, indicator]
    grind only
  -- Using Tonelli's theorem, we couple integrals over ℝ × ℝ to prepare for a change of variables.
  convert_to ∫⁻ xy : ℝ × ℝ, T.indicator 1 xy * ((1 - ofReal xy.1 * ofReal xy.2)⁻¹) = _
    using 1
  . rw [←lintegral_prod fun xy => T.indicator 1 xy * ((1 - ofReal xy.1 * ofReal xy.2)⁻¹)]
    · rw [←Measure.volume_eq_prod]
    · unfold T
      clear * -; measurability
  convert_to ∫⁻ xy : ℝ × ℝ in T, (1 - ofReal xy.1 * ofReal xy.2)⁻¹ = _ using 1
  . rw [←lintegral_indicator]
    · simp [indicator]
    · unfold T
      clear * -; measurability
  -- Now we perform the change of variables x = u - v, y = u + v.
  rw [← fS_eq_T]
  convert_to ∫⁻ uv : ℝ × ℝ in S, 2 * ((1 - ofReal (uv.1 - uv.2) * ofReal (uv.1 + uv.2))⁻¹) = _
    using 1
  . rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (f' := f')]
    · apply setLIntegral_congr_fun
      · exact measurableSet_S
      · intro uv huv
        beta_reduce
        congr 1
        norm_num [f', Matrix.det_fin_two, J]
    · exact measurableSet_S
    · intro uv huv
      refine (hasFDerivWithinAt_of_mem_nhds ?_).mpr ?_
      · rw [mem_nhds_iff]
        use S, by simp, isOpen_S, huv
      · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
        suffices ∀ h, f (uv + h) - f uv - (f' uv) h = 0 by simp [this]
        intro h
        simp [f, f', J, Matrix.mulVec]
        split_ands <;> ring
    · exact bijective_f.injective.injOn
  clear! f finv J f'
  -- Pull the ofReal upwards to prepare going back to regular ℝ valued interval based integrals.
  convert_to ∫⁻ uv : ℝ × ℝ in S, 2 * ((ofReal 1 - ofReal ((uv.1 - uv.2) * (uv.1 + uv.2)))⁻¹) = _
    using 1
  . refine setLIntegral_congr_fun measurableSet_S fun (u, v) huv => ?_
    congr 3
    · norm_num
    rw [ofReal_mul]
    simp [S, S1, S2, S3] at huv
    grind only
  convert_to ∫⁻ uv : ℝ × ℝ in S, 2 * (ofReal (1 - (uv.1 - uv.2) * (uv.1 + uv.2)))⁻¹ = _ using 1
  . refine setLIntegral_congr_fun measurableSet_S fun (u, v) huv => ?_
    congr 2
    rw [ofReal_sub]
    suffices 0 < u - v ∧ 0 < u + v by nlinarith only [this]
    simp [S, S1, S2, S3] at huv
    grind only
  convert_to 2 * ∫⁻ uv : ℝ × ℝ in S, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹) = _ using 1
  . rw [←lintegral_const_mul]
    · refine setLIntegral_congr_fun measurableSet_S fun (u, v) huv => ?_
      congr 1
      rw [ofReal_inv_of_pos]
      suffices 0 < u - v ∧ u - v < 1 ∧ 0 < u + v ∧ u + v < 1 by nlinarith only [this]
      simp [S, S1, S2, S3] at huv
      grind only
    · clear * -; measurability
    -- Split the integral over two simpler regions that will allow us to separate the integrals.
  convert_to 2 * ((∫⁻ uv : ℝ × ℝ in S1, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)) +
            (∫⁻ uv : ℝ × ℝ in S2, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)) +
            (∫⁻ uv : ℝ × ℝ in S3, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹))) = _ using 2
  . unfold S
    rw [lintegral_union, lintegral_union]
    · unfold S2
      clear * -; measurability
    · grind
    · unfold S3
      clear * -; measurability
    · grind
  convert_to (2 * ∫⁻ uv : ℝ × ℝ in S1, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)) +
        2 * ∫⁻ uv : ℝ × ℝ in S2, ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹) = _ using 1
  . rw [setLIntegral_measure_zero S3]
    · ring
    · simp [S3, volume]
  convert_to
    (2 * ∫⁻ uv : ℝ × ℝ, S1.indicator 1 uv * ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)) +
     2 * ∫⁻ uv : ℝ × ℝ, S2.indicator 1 uv * ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹) = _
    using 3
  · rw [←lintegral_indicator]
    · simp [indicator]
    · unfold S1
      clear * -; measurability
  · rw [←lintegral_indicator]
    · simp [indicator]
    · unfold S2
      clear * -; measurability
  -- Separate the integrals over u and v using Tonelli's theorem again.
  convert_to
    (2 * ∫⁻ u : ℝ, ∫⁻ v : ℝ, S1.indicator 1 (u, v) * ofReal ((1 - (u - v) * (u + v))⁻¹)) +
     2 * ∫⁻ u : ℝ, ∫⁻ v : ℝ, S2.indicator 1 (u, v) * ofReal ((1 - (u - v) * (u + v))⁻¹) = _
    using 3
  · rw [←lintegral_prod fun uv => S1.indicator 1 uv * ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)]
    · rw [←Measure.volume_eq_prod]
    · unfold S1
      clear * -; measurability
  · rw [←lintegral_prod fun uv => S2.indicator 1 uv * ofReal ((1 - (uv.1 - uv.2) * (uv.1 + uv.2))⁻¹)]
    · rw [←Measure.volume_eq_prod]
    · unfold S2
      clear * -; measurability
  -- Get rid of the indicator functions
  convert_to
    (2 * ∫⁻ u : ℝ, ∫⁻ v : ℝ, (Ioo 0 2⁻¹).indicator 1 u * (Ioo (-u) u).indicator 1 v *
      ofReal ((1 - (u - v) * (u + v))⁻¹)) +
    2 * ∫⁻ u : ℝ, ∫⁻ v : ℝ, (Ioo 2⁻¹ 1).indicator 1 u * (Ioo (-(1 - u)) (1 - u)).indicator 1 v *
      ofReal ((1 - (u - v) * (u + v))⁻¹) = _ using 8 with u v
  · simp [S1, indicator]
    grind only
  · simp [S2, indicator]
    grind only
  clear! S1 S2 S3 S T
  convert_to
    (2 * ∫⁻ u : ℝ, (Ioo 0 2⁻¹).indicator 1 u * ∫⁻ v : ℝ, (Ioo (-u) u).indicator 1 v *
      ofReal ((1 - (u - v) * (u + v))⁻¹)) +
    2 * ∫⁻ u : ℝ, (Ioo 2⁻¹ 1).indicator 1 u * ∫⁻ v : ℝ, (Ioo (-(1 - u)) (1 - u)).indicator 1 v *
      ofReal ((1 - (u - v) * (u + v))⁻¹) = _ using 1
  . congr 2
    all_goals
    · congr! 2 with u
      rw [←lintegral_const_mul]
      · ring_nf
      · clear *-; measurability
  convert_to
    (2 * ∫⁻ u : ℝ in Ioo 0 2⁻¹, ∫⁻ v : ℝ in Ioo (-u) u,
      ofReal ((1 - (u - v) * (u + v))⁻¹)) +
    2 * ∫⁻ u : ℝ in Ioo 2⁻¹ 1, ∫⁻ v : ℝ in Ioo (-(1 - u)) (1 - u),
      ofReal ((1 - (u - v) * (u + v))⁻¹) = _ using 1
  . simp [←lintegral_indicator, indicator]
  -- Pull the ofReal upwards again to convert the inner integrals to ℝ.
  convert_to
    (2 * ∫⁻ u : ℝ in Ioo 0 2⁻¹,
      ofReal (∫ v : ℝ in Ioo (-u) u, (1 - (u - v) * (u + v))⁻¹)) +
    2 * ∫⁻ u : ℝ in Ioo 2⁻¹ 1,
      ofReal (∫ v : ℝ in Ioo (-(1 - u)) (1 - u), (1 - (u - v) * (u + v))⁻¹) = _ using 1
  . congr 2
    all_goals
    · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      simp at hu
      rw [ofReal_integral_eq_lintegral_ofReal]
      · apply IntegrableOn.integrable
        rw [←integrableOn_Icc_iff_integrableOn_Ioo]
        apply ContinuousOn.integrableOn_Icc
        apply ContinuousOn.inv₀
        · fun_prop
        · intro v hv
          simp at hv
          nlinarith only [hu, hv]
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        simp at hv ⊢
        nlinarith only [hu, hv]
  -- Now compute the inner integrals explicitly.
  -- This will facilitate checking integrability conditions necessary to convert
  -- the outer integrals back to ℝ.
  convert_to
    (2 * ∫⁻ u : ℝ in Ioo 0 2⁻¹, ofReal (∫ v : ℝ in (-u)..u, (1 - (u - v) * (u + v))⁻¹)) +
    2 * ∫⁻ u : ℝ in Ioo 2⁻¹ 1, ofReal (∫ v : ℝ in -(1 - u)..(1 - u), (1 - (u - v) * (u + v))⁻¹) = _
      using 3
  · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu2 : -u ≤ u := by linarith only [hu.1, hu.2]
    simp only [intervalIntegral_eq_integral_uIoc, hu2, uIoc_of_le hu2, ←integral_Ioc_eq_integral_Ioo]
    simp
  · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu2 : -(1 - u) ≤ 1 - u := by linarith only [hu.1, hu.2]
    simp only [intervalIntegral_eq_integral_uIoc, hu2, uIoc_of_le hu2, ←integral_Ioc_eq_integral_Ioo]
    simp
  convert_to
    (2 * ∫⁻ u : ℝ in Ioo 0 2⁻¹, ofReal (∫ v : ℝ in (-u)..u, (√(1 - u ^ 2) ^ 2 + v ^ 2)⁻¹)) +
    2 * ∫⁻ u : ℝ in Ioo 2⁻¹ 1, ofReal (∫ v : ℝ in -(1 - u)..(1 - u), (√(1 - u ^ 2) ^ 2 + v ^ 2)⁻¹)
      = _ using 1
  . congr 2
    all_goals
    · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      congr 1
      refine intervalIntegral.integral_congr fun v hv => ?_
      congr 1
      calc
        1 - (u - v) * (u + v) = 1 - u ^ 2 + v ^ 2 := by ring_nf
        _ = _ := by rw [sq_sqrt (by nlinarith only [hu.1, hu.2])]
  convert_to
    (2 * ∫⁻ u : ℝ in Ioo 0 2⁻¹, ofReal (2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2)))) +
    2 * ∫⁻ u : ℝ in Ioo 2⁻¹ 1, ofReal (2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2)))
      = _ using 1
  . congr 2
    all_goals
    · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      congr 1
      rw [integral_inv_sq_add_sq]
      swap
      · rw [sqrt_ne_zero] <;> nlinarith only [hu.1, hu.2]
      simp_rw [sub_eq_add_neg, ←arctan_neg]
      ring_nf
  have integrable_deriv_g_explicit : IntervalIntegrable
      (fun u ↦ 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2))) volume 0 2⁻¹ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.mul
    apply ContinuousOn.mul
    · exact continuousOn_const
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu; simp at hu; rw [sqrt_ne_zero] <;> nlinarith only [hu]
    · apply continuous_arctan.comp_continuousOn'
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu; simp at hu; rw [sqrt_ne_zero] <;> nlinarith only [hu]
  have integrable_deriv_h_explicit : IntervalIntegrable
      (fun u ↦ 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2))) volume 2⁻¹ 1 := by
    have h1 : IntervalIntegrable (fun u ↦ π * (√(1 - u ^ 2))⁻¹) volume 2⁻¹ 1 :=
      intervalIntegrable_inv_sqrt_one_sub_sq.const_mul π
    apply IntervalIntegrable.mono_fun h1 (by clear * -; measurability)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    replace hu : 2⁻¹ < u ∧ u ≤ 1 := by simp [uIoc] at hu; grind only
    have h2 : 0 ≤ (√(1 - u ^ 2))⁻¹ := by simp
    rw [norm_of_nonneg, norm_of_nonneg]
    · calc
        _ = 2 * arctan ((1 - u) / √(1 - u ^ 2)) * (√(1 - u ^ 2))⁻¹ := by ring
        _ ≤ 2 * (π / 2) * (√(1 - u ^ 2))⁻¹ := by gcongr 2; apply le_of_lt (arctan_lt_pi_div_two _)
        _ = _ := by field_simp
    · nlinarith only [h2, pi_nonneg]
    · have h3 : 0 ≤ arctan ((1 - u) / √(1 - u ^ 2)) := by
        rw [arctan_nonneg]
        apply div_nonneg (by linarith only [hu]) (by simp)
      nlinarith only [h2, h3]
  -- Convert the outer integrals back to ℝ.
  convert_to
    (2 * ofReal (∫ u : ℝ in Ioo 0 2⁻¹, 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2)))) +
    2 * ofReal (∫ u : ℝ in Ioo 2⁻¹ 1, 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2))) = _
      using 3
  · rw [ofReal_integral_eq_lintegral_ofReal]
    · apply IntegrableOn.integrable
      rw [←intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      exact integrable_deriv_g_explicit
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      simp only [Pi.zero_apply]
      have h1 : (√(1 - u ^ 2))⁻¹ ≥ 0 := inv_nonneg_of_nonneg (by simp)
      have h2 : 0 ≤ arctan (u / √(1 - u ^ 2)) := by
        simpa [arctan_nonneg] using div_nonneg (by linarith only [hu.1]) (by simp)
      nlinarith only [h1, h2]
  · rw [ofReal_integral_eq_lintegral_ofReal]
    · apply IntegrableOn.integrable
      rw [←intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      exact integrable_deriv_h_explicit
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      simp only [Pi.zero_apply]
      have h1 : (√(1 - u ^ 2))⁻¹ ≥ 0 := inv_nonneg_of_nonneg (by simp)
      have h3 : 0 ≤ arctan ((1 - u) / √(1 - u ^ 2)) := by
        simpa [arctan_nonneg] using div_nonneg (by nlinarith only [hu.1, hu.2]) (by simp)
      nlinarith only [h1, h3]
  convert_to
    ofReal (2 * (∫ u : ℝ in 0..2⁻¹, 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2)))) +
    ofReal (2 * (∫ u : ℝ in 2⁻¹..1, 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2)))) = _
      using 1
  . congr 1
    all_goals
    · rw [←integral_Ioc_eq_integral_Ioo, intervalIntegral_eq_integral_uIoc]
      norm_num
  convert_to
    ofReal (2 * (∫ u : ℝ in 0..2⁻¹, 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2))) +
    2 * (∫ u : ℝ in 2⁻¹..1, 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2)))) = _ using 1
  . rw [ofReal_add]
    all_goals
    · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      apply intervalIntegral.integral_nonneg
      · norm_num
      · intro u hu
        have h1 : (√(1 - u ^ 2))⁻¹ ≥ 0 := inv_nonneg_of_nonneg (by simp)
        have h2 : 0 ≤ arctan (u / √(1 - u ^ 2)) := by
          simpa [arctan_nonneg] using div_nonneg (by linarith only [hu.1]) (by simp)
        have h3 : 0 ≤ arctan ((1 - u) / √(1 - u ^ 2)) := by
          simpa [arctan_nonneg] using div_nonneg (by linarith only [hu.2]) (by simp)
        nlinarith only [h1, h2, h3]
  -- Now let's go back to ℝ, and compute the remaining integrals.
  congr 1
  -- Primitive appearing in the first integral after substitution
  let g := fun u : ℝ => arctan (u / √(1 - u ^ 2)) ^ 2
  have deriv_g_eq (u : ℝ) (hu : u ∈ Ioo 0 1) :
      deriv g u = 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2)) := by
    simp at hu
    have h1 : √(1 - u ^ 2) ≠ 0 := by rw [sqrt_ne_zero] <;> nlinarith only [hu]
    have h2 : 1 - u ^ 2 ≠ 0 := by nlinarith only [hu]
    have h3 : DifferentiableAt ℝ (fun u ↦ √(1 - u ^ 2)) u := by
      apply DifferentiableAt.comp
      · exact (hasDerivAt_sqrt h2).differentiableAt
      · simp
    have h4 : DifferentiableAt ℝ (fun u ↦ u / √(1 - u ^ 2)) u := by
      apply DifferentiableAt.div
      · simp
      · exact h3
      · exact h1
    show deriv (fun u => ((arctan ∘ fun u => _ / ((sqrt ∘ fun u => _) u)) ^ 2) u) u = _
    erw [deriv_fun_pow, deriv_comp, deriv_fun_div, deriv_comp, deriv_fun_sub]
    erw [deriv_sqrt, deriv_fun_pow]
    erw [Real.deriv_arctan, deriv_id'', deriv_const]
    · simp
      field_simp
    · simp
    · simp
    · exact h2
    · simp
    · simp
    · exact (hasDerivAt_sqrt h2).differentiableAt
    · simp
    · simp
    · exact h3
    · exact h1
    · apply differentiableAt_arctan
    · exact h4
    · apply (differentiableAt_arctan _).comp _ h4
  have integrable_deriv_g : IntervalIntegrable (deriv g) volume 0 2⁻¹ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    convert_to IntegrableOn (fun u => 2 * (√(1 - u ^ 2))⁻¹ * arctan (u / √(1 - u ^ 2))) (Ioo 0 2⁻¹)
      using 0
    · refine integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioo
      simp at hu
      rw [deriv_g_eq u (by split_ands <;> linarith only [hu])]
    rw [←intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    exact integrable_deriv_g_explicit
  have differentiableAt_uIoo_g u (hu : u ∈ uIoo 0 2⁻¹) : DifferentiableAt ℝ g u := by
    simp at hu
    refine differentiableAt_of_deriv_ne_zero ?_
    rw [deriv_g_eq u (by split_ands <;> linarith only [hu])]
    have h1 : √(1 - u ^ 2) ≠ 0 := by rw [sqrt_ne_zero] <;> nlinarith only [hu]
    have h2 : arctan (u / √(1 - u ^ 2)) ≠ 0 := by simp [h1]; linarith
    grind only
  have continuousOn_uIcc_g : ContinuousOn g (uIcc 0 2⁻¹) := by
    convert_to ContinuousOn g (Icc 0 2⁻¹) using 1
    · grind [uIcc]
    apply ContinuousOn.pow
    apply continuous_arctan.comp_continuousOn'
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    simp at hu
    rw [sqrt_ne_zero] <;> nlinarith only [hu]
  -- Primitive appearing in the second integral after substitution
  let h := fun u : ℝ => -2 * arctan ((1 - u) / √(1 - u ^ 2)) ^ 2
  have deriv_h_eq (u : ℝ) (hu : u ∈ Ioo 0 1) :
      deriv h u = 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2)) := by
    simp at hu
    have h1 : √(1 - u ^ 2) ≠ 0 := by rw [sqrt_ne_zero] <;> nlinarith only [hu]
    have h2 : 1 - u ^ 2 ≠ 0 := by nlinarith only [hu]
    have h3 : DifferentiableAt ℝ (fun u ↦ √(1 - u ^ 2)) u := by
      apply DifferentiableAt.comp
      · exact (hasDerivAt_sqrt h2).differentiableAt
      · simp
    have h5 : DifferentiableAt ℝ (HSub.hSub 1) u := DifferentiableAt.sub (by simp) (by simp)
    have h4 : DifferentiableAt ℝ (fun u ↦ (1 - u) / √(1 - u ^ 2)) u := by
      apply DifferentiableAt.div
      · exact h5
      · exact h3
      · exact h1
    show deriv (fun u => -2 * ((arctan ∘ fun u => _ / ((sqrt ∘ fun u => _) u)) ^ 2) u) u = _
    erw [deriv_const_mul]
    erw [deriv_fun_pow, deriv_comp, deriv_fun_div, deriv_comp, deriv_fun_sub]
    erw [deriv_sqrt, deriv_sub, deriv_fun_pow]
    erw [Real.deriv_arctan, deriv_id'', deriv_const]
    · simp
      field_simp
      rw [sq_sqrt (by nlinarith only [hu])]
      ring
    · simp
    · simp
    · simp
    · simp
    · exact h2
    · simp
    · simp
    · exact h5
    · simp
    · exact h5
    · exact h3
    · exact h1
    · apply differentiableAt_arctan
    · exact h4
    · apply (differentiableAt_arctan _).comp _ h4
    · apply (differentiableAt_pow _).comp _ ((differentiableAt_arctan _).comp _ h4)
  have integrable_deriv_h : IntervalIntegrable (deriv h) volume 2⁻¹ 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    convert_to IntegrableOn (fun u => 2 * (√(1 - u ^ 2))⁻¹ * arctan ((1 - u) / √(1 - u ^ 2)))
      (Ioo 2⁻¹ 1) using 0
    · refine integrableOn_congr_fun (fun u ⟨hu1, hu2⟩ => ?_) measurableSet_Ioo
      exact deriv_h_eq u (by split_ands <;> linarith only [hu1, hu2])
    rw [←intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    exact integrable_deriv_h_explicit
  have continuousOn_uIcc_h : ContinuousOn h (uIcc 2⁻¹ 1) := by
    convert_to ContinuousOn h (Icc 2⁻¹ 1) using 1
    · grind [uIcc]
    apply ContinuousOn.mul
    · exact continuousOn_const
    apply ContinuousOn.pow
    apply continuous_arctan.comp_continuousOn'
    set f1 := fun u => (1 - u) / √(1 - u ^ 2)
    set f2 := fun u => √((1 - u) / (1 + u))
    convert_to ContinuousOn f2 (Icc 2⁻¹ 1) using 0
    · refine continuousOn_congr fun u hu => ?_
      unfold f1 f2
      simp at hu
      calc
        _ = √((1 - u) ^ 2) / √(1 - u ^ 2) := by rw [sqrt_sq]; linarith only [hu]
        _ = √(((1 - u) * (1 - u)) / ((1 - u) * (1 + u))) := by
          rw [←sqrt_div]
          · ring_nf
          positivity
        _ = _ := by field_simp
    apply ContinuousOn.sqrt
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    simp at hu
    linarith only [hu]
  have differentiableAt_uIoo_h u (hu : u ∈ uIoo 2⁻¹ 1) : DifferentiableAt ℝ h u := by
    replace hu : (2⁻¹ : ℝ) < u ∧ u < 1 := by grind [uIoo]
    refine differentiableAt_of_deriv_ne_zero ?_
    rw [deriv_h_eq u (by split_ands <;> linarith only [hu])]
    have h1 : √(1 - u ^ 2) ≠ 0 := by rw [sqrt_ne_zero] <;> nlinarith only [hu]
    have h2 : arctan ((1 - u) / √(1 - u ^ 2)) ≠ 0 := by simp [h1]; linarith
    grind only
  convert_to (2 * ∫ u : ℝ in 0..2⁻¹, deriv g u) + 2 * (∫ u : ℝ in 2⁻¹..1, deriv h u) = _
    using 3
  · iterate 2 rw [intervalIntegral_eq_integral_uIoc]
    norm_num
    iterate 2 rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u ⟨hu1, hu2⟩ => ?_
    rw [deriv_g_eq u]
    split_ands <;> nlinarith only [hu1, hu2]
  · iterate 2 rw [intervalIntegral_eq_integral_uIoc]
    norm_num
    iterate 2 rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u ⟨hu1, hu2⟩ => ?_
    rw [deriv_h_eq u]
    split_ands <;> nlinarith only [hu1, hu2]
  convert_to (2 * (g 2⁻¹ - g 0)) + (2 * (h 1 - h 2⁻¹)) = _ using 3
  · rw [integral_deriv_eq_sub_uIoo]
    · exact continuousOn_uIcc_g
    · exact differentiableAt_uIoo_g
    · exact integrable_deriv_g
  · rw [integral_deriv_eq_sub_uIoo]
    · exact continuousOn_uIcc_h
    · exact differentiableAt_uIoo_h
    · exact integrable_deriv_h
  unfold g h
  norm_num
  cancel_denoms
  rw [arctan_inv_of_pos (by norm_num), arctan_sqrt_three]
  field_simp
  norm_num


theorem euler_series' :
   ∑' (k : ℕ), (1 : ℝ) / (2 * k + 1) ^ 2  = π ^ 2  / 8 := by
  sorry

theorem euler_series_3 :
  ∑' (n : ℕ+), (1 : ℝ) / n = π ^ 2  / 6 := by
  sorry

theorem euler_series_4 :
  ∑' (n : ℕ+), (1 : ℝ) / n = π ^ 2  / 6 := by
  sorry
