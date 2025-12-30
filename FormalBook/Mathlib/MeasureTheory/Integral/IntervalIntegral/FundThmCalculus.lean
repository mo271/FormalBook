import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

theorem intervalIntegral.integral_deriv_eq_sub_uIoo
    {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ uIoo a b, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, hab, uIoo_of_le] at hcont hderiv
    rw [integral_eq_sub_of_hasDerivAt_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivAt) hint]
  · simp only [uIcc_of_ge, hab, uIoo_of_ge] at hcont hderiv
    rw [integral_symm]
    rw [integral_eq_sub_of_hasDerivAt_of_le
      hab hcont (fun x hx => (hderiv x hx).hasDerivAt) hint.symm]
    rw [neg_sub]
