import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open Real

@[simp]
theorem arctan_sqrt_three : arctan (√3) = π / 3 := by
  rw [←tan_pi_div_three, arctan_tan]
  all_goals
  · field_simp
    norm_num
