module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

open Real

@[simp, nolint simpNF]
theorem arctan_sqrt_three : arctan (√3) = π / 3 := by
  rw [←tan_pi_div_three, arctan_tan]
  all_goals
  · field_simp
    norm_num
