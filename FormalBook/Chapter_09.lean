/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic

open scoped BigOperators Real
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
theorem euler_series :
  ∑' (n : ℕ+), (1 : ℝ) / n = π ^ 2  / 6 := by
  sorry

theorem euler_series':
   ∑' (k : ℕ), (1 : ℝ) / (2 * k + 1) ^ 2  = π ^ 2  / 8 := by
  sorry

theorem euler_series_3 :
  ∑' (n : ℕ+), (1 : ℝ) / n = π ^ 2  / 6 := by
  sorry

theorem euler_series_4 :
  ∑' (n : ℕ+), (1 : ℝ) / n = π ^ 2  / 6 := by
  sorry
