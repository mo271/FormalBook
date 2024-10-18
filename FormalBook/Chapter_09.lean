/-
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

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
