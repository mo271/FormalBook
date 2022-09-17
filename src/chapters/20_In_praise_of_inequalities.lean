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
import tactic
import analysis.inner_product_space.basic
import algebra.module.basic
import data.real.basic
open_locale real_inner_product_space

/-!
# In praise of inequalities

## TODO
  - Theorem I
    - proof
  - Theorem II
    - proof
      - (A)
      - (B)
    - another proof
    - still another proof
  - Theorem 1
    - proof
  - The tangential triangle
  - Theorem 2
    - proof
  - Theorem 3
    - First proof
    - Second proof
-/

-- Not quite sure what we actually need here, want to have ℝ-vector space with inner product.
variables {V : Type*}  [add_comm_group V] [module ℝ V] [inner_product_space ℝ V] [normed_space ℝ V]

theorem cauchy_schwarz_inequality (a b : V) : ⟪a, b⟫^2 ≤ ∥a∥^2 * ∥b∥^2 :=
begin
  have h: ∀ (x : ℝ), ∥x•a + b∥^2 = x^2*∥a∥^2 + 2*x*⟪a, b⟫ + ∥b∥^2 := by
  { cases em (a = 0),
    { rw h,
      intro x,
      simp only [smul_zero, zero_add, self_eq_add_left],
      sorry, },
    { cases em (∃ (l : ℝ),  b = l•a),
      { sorry, },
      { sorry, }, }, },
  sorry,
end
