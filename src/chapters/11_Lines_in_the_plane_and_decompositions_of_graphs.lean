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
import geometry.euclidean.basic

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real_inner_product_space

/-!
# Lines in the plane and decompositions of graphs

## TODO
  - Theorem 1.
    - proof
      - Claim
  - Theorem 2.
    - proof
  Theorem 3.
    - proof
  Theorem 4.
    - proof
  Appendix: Basic graph concepts
-/

variables {V : Type*} {Pl : Type*} [inner_product_space ℝ V] [metric_space Pl]
    [normed_add_torsor V Pl]
local notation `⟪`x`, `y`⟫` := @inner ℝ V _ x y
include V

theorem one (n : ℕ) (P : finset V) (h_card: P.card = n)
-- a line is given by two points; there is no line that contains all points
(h: ¬ (∃ (v₀ v₁ : V), ∀ (p : P), ∃ r_p : ℝ, v₀ +ᵥ r_p • v₁ = p )) :
∃ (w₀ w₁ : V) , ∃ (p₀ p₁ ∈ P), p₀ ≠ p₁ ∧
(∀ (p ∈ P), ∃ (r : ℝ), w₀ +ᵥ r • w₁ = p ↔ (p = p₀ ∨ p = p₁)) :=
begin
  sorry,
end
