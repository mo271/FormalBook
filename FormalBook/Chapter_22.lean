/-
Copyright 2024 the Amsterdam Lean seminar

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching,
Maris Ozols,
Jan Hendriks,
Casper,
Pjotr Buys,
Giacomo,
Dion Leijnse,
Thijs Maessen,
Thomas Koopman,
Jonas van der Schaaf,
Lenny Taelman,
Dhyan Aranha.
-/
import Mathlib.Tactic
/-!
# One square and an odd number of triangles

## TODO
  - Monsky's Theorem
    - proof
      - Lemma 1
        - proof
      - Corollary
        - proof
      - Lemma 2
        - proof
          - (A)
          - (B)
  - Appendix: Extending valuations
    - definition
    - Theorem
      - proof
    - Lemma
      - proof
    - Claim
    - Zorn's Lemma
-/

noncomputable section

open ValuationSubring

lemma inclusion_maximal_valuation (B : Subring ℝ) (h1 : (1/2) ∉ B)
(h2 : ∀(C : Subring ℝ), (B ≤ C) ∧ (1/2) ∉ C → B = C) : ∃(D : ValuationSubring ℝ), D.toSubring = B := by  sorry

lemma valuation_ring_no_half : ∃(B : ValuationSubring ℝ), (1/2) ∉ B := sorry

lemma non_archimedean (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] (K : Type) [Field K] (v : Valuation K Γ₀) :
  (∀(x y : K), v x ≠ v y → v (x + y) = max (v x) (v y)) := sorry

theorem valuation_on_reals : ∃(Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀)
  (v : Valuation ℝ Γ₀), (v (1/2)) > 1 := by
    have h := valuation_ring_no_half
    cases' h with B h
    use B.ValueGroup
    -- We got stuck on giving the group structure. The rest of the proof is below
    -- use B.valuation
    -- have g := valuation_le_one_iff B (1/2)
    -- rw[← not_iff_not] at g
    -- rwa[gt_iff_lt, ← not_le, g]
    sorry

-- lemma valuation_lemma (K : Type) [Field K] (R : Subring K) :
--   ∃(vsr : ValuationSubring R), R.valuation ↔ (∃(Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation K Γ₀), 1 = 1) := sorry
--   (∀ (x : K), (x ≠ 0) → (x ∈ R) ∨ (x⁻¹ ∈ R)) ↔
--   (∃(Γ₀ : Type)  (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation K Γ₀)) := sorry
