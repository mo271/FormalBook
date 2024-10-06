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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered

open Real
open RealInnerProductSpace
open BigOperators
open Classical

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

-- porting note: waiting for
-- https://leanprover-community.github.io/mathlib-port-status/file/analysis/inner_product_space/basic

-- Not quite sure what we actually need here, want to have ℝ-vector space with inner product.
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq V]

theorem cauchy_schwarz_inequality (a b : V) : ⟪ a, b ⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have h: ∀ (x : ℝ), ‖x • a + b‖ ^ 2 = x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
    simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
    simp only [inner_add_add_self, inner_smul_right, inner_smul_left, conj_trivial,
        add_left_inj, real_inner_comm]
    intro x
    ring_nf
  by_cases ha : a = 0
  · rw [ha]
    simp
  · by_cases hl : (∃ (l : ℝ),  b = l • a)
    · obtain ⟨l, hb⟩ := hl
      rw [hb]
      simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
      simp only [inner_add_add_self, inner_smul_right, inner_smul_left, conj_trivial,
        add_left_inj]
      ring_nf
      rfl
    · have : ∀ (x : ℝ), 0 < ‖x • a + b‖ := by
        intro x
        by_contra hx
        simp only [norm_pos_iff, ne_eq, Decidable.not_not] at hx
        absurd hl
        use -x
        rw [← add_zero (-x•a), ← hx]
        simp only [neg_smul, neg_add_cancel_left]
      have : ∀ (x : ℝ), 0 < ‖x • a + b‖^2 := by
        exact fun x ↦ sq_pos_of_pos (this x)
      have : ∀ (x : ℝ), 0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
        convert this
        exact (h _).symm
      have : ∀ (x : ℝ), 0 <  ‖a‖ ^ 2 * x * x  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2 := by
        intro x
        calc
          0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := this x
          _ = ‖a‖ ^ 2 * x * x  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2  := by ring_nf
      have ha_sq : ‖a‖ ^ 2 ≠ 0 := by aesop
      have := discrim_lt_zero ha_sq this
      unfold discrim at this
      have  : (2 * inner a b) ^ 2 < 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by linarith
      linarith


theorem harmonic_geometric_arithmetic₁ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by sorry



theorem harmonic_geometric_arithmetic₂ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by sorry


theorem harmonic_geometric_arithmetic₃ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by sorry

