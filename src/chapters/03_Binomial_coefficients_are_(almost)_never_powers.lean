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
open nat
/-!
# Binomial coefficients are (almost) never powers

## TODO
  - (1)
  - (2)
  - (3)
  - (4)

There is no proof given in the book, perhaps check out Erdős' for a proof to formalize.
-/
theorem sylvester (k n : ℕ) (h: n ≥ 2*k): ∃ p, p > k ∧ p.prime ∧ p ∣ choose n k :=
begin
  sorry,
end

/-
Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/
theorem binomials_coefficients_never_powers (k l m n : ℕ) (h_l : l ≥ 2) (h_k : 4 ≤ k)
(h_n : k ≤ n - 4) : choose n k ≠ m^l :=
begin
  have h_wlog : ∀ (k' : ℕ) (h_k' : 4 ≤ k') (h_n' : k' ≤ n - 4), n ≥ 2*k' → choose n k' ≠ m^l := by
  { clear h_k h_n k,
    intros k h_k h_n h,
    /- main proof here proceeding in four steps
    (1) -/
    have h₀: ∃ p, nat.prime p ∧ n ≥ p^l ∧ p^l > k^l ∧ k^l ≥ k^2 := by
    { have h_sylvester := sylvester k n h,
      cases h_sylvester with p hp,
      cases hp with h_pk h_right,
      cases h_right with h_p h_p_div,
      use p,
      split,
      { exact h_p, },
      { split,
        { sorry, },
        { split,
          { sorry, },
          { sorry, }, } }, },
    sorry, },
  cases em (n ≥ 2*k) with h_2k,
  { exact h_wlog k h_k h_n h_2k, },
  { /- This is just transforming the cases k -> n - k, so that we can use the
    extra condition n ≥ 2*k in the proof above. -/
    have h_n' : k ≤ n := le_trans h_n (nat.sub_le n 4),
    rw ←choose_symm h_n',
    let k' := n - k,
    have h_k'_def: k' = n - k := by refl,
    have: n ≥ 2*k':= by
    { simp at h,
      have h': n ≤ 2 * k := le_of_lt h,
      simp [h_k'_def],
      zify,
      zify at h',
      ring_nf,
      rw sub_le_iff_le_add,
      have := add_le_add_right h' n,
      ring_nf at this,
      exact this, },
    have h_4_n: 4 ≤ n := le_trans (le_trans h_k h_n) (nat.sub_le n 4),
    have h_n_l : k' ≤ n - 4 := by
    { simp [h_k'_def],
      zify,
      sorry, },
    have h_k_l : 4 ≤ k' := by
    { simp [h_k'_def],
      zify,
      zify at h_n,
      exact le_sub.mp h_n, },
    exact h_wlog k' h_k_l h_n_l this, }
end
