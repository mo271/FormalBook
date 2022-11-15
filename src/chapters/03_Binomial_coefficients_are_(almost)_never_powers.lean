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
open finset
open_locale nat big_operators
/-!
# Binomial coefficients are (almost) never powers

## TODO
  - (1)
  - (2)
  - (3)
  - (4)

### Sylvester's Theorem
There is no proof given in the book, perhaps check out Erdős' for a proof to formalize.
-/
theorem sylvester (k n : ℕ) (h: 2*k ≤ n ): ∃ p, k < p ∧ p.prime ∧ p ∣ choose n k :=
begin
  sorry,
end

/-
### Erdo's Theorem
Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/
theorem binomials_coefficients_never_powers (k l m n : ℕ) (h_l : 2 ≤ l) (h_k : 4 ≤ k)
(h_n : k ≤ n - 4) : choose n k ≠ m^l :=
begin

  /- Assumption that n ≥ 2k -/
  have h_wlog : ∀ (k' : ℕ) (h_k' : 4 ≤ k') (h_n' : k' ≤ n - 4), 2*k' ≤ n → choose n k' ≠ m^l := by
  { clear h_k h_n k,
    intros k h_k h_n h,
    by_contra H,
    -- main proof here proceeding in four steps

    -- STEP (1) : ∃ p prim : n ≥ p^l > k^l ≥ k² 
    have h₁: ∃ p, nat.prime p ∧ p^l ≤ n ∧ k^l < p^l ∧ k^2 ≤ k^l := by
    { have h_sylvester := sylvester k n h,
      cases h_sylvester with p hp,
      cases hp with h_pk h_right,
      cases h_right with h_p h_p_div,
      use p,
      split,
      -- prove that p is prim
      { exact h_p, },
      { split,
        -- prove p^l ≤ n
        { -- p^l ∣ choose n k
          have h_p_div2 : p ∣ m^l := by
            { rw ← H, 
            exact h_p_div, }, 
          have h_pl_div : p^l ∣ m^l := by
            { sorry, }, 
          have h_pl_div2 : p^l ∣ choose n k := by
            { rw H,
            exact h_pl_div, },
          -- p^l ∣ n!/ (k! * (n-k)!)
          have h_pl_div_fac : p^l ∣ (n.factorial / (k.factorial * (n-k).factorial)) := by
            { have h_n'help : n-4 ≤ n := by
                { exact nat.sub_le n 4, },
              have h_n' : k ≤ n := by
                { exact le_trans h_n h_n'help, },
              rw ← nat.choose_eq_factorial_div_factorial h_n',
              exact h_pl_div2, },
          -- p^l ∣ (n*...*(n-k+1)) /  k!
          

          --have L : list.ico,
          --have S : finset ℕ := by
            --{exact finset.Icc l l,},
          have h_rw_fac1 : n.factorial / (n-k).factorial = n*(n-k+1) := by
            { sorry, },
            --{ induction k with k h_ind,
            --rw tsub_zero n,
            --have hh : n-0 = n, exact tsub_zero n},
          --have h_help : (n.factorial / (k.factorial * (n-k).factorial)) = (n-k+1).factorial / k.factorial := by
            --{ have h_help' n.factorial / (n-k).factorial = (n-k+1).factorial, }, 
          sorry, },
        { split,
          -- prove k^l < p^l
          { exact nat.pow_lt_pow_of_lt_left (h_pk)(gt_of_ge_of_gt h_l two_pos), },
          -- prove k² ≤ k^l
          { exact nat.pow_le_pow_of_le_right (pos_of_gt h_k) h_l,  }, 
        }, 
      }, 
    },
      
    -- STEP (2) : Breakdown of numerator factros n-j = a_j m_j^l whereas a_j pairwise distinct
    have h₂ : ∀ (n k p : ℕ) (h_kleqn : k ≤ n) (h_klp : k < p), 
    choose n k = ∏ i  in Icc (n-k+1) n , i * 1/k.factorial := by
    { sorry, },
    have h_binom_fac : choose n k = n.factorial / ( k.factorial * (n-k).factorial) := by
    { sorry, },
    have h_red_fac : n.factorial / (n-k).factorial = ∏ i in Icc (n-k+1) n, i := by
    { sorry, },

    --have h_rw_num : 
    
    -- STEP (3) : a_i are integers 1..k


    -- STEP (4) : Contradiciton


    sorry, 
  },



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