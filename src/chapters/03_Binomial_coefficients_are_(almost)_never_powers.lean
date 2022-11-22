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
Authors: Moritz Firsching, Christopher Schmidt
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
theorem sylvester (k n : ℕ) (h : n ≥ 2*k): ∃ p, p > k ∧ p.prime ∧ p ∣ choose n k :=
begin
  sorry,
end

lemma desc_factorial_eq_prod (n : ℕ) : ∀ (k : ℕ), k ≤ n →
  n.desc_factorial k = ∏ i in range k, (n - i) :=
begin
  induction n with n hn,
  { intros h h_klen,
    rw le_zero_iff.mp h_klen,
    simp only [nat.desc_factorial_zero, zero_tsub, range_zero, prod_const, card_empty, pow_zero], },
  { intro k,
    cases k,
    { have := hn 0 (zero_le n),
      intros hsucc,
      simp only [nat.desc_factorial_zero, range_zero, prod_empty], },
    { intro h_klenn,
    rw nat.succ_desc_factorial_succ,
    have h_4lek_n := nat.succ_le_succ_iff.mp h_klenn,
    rw hn k h_4lek_n,
    rw prod_range_succ',
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
    rw mul_comm,}, },
end

lemma prime_dvd_prod (p : ℕ) (hp : _root_.prime p) {s : finset ℕ } {f : ℕ → ℕ}:
p ∣ ∏ i in s, f i → ∃ i, i ∈ s ∧ p ∣ (f i) :=
begin
  rw ← prod_to_list,
  intro h,
  have := (prime.dvd_prod_iff (hp)).mp h,
  cases this with i hi,
  simp at hi,
  cases hi with hi hpi,
  cases hi with j hj,
  use j,
  cases hj,
  rw ←hj_right at hpi,
  exact ⟨hj_left, hpi⟩,
end

lemma desc_factorial_div_fac (n k p : ℕ) (h_klen : k ≤ n) (hp : _root_.prime p)
(h : p ∣ n.desc_factorial k) : ∃ i ∈ range k, p ∣ n - i :=
begin
  rw desc_factorial_eq_prod n k h_klen at h,
  convert prime_dvd_prod p hp h,
  simp only [mem_Ico, zero_le', true_and, exists_prop, mem_range],
end

lemma factor_in_desc_factorial (n k p l : ℕ) (h_4lekleqn : k<=n) (h_p : k < p) (hp: _root_.prime p )
(h_pow_div: p^l ∣ n.desc_factorial k) :
∃ (i : ℕ), (i ≤ k) ∧ p^l ∣ (n - i) :=
begin
have h_one_fac : 1 ≤ l → ∃! i ∈ (range k), p ∣ (n - i) := by
{ intro hl,
  have h_exists : ∃ (i : ℕ), i  ∈ (range k) ∧ p ∣ (n - i) := by
  { have h_div : p ∣ n.desc_factorial k := by {
    have h_p_div : p ∣ p^l := by {
      nth_rewrite 0 ←pow_one p,
      exact pow_dvd_pow p hl, },
    exact dvd_trans h_p_div h_pow_div, },
    have := desc_factorial_div_fac n k p h_4lekleqn hp h_div,
    cases this with j hj,
    use j,
    simp at hj,
    cases hj,
    exact ⟨mem_range.mpr hj_left, hj_right ⟩, },
  cases h_exists with i h_i,
  have h_unique: (i ∈ range k ∧ p ∣ n - i) ∧
                 ∀ (y : ℕ), y ∈ range k → p ∣ n - y → y = i := by
  { split,
    {exact h_i,},
    { cases h_i,
      intros j h_j_left h_j_right,
      simp only [nat.Ico_zero_eq_range, mem_range] at h_j_left,
      simp only [nat.Ico_zero_eq_range, mem_range] at h_i_left,
      cases h_j_right with q_j,
      cases h_i_right with q_i,
      have h_in : i≤n := by { sorry, },
      have h_jn : j≤n := by { sorry, },
      zify at *,
      have h_i_sub_j : (i : ℤ) - j = p*(q_i - q_j) := by { sorry, },
      have h_abs : |(i : ℤ) - j| < k := by { sorry, },
      have h_abs' : |(i : ℤ) - j| < p := lt_trans h_abs h_p,
      have h_q_diff_zero : (q_i - q_j) = 0 := by { sorry, },
      have h_diff : (i : ℤ) - j = 0 := by { sorry, },
      sorry, }, },
  refine ⟨i, _⟩,
  simp only [true_and, exists_unique_iff_exists, exists_prop, and_imp],
  exact h_unique, },
induction l with l hl,
{ use 0,
  simp only [zero_le', pow_zero, is_unit.dvd, nat.is_unit_iff, and_self], },
{ have h_p_prod: p ^ l * p = p ^ l.succ := by
  { nth_rewrite 1 ←pow_one p,
    rw ←pow_add p _ _ , },
  have one_le_succ: 1 ≤ l.succ := by
  { rw nat.succ_eq_add_one, simp only [le_add_iff_nonneg_left, zero_le'], },
  replace h_one_fac := h_one_fac one_le_succ,
  cases h_one_fac with i hi,
  simp at hi,
  use i,
  sorry,
  },
end


/-
### Erdo's Theorem
Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/
theorem binomials_coefficients_never_powers (k l m n : ℕ) (h_2lel : 2 ≤ l) (h_4lek : 4 ≤ k)
(h_klen4 : k ≤ n - 4) : choose n k ≠ m^l :=
begin
  /- Assumption that n ≥ 2k -/
  have h_wlog : ∀ (k' : ℕ) (h_4lek' : 4 ≤ k') (h_klen4' : k' ≤ n - 4), 2*k' ≤ n → choose n k' ≠ m^l := by
  { clear h_4lek h_klen4 k,
    intros k h_4lek h_klen4 h,
    have h_klen: k ≤ n := by 
    { exact le_trans h_klen4 (nat.sub_le n 4), },
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
          have h_p_div_ml : p ∣ m^l := by
            { rw ← H,
            exact h_p_div, },
          have h_pl_div_ml : p^l ∣ m^l := by
            { have help : p ∣ m := by 
              { exact nat.prime.dvd_of_dvd_pow (h_p)(h_p_div_ml), },
              exact pow_dvd_pow_of_dvd help l, },
          have h_pl_div_binom : p^l ∣ choose n k := by
            { rw H,
            exact h_pl_div_ml, },
          -- p^l ∣ n!/ (k! * (n-k)!)
          have h_pl_div_fac : p^l ∣ (n.factorial / (k.factorial * (n-k).factorial)) := by
          { have h_klen4'help : n-4 ≤ n := by
              { exact nat.sub_le n 4, },
            have h_klen4' : k ≤ n := by
              { exact le_trans h_klen4 h_klen4'help, },
            rw ← nat.choose_eq_factorial_div_factorial h_klen4',
            exact h_pl_div_binom, },

          have h_fraction: (n.factorial / (k.factorial * (n - k).factorial)) =
            (n.factorial / (n - k).factorial) / k.factorial := by
          { sorry, },
          have h_pl_div_ml_frac: p^l ∣ (n.factorial /(n - k).factorial) := by
          { sorry, },
          have h_pl_div_ml_desc: p^l ∣ n.desc_factorial k := by
          { convert  h_pl_div_ml_frac,
            exact desc_factorial_eq_div h_klen, },
          have h_p_pow_dvd := factor_in_desc_factorial n k p l h_klen (gt_iff_lt.mp h_pk) (nat.prime_iff.mp h_p)
            h_pl_div_ml_desc,
          cases h_p_pow_dvd with i hi,
          cases hi,
          have : p^l ≤ n - i := by
          { refine  nat.le_of_dvd _ hi_right,
            simp only [tsub_pos_iff_lt],
            linarith, },
          have h_klen4i : n - i ≤ n := nat.sub_le n i,
          exact le_trans this h_klen4i, },
        { split,
          -- prove k^l < p^l
          { exact nat.pow_lt_pow_of_lt_left (h_pk)(gt_of_ge_of_gt h_2lel two_pos), },
          -- prove k² ≤ k^l
          { exact nat.pow_le_pow_of_le_right (pos_of_gt h_4lek) h_2lel,  },
        },
      },
    },

    -- STEP (2) : Breakdown of numerator factros n-j = a_j m_j^l whereas a_j pairwise distinct
    have h₂ : ∀ (n k p : ℕ) (h_4lekleqn : k ≤ n) (h_4leklp : k < p),
    choose n k = ∏ i in Icc (n - k + 1) n , i * 1/k.factorial := by
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
  { exact h_wlog k h_4lek h_klen4 h_2k, },
  { /- This is just transforming the cases k -> n - k, so that we can use the
    extra condition n ≥ 2*k in the proof above. -/
    have h_klen4' : k ≤ n := le_trans h_klen4 (nat.sub_le n 4),
    rw ←choose_symm h_klen4',
    let k' := n - k,
    have h_4lek'_def: k' = n - k := by refl,
    have: n ≥ 2*k':= by
    { simp at h,
      have h': n ≤ 2 * k := le_of_lt h,
      simp [h_4lek'_def],
      zify,
      zify at h',
      ring_nf,
      rw sub_le_iff_le_add,
      have := add_le_add_right h' n,
      ring_nf at this,
      exact this, },
    have h_4_n: 4 ≤ n := le_trans (le_trans h_4lek h_klen4) (nat.sub_le n 4),
    have h_klen4_l : k' ≤ n - 4 := by
    { simp [h_4lek'_def],
      zify,
      sorry, },
    have h_4lek_l : 4 ≤ k' := by
    { simp [h_4lek'_def],
      zify,
      zify at h_klen4,
      exact le_sub.mp h_klen4, },
    exact h_wlog k' h_4lek_l h_klen4_l this, }
end

