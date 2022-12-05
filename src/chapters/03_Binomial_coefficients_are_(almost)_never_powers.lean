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
import tactic.qify
import ring_theory.prime
import data.list.prime
import data.nat.sqrt
--set_option trace.simp_lemmas true


open nat
open finset

open_locale nat big_operators
/-!
# Binomial coefficients are (almost) never powers
## TODO
  - Lemmata
  - (1)
  - (2)
  - (3)
  - (4)
### Sylvester's Theorem
There is no proof given in the book, perhaps check out Erdős' for a proof to formalize.
-/
theorem sylvester (k n : ℕ) (h : n ≥ 2*k): ∃ p, p > k ∧ prime p ∧ p ∣ choose n k :=
begin
  sorry,
end

/-!
### Lemmata for Step 1 and Step 2
-/
example (a p : ℕ) (h : p ∣ a) (g : a < p): a = 0 :=
begin
  exact eq_zero_of_dvd_of_lt h g,
end

lemma prime_div_desc_fac (n k m l p : ℕ) (h_1lel : 1 ≤ l) (h_4lek : 4 ≤ k) (h_klen : k ≤ n)
  (h_p : prime p) (h_p_div_binom : p ∣ choose n k) (h_klp : k < p) (H : choose n k = m^l) :
  p^l ∣ n.desc_factorial k :=
begin
  have h_p_div_ml : p ∣ m^l := by
  { rw ← H,
    exact h_p_div_binom, },
  have h_pl_div_ml : p^l ∣ m^l := by
  { have help : p ∣ m := by
    { exact prime.dvd_of_dvd_pow (h_p)(h_p_div_ml), },
    exact pow_dvd_pow_of_dvd help l, },
  have h_pl_div_binom : p^l ∣ choose n k := by
  { rw H,
    exact h_pl_div_ml, },
  have h_pl_div_fac : p^l ∣ (n.factorial / (k.factorial * (n-k).factorial)) := by
  { rw ← nat.choose_eq_factorial_div_factorial h_klen,
    exact h_pl_div_binom, },

  have h_fac_div : (↑k! * ↑(n - k)!) ∣ (n! : ℤ) := by
  { norm_cast,
    exact factorial_mul_factorial_dvd_factorial h_klen, },
  have h_fac_div' : ↑(n - k)! ∣ (n! : ℤ) := dvd_of_mul_left_dvd h_fac_div,
  have h_fac_div'' :  (k! : ℤ) ∣ (↑n! / ↑(n - k)!) := by
  { norm_cast,
    refine (dvd_div_iff ((int.coe_nat_dvd).mp h_fac_div')).mpr _,
    norm_cast at h_fac_div,
    rw mul_comm,
    exact h_fac_div, },
  have h_kfac_ne_zero : (k! : ℚ) ≠ 0 := cast_ne_zero.mpr (factorial_ne_zero k),
  have h_nkfac_ne_zero : ((n - k)! : ℚ) ≠ 0 := cast_ne_zero.mpr (n - k).factorial_ne_zero,
  have : (k! * (n - k)! : ℚ) ≠ 0 := mul_ne_zero h_kfac_ne_zero h_nkfac_ne_zero,
  have h_fraction: (n.factorial / (k.factorial * (n - k).factorial)) =
    (n.factorial / (n - k).factorial) / k.factorial := by
  { zify,
    qify,
    field_simp,
    rw mul_comm,
    left,
    refl, },
  rw h_fraction at h_pl_div_fac,
  have h_pl_div_fac_part: p^l ∣ (n.factorial / (n - k).factorial) := by
  { have h_eq_pl_with_k := exists_eq_mul_right_of_dvd h_pl_div_fac,
    have h_eq_pl : ∃ (r : ℕ), r * p^l = n.factorial / (n - k).factorial := by
    { cases h_eq_pl_with_k with j h_eq,
      use (j * k.factorial),
      have h_rew : j * k.factorial * p^l = p^l * j * k.factorial := by
      { simp only [mul_comm, mul_assoc], },
      rw h_rew,
      rw ← h_eq,
      zify,
      qify,
      field_simp,
      rw mul_comm ((n - k)! : ℚ) _,
      rw mul_assoc, },
    cases h_eq_pl with j h_eq,
    exact dvd.intro_left j h_eq, },
    convert  h_pl_div_fac_part,
    exact desc_factorial_eq_div h_klen,
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

lemma prime_dvd_prod (p : ℕ) (hp : prime p) {s : finset ℕ } {f : ℕ → ℕ}:
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
  rw ← hj_right at hpi,
  exact ⟨hj_left, hpi⟩,
end

lemma desc_factorial_div_fac (n k p : ℕ) (h_klen : k ≤ n) (hp : _root_.prime p)
(h : p ∣ n.desc_factorial k) : ∃ i ∈ range k, p ∣ n - i :=
begin
  rw desc_factorial_eq_prod n k h_klen at h,
  convert prime_dvd_prod p hp h,
  simp only [mem_Ico, zero_le', true_and, exists_prop, mem_range],
end

lemma factor_in_desc_factorial (n k p l : ℕ) (h_klen : k ≤ n) (h_klp : k < p) (hp: _root_.prime p )
(h_pow_div: p^l ∣ n.desc_factorial k) ( h_1lel : 1 ≤ l):
∃ (i : ℕ), (i ≤ k - 1) ∧ p^l ∣ (n - i) :=
begin
have h_one_fac : 1 ≤ l → ∃! i ∈ (range k), p ∣ (n - i) := by
{ intro hl,
  have h_exists : ∃ (i : ℕ), i  ∈ (range k) ∧ p ∣ (n - i) := by
  { have h_div : p ∣ n.desc_factorial k := by
    { have h_p_div_pl : p ∣ p^l := by
      { nth_rewrite 0 ←pow_one p,
        exact pow_dvd_pow p hl, },
      exact dvd_trans h_p_div_pl h_pow_div, },
    have := desc_factorial_div_fac n k p h_klen hp h_div,
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
      have h_in : i ≤ n := le_trans (le_of_lt h_i_left) h_klen,
      have h_jn : j ≤ n := le_trans (le_of_lt h_j_left) h_klen,
      zify at *,
      have h_i_sub_j : (i : ℤ) - j = p*(q_j - q_i) := by
      { have h : (n : ℤ) - j - (n - i) = p * q_j - p * q_i :=
          congr (congr_arg has_sub.sub h_j_right_h) h_i_right_h,
        simp only [sub_sub_sub_cancel_left] at h,
        rw mul_sub,
        exact h,},
      have h_abs : |(i : ℤ) - j| < k := by
      { have h_pos : (i : ℤ) - j < k - 0 := by
        { have h_help : 0 ≤ j := by
          { exact zero_le j, },
          zify at h_help,
          exact int.sub_lt_sub_of_lt_of_le h_i_left h_help, },
        simp only [tsub_zero] at h_pos,
        have h_neg : -((i : ℤ) - j) < k - 0 := by
        { simp only [neg_sub],
          exact int.sub_lt_sub_of_lt_of_le h_j_left (cast_nonneg i), },
        simp only [neg_sub, tsub_zero] at h_neg,
        cases em ((i : ℤ) - j ≤ 0),
        { have h_help : |(i : ℤ) - j | = -(i - j) := abs_of_nonpos h,
          rw h_help,
          norm_num,
          exact h_neg, },
        { have : (i : ℤ) - j ≥ 0 := by { exact le_of_not_ge h, },
          have h_help : |(i : ℤ) - j| = i - j := abs_of_nonneg this,
          rw h_help,
          exact h_pos, }, },
      have h_abs' : |(i : ℤ) - j| < p := by
      { exact lt_trans h_abs h_klp, },
      have h_abs_div: (p : ℤ) ∣ |(i : ℤ) - j| := by
      { simp only [dvd_abs],
        use (↑q_j - (q_i : ℤ)),
        exact h_i_sub_j, },
      have h_q_diff_zero : |((i : ℤ) - j)| = 0 :=
        int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg (↑i - ↑j)) h_abs' h_abs_div,
      have h_diff : (i : ℤ) - j = 0 := by
      { exact abs_eq_zero.mp h_q_diff_zero, },
      have h_help : (i : ℤ) = j := by
      { exact sub_eq_zero.mp h_diff},
      exact eq.symm h_help, }, },
  refine ⟨i, _⟩,
  simp only [true_and, exists_unique_iff_exists, exists_prop, and_imp],
  exact h_unique, },
  -- new Version

  -- tbc

--induction l with l hl,
--{ use 0,
  --simp only [zero_le', pow_zero, is_unit.dvd, is_unit_one, and_self], },
--{ have h_klp_prod: p ^ l * p = p ^ l.succ := by
  --{ nth_rewrite 1 ←pow_one p,
    --rw ←pow_add p _ _ , },
  --have one_le_succ: 1 ≤ l.succ := by
  --{ rw nat.succ_eq_add_one, simp only [le_add_iff_nonneg_left, zero_le'], },
  --replace h_one_fac := h_one_fac one_le_succ,
  --cases h_one_fac with i hi,
  --simp at hi,
  --use i,
  --sorry,
  --},
  sorry,
end

lemma factor_in_desc_factorial2 (n k p l : ℕ) (h_klen : k ≤ n) (h_klp : k < p) (hp: _root_.prime p )
(h_pow_div: p^l ∣ n.desc_factorial k) ( h_1lel : 1 ≤ l):
∃! (i : ℕ), (i ≤ k - 1) ∧ p^l ∣ (n - i) :=
begin
  sorry, 
end

/-!
### Lemmata for Step 2
-/
definition power_div (l z : ℕ) := (finset.range (z + 1)).filter (λ i, i^l ∣ z)

lemma power_div_nonempty (l z : ℕ) : (power_div l z).nonempty :=
begin
 cases (em (0 < z)),
  { use 1,
    rw power_div,
    simp only [mem_filter, mem_range, add_pos_iff, lt_one_iff, eq_self_iff_true,
     or_true, true_and],
    split,
    { exact succ_lt_succ h, },
    { simp only [one_pow, is_unit.dvd, is_unit_one], }, },
  { use 0,
    rw power_div,
    simp only [not_lt, le_zero_iff] at h,
    simp only [mem_filter, mem_range, add_pos_iff, lt_one_iff, eq_self_iff_true, or_true, true_and],
    rw h,
    simp only [dvd_zero],},
end

definition largest_power_divisor (l z: ℕ) : ℕ := (power_div l z).max' (power_div_nonempty l z)

lemma largest_power_divisor_divides (l z : ℕ) : (largest_power_divisor l z)^l ∣ z :=
begin
  have h := (power_div l z).max'_mem (power_div_nonempty l z),
  rw ←largest_power_divisor at h,
  have : (power_div l z) = (finset.range (z + 1)).filter (λ i, i^l ∣ z) := by refl,
  rw this at h,
  simp at h,
  exact h.2,
end

definition mFct (l n: ℕ) : ℕ → ℕ := λ j, (largest_power_divisor l (n - j))

definition aFct (l n: ℕ) : ℕ → ℕ := λ j, (n - j)/(mFct l n j)^l

lemma decompose_n_j (n j l : ℕ) : n - j = (aFct l n j)*(mFct l n j)^l :=
begin
  have : (mFct l n j)^l ∣ n - j := largest_power_divisor_divides l (n - j),
  rw aFct,
  rw nat.div_mul_cancel this,
end

/-!
### Lemmata for Step 3
-/
definition s_1tok (k : ℕ) := (finset.range (k + 1)).filter(λ i, 1 ≤ i ∧ i ≤ k)

definition a_values (l n k : ℕ) := finset.image (aFct l n) (range k)

lemma fac_eq_prod (n : ℕ) : n.factorial = ∏ i in Icc 1 n, i :=
begin
  induction n with n h_ind,
  -- induction start
  { simp only [factorial_zero, Icc_eq_empty_of_lt, lt_one_iff, prod_empty], },
  -- indcution step
  { simp only [factorial_succ],
    rw h_ind,
    have h_help : Icc 1 n.succ = (Icc 1 n) ∪ (singleton n.succ) := by
    { refine subset.antisymm _ _,
      -- left in right
      { intros k hk,
        simp only [mem_union, mem_Icc, mem_singleton],
        simp at hk,
        cases em (k ≤ n),
        { left,
          split,
          { exact hk.left, },
          { exact h, }, },
        { right,
          simp only [not_le] at h,
          have h2 := hk.right,
          exact ge_antisymm (succ_le_iff.mpr (h)) h2,}, },
      -- right in left
      { intros k hk,
        simp only [mem_union, mem_Icc, mem_singleton],
        simp at hk,
        cases hk with hk1 hk2,
        { split,
          { exact hk1.left, },
          { have := hk1.right,
            exact le_succ_of_le this, }, },
        { split,
          { rw hk2,
            have help : 0 < n.succ := by
            { exact ne_zero.pos (succ n), },
            exact succ_le_iff.mpr help, },
          { exact (eq.symm hk2).ge}, }, }, },
    have h_help2 : disjoint (Icc 1 n) (singleton n.succ) := by
    { simp only [disjoint_singleton_right, mem_Icc, not_and, not_le],
      intro p,
      rw nat.succ_eq_one_add,
      simp only [lt_add_iff_pos_left, lt_one_iff], },
    rw h_help,
    have h := prod_union h_help2,
    rw h,
    simp,
    apply mul_comm, },
end 

/-!
### Lemmata for Step 4
-/
lemma h_mul_div (a b : ℕ) (h_b : b ≠ 0) : a * b / b = 1 :=
begin
  sorry,
end

lemma h_div_mul (a b : ℕ) (h_b : b ≠ 0) : a / b * b = 1 :=
begin
  sorry,
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
    -- inequalities needed
    have h_klen : k ≤ n := le_trans h_klen4 (nat.sub_le n 4),
    have h_1lel : 1 ≤ l := le_of_succ_le (h_2lel),
    -- proof by contradiciton
    by_contra H,
    -- main proof here proceeding in four steps
    -- STEP (1) : ∃ p prim : n ≥ p^l > k^l ≥ k²
    have h₁: ∃ p, prime p ∧ p^l ≤ n ∧ k^l < p^l ∧ k^2 ≤ k^l := by
    { have h_sylvester := sylvester k n h,
      cases h_sylvester with p hp,
      cases hp with h_klp h_right,
      cases h_right with h_p h_p_div_binom,
      use p,
      split,
      -- prove that p is prim
      { exact h_p, },
      { split,
        -- prove p^l ≤ n
        { -- use of lemmata
          have h_pl_div_desc: p^l ∣ n.desc_factorial k := by
          { exact prime_div_desc_fac n k m l p h_1lel h_4lek h_klen h_p h_p_div_binom h_klp H, },
          have h_klp_pow_dvd := factor_in_desc_factorial n k p l h_klen (gt_iff_lt.mp h_klp) (h_p)
            h_pl_div_desc h_1lel,
          -- working with them
          cases h_klp_pow_dvd with i hi,
          cases hi,
          have : p^l ≤ n - i := by
          { refine  nat.le_of_dvd _ hi_right,
            simp only [tsub_pos_iff_lt],
            have h_ilk : i < k := by
            { have hk : 0 < k := lt_of_lt_of_le four_pos h_4lek,
              zify at hi_left,
              zify,
              exact int.lt_of_le_sub_one hi_left, },
            exact lt_of_lt_of_le h_ilk h_klen, },
          have h_klen4i : n - i ≤ n := nat.sub_le n i,
          exact le_trans this h_klen4i, },
        { split,
          -- prove k^l < p^l
          { exact nat.pow_lt_pow_of_lt_left (h_klp)(gt_of_ge_of_gt h_2lel two_pos), },
          -- prove k² ≤ k^l
          { exact nat.pow_le_pow_of_le_right (pos_of_gt h_4lek) h_2lel,  }, }, }, },
    -- STEP (2) : aⱼ only have prime divisors ≤ k ; aᵢ ≠ aⱼ
    have h₂ : ∀ (j ≤ k - 1),
      (∀ (q : ℕ), q ∣ (aFct l n j) ∧ prime q → q ≤ k) ∧
      (∀ i ≤ k - 1, i ≠ j → (aFct l n i) ≠ (aFct l n j)) := by
    { intros j h_jlek1,
      split,
      -- First Claim: aⱼ only have prime divisors ≤ k
      { intros q hq,
        cases hq with h_q_div_a h_q,
        by_contra h_klq,
        simp only [not_le] at h_klq,
        -- pre work, important result q ∣ n - j and q ∣ choose n k
        have h_q_div_nj : q ∣ (n - j) := by
        { have h_q_div_am := dvd_mul_of_dvd_left h_q_div_a (mFct l n j),
          have h_am_eq_nj : aFct l n j * mFct l n j = n - j := by
          { sorry, },
          rw ← h_am_eq_nj,
          exact h_q_div_am, },
        have h_q_div_desc_fact : q ∣ n.desc_factorial k := by
        { sorry, },
        have h_q_div_binom : q ∣ choose n k := by
        { have h_q_div_desc_fact : q ∣ n.desc_factorial k := by
          { sorry, },
          have h_descfac_div_binom : n.desc_factorial k ∣ choose n k := by
          { sorry, }, 
          exact dvd_trans h_q_div_desc_fact h_descfac_div_binom, },
        -- introducing lemmata by using q ∣ choose n k
        have h_ql_div_desc: q^l ∣ n.desc_factorial k := by
          { exact prime_div_desc_fac n k m l q h_1lel h_4lek h_klen h_q h_q_div_binom h_klq H, },
        have h_klp_pow_dvd := factor_in_desc_factorial2 n k q l h_klen (gt_iff_lt.mp h_klq) (h_q)
            h_ql_div_desc h_1lel,
        -- working with lemmata 
        cases h_klp_pow_dvd with i hi,
        cases hi with h_ex h_uni,
        cases h_ex,
        have h_qldivam : q^l ∣ ((aFct l n i) * (mFct l n i)^l) := by
        { sorry, },
        have h_qdivml : q ∣ (mFct l n i)^l := by
        { sorry, }, 
        have h_qldivml : q^l ∣ (mFct l n i)^l := by
        { sorry, },
        have h_qnotdiva : ¬ (q ∣ (aFct l n i)) := by
        { sorry, },
        -- applying result of lemmata by using q ∣ n - j
        have h_ieqj : j = i := by
        { sorry, },
        rw h_ieqj at h_q_div_a,
        exact h_qnotdiva h_q_div_a, },
      -- Second Claim : aᵢ ≠ aⱼ
      { intros i h_ilek1 h_inej,
        -- here we perform the proof by contradiciton which we will use for both cases below
        have h_cases : ∀ (x y : ℕ), (x ≤ k - 1 ∧ y ≤ k - 1 ∧ x < y) → aFct l n x ≠ aFct l n y := by
        { intros x y h,
          cases h with h_x h,
          cases h with h_y h_xley, 
          by_contra,
          -- will help us rewriting
          have h_mjlmi : (mFct l n j) + 1 ≤ mFct l n i := by
          { have h_njlni : n - i < n - j := by
            { sorry, },
            have h_amjlami : (aFct l n j) * (mFct l n j)^l < (aFct l n i) * (mFct l n i)^l := by
            { sorry, },
            have h_mjlmi_pow : (mFct n l j)^l < (mFct n l i)^l := by
            { sorry, },
            have h_mjlmi : mFct n l j < mFct n l i := by
            { sorry, },
            sorry, },
          -- n < k²
          have h_sqrtnlk : n.sqrt < k := by
          { have h_ineq1 : n.sqrt < l * (n / 2 + 1).sqrt := by
            { sorry, },
            have h_ineq2 : l * (n / 2 + 1).sqrt ≤ l * (n - k + 1).sqrt := by
            { sorry, },
            have h_ineq3 : l * (n - k + 1).sqrt ≤ 
              l * ((aFct l n j) * (mFct l n j)^l).sqrt := by
            { sorry, },
            have h_ineq4 : l * ((aFct l n j) * (mFct l n j)^l).sqrt ≤ 
              (aFct l n j) * l * (mFct l n j)^(l - 1) := by
            { sorry, },
            have h_ineq5 : (aFct l n j) * l * (mFct l n j)^(l - 1) ≤ 
              (aFct l n j) * ((mFct l n j + 1)^l - (mFct l n j)^l) := by
            { sorry, },
            have h_ineq6 : (aFct l n j) * ((mFct l n j + 1)^l - (mFct l n j)^l) ≤ 
              (aFct l n j) * ((mFct l n i)^l * (mFct l n j)^l) := by 
            { sorry, }, 
            have h_eq7 : (aFct l n j) * ((mFct l n i)^l * (mFct l n j)^l) = (n - i) - (n - j) := by
            { sorry, },
            have h_eq8 :  (n - i) - (n - j) = j - i := by
            { sorry, },
            have h_ineq9 : j - i < k := by 
            { sorry, },
            linarith, },
          have h_nlk2 : n < k^2 := by
          { exact sqrt_lt'.mp h_sqrtnlk, },
          -- usage of h₁ : k² < n
          cases h₁ with p h,
          cases h with h_p h,
          cases h with hplen h,
          cases h with h_kllpl h_k2kl,
          have h_from1 : k^2 < n := by
          { have h_k2lpl : k^2 < p^l := gt_of_gt_of_ge h_kllpl h_k2kl, 
            exact gt_of_ge_of_gt hplen h_k2lpl, },
          exact nat.lt_asymm h_nlk2 h_from1, },
        cases em (i < j),
        { -- case i < j using h_cases
          have h_casesij := h_cases i j,
          have h_help : i ≤ k - 1 ∧ j ≤ k - 1 ∧ i < j := by
          { split, 
            { exact h_ilek1, }, 
            { split, 
              { exact h_jlek1, },
              { exact h_1, }, }, }, 
          exact h_casesij h_help, },
        { -- case i > j using h_cases
          simp only [not_lt] at h_1,
          have h_1' := (ne.symm h_inej).lt_of_le h_1, 
          have h_casesji := h_cases j i,
          have h_help : j ≤ k - 1 ∧ i ≤ k - 1 ∧ j < i := by
          { split, 
            { exact h_jlek1, },
            { split,
              { exact h_ilek1, }, 
              { exact h_1', }, }, }, 
          exact ne.symm (h_cases j i h_help), }, }, },
    -- STEP (3) : a_i are integers 1..k
    have h₃ : a_values l n k = s_1tok k := by
    { dsimp only [a_values, s_1tok],
      have h_div : (∏ i in (a_values l n k), i) ∣ k.factorial := by
      { sorry, },
      have h_eq : (∏ i in (a_values l n k), i) = k.factorial := by
      { sorry, },
      rw fac_eq_prod at h_eq,
      sorry, },
    -- divide in two cases
    cases em (l = 2),
    -- Special Case l = 2 by Contradicition
    { have h_4ins : 4 ∈ (s_1tok k) := by
      { dsimp only [s_1tok],
        simp only [mem_filter, mem_range, one_le_bit0_iff, succ_pos', true_and],
        split,
        { exact lt_succ_iff.mpr h_4lek, },
        { exact h_4lek, }, }, 
      have h_4inavalues : 4 ∈ (a_values l n k) := by
      { rw h₃,
        exact h_4ins, }, 
      have h_avalue4 : ∃ (j ∈ range k), aFct l n j = 4 := by
      { sorry, }, 
      cases h_avalue4 with j hj,
      cases hj with h_j h_ais4,
      have h_a : aFct l n j = 2^l := by
      { have h_help : 2 * 2 = 4 := by
        { sorry, },
        rw h_1,
        rw h_1 at h_ais4,
        rw sq 2,
        rw h_help,
        exact h_ais4, }, 
      dsimp only [aFct] at h_a,
      dsimp only [mFct] at h_a,
      sorry, },
    -- STEP (4) : l ≥ 3 by Contradiciton
    { -- case l ≥ 3
      have h_3lel : 3 ≤ l := by
      { have h_2ll :=(ne.symm h_1).lt_of_le h_2lel, 
        exact succ_le_iff.mpr h_2ll, }, 
      -- main work : n < k³
      have h₄ : n < k^3 := by
      { have h_intro : ∃ (i1 i2 i3 : ℕ), aFct l n i1 = 1 ∧ aFct l n i2 = 2 ∧ aFct l n i3 = 4 := by
        { sorry, },
        cases h_intro with i1 h,
        cases h with i2 h,
        cases h with i3 h,
        cases h with h_a1 h,
        cases h with h_a2 h_a3,
        have h_ineqm : (mFct l n i2)^2 ≠ (mFct l n i1) * (mFct l n i2) := by
        { sorry, },
        -- cases for m₂² ≠ m₁ * m₃ 
        cases em ((mFct l n i2)^2 > (mFct l n i1) * (mFct l n i3)),
        { -- that is the case being covered in the book
          have h_ineq1 : k * n^(2 / 3) > n := by
          { have h_ineq2 : 2 * (k - 1) * n * (mFct l n i1) * (mFct l n i3) > 2 * n^2 := by
            { have h_ineq3 : 2 * (k - 1) * n > 4 * l * (mFct l n i1)^(l - 1) * (mFct l n i3)^(l - 1) := by
              { sorry, }, 
              sorry, }, 
            sorry, },
          sorry, },
        { -- that is the case not being covered in the book
          sorry, }, }, 
      -- using step 1 for k³ < n
      cases h₁ with p h,
      cases h with h_p h,
      cases h with h_plen h,
      cases h with h_kllpl h_k2kl, 
      have h_k3ln : k^3 < n := by
      { have h_k3lpl : k^3 < p^l := by
        { have h_k3lekl : k^3 ≤ k^l := by
          { have h_0lk : 0 < k := by
            { have h_0l4 : 0 < 4 := by 
              { exact four_pos, },
              exact gt_of_ge_of_gt h_4lek h_0l4, },
            exact pow_le_pow_of_le_right h_0lk h_3lel, }, 
          exact gt_of_gt_of_ge h_kllpl h_k3lekl, },
        exact gt_of_ge_of_gt h_plen h_k3lpl, }, 
      -- contradiciton 
      exact nat.lt_asymm h₄ h_k3ln, },
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
    have h_4lek_l : 4 ≤ k' := by linarith,
    exact h_wlog k' h_4lek_l h_klen4_l this, }
end
