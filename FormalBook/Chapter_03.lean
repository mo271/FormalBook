/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Christopher Schmidt
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Qify
--set_option trace.simp_lemmas true


open Nat
open Finset
open BigOperators


/-!
# Binomial coefficients are (almost) never powers
## TODO
  - Lemmata
    - .. for Step 1: needs golfing
  - (1)
  - (2)
  - (3)
  - (4)
  There is a somewhat more detailed, but quite messy version of the lean3 version here:
  https://github.com/mo271/FormalBook/blob/92f57b44cbbc1cd02ca77994efe8d8e6de050a19/src/chapters/03_Binomial_coefficients_are_(almost)_never_powers.lean
  Let's not follow that, but keep the proof cleaner.
### Sylvester's Theorem
There is no proof given in the book, perhaps check out Erdős' for a proof to formalize.
-/
namespace chapter3

theorem sylvester (k n : ℕ) (h : n ≥ 2*k) (h_k : k > 0): ∃ p, p > k ∧ p.Prime ∧ p ∣ choose n k :=
  sorry

/-!
### Lemmata for Step 1 and Step 2
-/
example (a p : ℕ) (h : p ∣ a) (g : a < p): a = 0 := eq_zero_of_dvd_of_lt h g

theorem prime_div_descFactorial (n k m l p : ℕ) (h_klen : k ≤ n)
  (h_p : p.Prime) (h_p_div_binom : p ∣ choose n k) (H : choose n k = m^l) :
  p^l ∣ n.descFactorial k := by

  have h_p_div_ml : p ∣ m^l := by
    rw [← H]
    exact h_p_div_binom
  have h_pl_div_ml : p^l ∣ m^l := by
    exact pow_dvd_pow_of_dvd (Nat.Prime.dvd_of_dvd_pow (h_p) (h_p_div_ml)) l
  have h_pl_div_binom : p^l ∣ choose n k := by
    rw [H]
    exact h_pl_div_ml
  have h_pl_div_fac : p^l ∣  (n.factorial / (k.factorial * (n-k).factorial)) := by
    rw [← Nat.choose_eq_factorial_div_factorial h_klen]
    exact h_pl_div_binom

  -- here we start using qify to handle division
  have h_fac_div : ((↑k ! * ↑(n - k)!) : ℤ)  ∣ (n ! : ℤ) :=
    mod_cast factorial_mul_factorial_dvd_factorial h_klen
  have h_fac_div' : ↑(n - k)! ∣ (n ! : ℤ) := dvd_of_mul_left_dvd h_fac_div
  have h_fac_div'' : (k ! : ℤ) ∣ (↑n ! / ↑(n - k)!) := by
    refine' mod_cast (dvd_div_iff_mul_dvd ((Int.natCast_dvd_natCast).mp h_fac_div')).mpr _
    rw [mul_comm]
    exact mod_cast h_fac_div
  have h_kfac_ne_zero : (k ! : ℚ) ≠ 0 := cast_ne_zero.mpr (factorial_ne_zero k)
  have h_nkfac_ne_zero : ((n - k)! : ℚ) ≠ 0 := cast_ne_zero.mpr (n - k).factorial_ne_zero
  have : (k ! * (n - k)! : ℚ) ≠ 0 := mul_ne_zero h_kfac_ne_zero h_nkfac_ne_zero
  have h_fraction: (n.factorial / (k.factorial * (n - k).factorial)) =
    (n.factorial / (n - k).factorial) / k.factorial := by
    qify
    simp
    rw [mul_comm]
    norm_cast
    exact (Nat.div_div_eq_div_mul n ! (n - k)! k !).symm
  rw [h_fraction] at h_pl_div_fac
  have h_pl_div_fac_part: p^l ∣ (n.factorial / (n - k).factorial) := by
    have h_eq_pl_with_k := exists_eq_mul_right_of_dvd h_pl_div_fac
    have h_eq_pl : ∃ (r : ℕ), r * p^l = n.factorial / (n - k).factorial := by
      cases' h_eq_pl_with_k with j h_eq
      use (j * k.factorial)
      rw [(mul_rotate _ _ _).symm, ← h_eq]
      qify
      aesop
    cases' h_eq_pl with j h_eq
    refine' Dvd.intro j _
    rw [mul_comm]
    exact h_eq
  rw [descFactorial_eq_div h_klen]
  convert h_pl_div_fac_part

/- now in mathlib? -/
lemma factor_in_descFactorial (n k p l : ℕ) (h_klen : k ≤ n) (h_klp : k < p) (hp: p.Prime)
(h_pow_div: p^l ∣ n.descFactorial k) (h_1lel : 1 ≤ l):
∃ (i : ℕ), (i ≤ k - 1) ∧ p^l ∣ (n - i) := by sorry

/-
### Erdős' Theorem
Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/
theorem binomials_coefficients_never_powers (k l m n : ℕ) (h_2lel : 2 ≤ l) (h_4lek : 4 ≤ k)
(h_klen4 : k ≤ n - 4) : choose n k ≠ m^l := by
  -- Assumption that n ≥ 2k
  have h_wlog :
      ∀ (k' : ℕ) (h_4lek' : 4 ≤ k') (h_klen4' : k' ≤ n - 4), 2*k' ≤ n → choose n k' ≠ m^l := by
    clear h_4lek h_klen4 k
    intros k h_4lek h_klen4 h
    -- inequalities needed
    have h_klen : k ≤ n := le_trans h_klen4 (Nat.sub_le n 4)
    have h_1lel : 1 ≤ l := le_of_succ_le (h_2lel)
    by_contra H
    -- main proof here proceeding in four steps
    -- Step (1)
    have h₁: ∃ p, p.Prime ∧ p^l ≤ n ∧ k^l < p^l ∧ k^2 ≤ k^l := by
      obtain ⟨p, ⟨h_klp, ⟨h_p, h_p_div_binom⟩⟩⟩ := sylvester k n h (lt_of_lt_of_le (Nat.zero_lt_succ 3) h_4lek)
      use p
      refine' ⟨h_p,  ⟨_, _⟩⟩
      -- prove p^l ≤ n
      · have h_pl_div_desc: p^l ∣ n.descFactorial k :=
            prime_div_descFactorial n k m l p  h_klen h_p h_p_div_binom H
        have h_klp_pow_dvd := factor_in_descFactorial n k p l h_klen (gt_iff_lt.mp h_klp) (h_p)
            h_pl_div_desc h_1lel
        -- working with them
        cases' h_klp_pow_dvd with i hi
        cases' hi with hi_left hi_right
        have : p^l ≤ n - i := by
          refine' Nat.le_of_dvd _ hi_right
          simp only [tsub_pos_iff_lt]
          have h_ilk : i < k := Iff.mpr (lt_iff_le_pred (lt_of_lt_of_le four_pos h_4lek)) hi_left
          exact lt_of_lt_of_le h_ilk h_klen
        have h_klen4i : n - i ≤ n := Nat.sub_le n i
        exact le_trans this h_klen4i
      · exact ⟨
            -- prove k^l < p^l
            Nat.pow_lt_pow_left (h_klp) (Nat.ne_of_gt <| gt_of_ge_of_gt h_2lel two_pos),
            Nat.pow_le_pow_of_le_right (pos_of_gt h_4lek) h_2lel -- prove k² ≤ k^l
            ⟩

    -- Step (2) : aⱼ only have prime divisors ≤ k ; aᵢ ≠ aⱼ
    --have h₂ : ∀ j, (j ≤ k - 1) ∧ (∀ (q : ℕ), q ∣ (aFct l n j) ∧ prime q → q ≤ k) ∧
    --    (∀ i ≤ k - 1, i ≠ j → (aFct l n i) ≠ (aFct l n j)) := by
    -- sorry
    -- Step (3) : a_i are integers 1..k
    --have h₃ : a_values l n k = s_1tok k := by
    -- divide in two cases
    cases em (l = 2)
    -- Special Case l = 2 by Contradiction
    ·  sorry
    -- STEP (4) : l ≥ 3 by Contradiction
    -- case l ≥ 3
    · have h_3lel : 3 ≤ l := by
        sorry
      -- main work : n < k³
      have h₄ : n < k^3 := by
        sorry

      sorry

  cases' em (n ≥ 2*k) with h_2k h
  · exact h_wlog k h_4lek h_klen4 h_2k
  · -- transform ¬(n ≥ 2 * k) into (n < 2 * k)
    simp only [not_le] at h
    -- transform (n.choose k) into (n.choose (n - k))
    have h_klen : k ≤ n := le_trans h_klen4 (Nat.sub_le n 4)
    rw [← choose_symm h_klen]
    -- define k' as n - k, such that k' can be used for h_wlog as k'
    -- satisfies all required features
    let k' := n - k
    have h_k'_def : k' = n - k := by rfl
    -- third requirement: 2 * k' ≤ n
    have h_2k'len : 2 * k' ≤ n := by
      sorry
    -- second requirement: k ≤ n - 4
    have h_k'len4 : k' ≤ n - 4 := by
      simp only [h_k'_def, tsub_le_iff_right]
      have help : k + k ≤ n - 4 + k := add_le_add_right h_klen4 k
      rw [← (two_mul k)] at help
      exact le_trans (le_of_lt h) help
    -- first requirement: 4 ≤ k
    have h_4lek' : 4 ≤ k' := Iff.mp (le_tsub_iff_le_tsub h_klen (le_trans (le_trans h_4lek h_klen4)
      (Nat.sub_le n 4))) h_klen4
    -- now we can use h_wlog
    exact h_wlog k' h_4lek' h_k'len4 h_2k'len


end chapter3
