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
import number_theory.lucas_lehmer

open finset nat
open_locale big_operators
/-!
# Six proofs of the infinity of primes

## TODO
 - Seccond Proof : golf/formatting
 - Third Proof
 - Fourth Proof
 - Fifth Proof
 - Sixth Proof
 - Appendix: Infinitely many more proofs

### Euclid's Proof

-/
theorem infinity_of_primes₁ (S : finset ℕ) (h : ∀ (q ∈ S), nat.prime q):
  ∃ (p : ℕ), nat.prime p ∧ p ∉ S :=
begin
  let n := 1 + ∏ q in S, q,
  /- This n has a prime divisor;
  we pick the minimal one, the argument works with any prime divisor -/
  let p := n.min_fac,
  use p,
  have hp : nat.prime p := by
  { have hn : 0 < ∏ q in S, q := by
    { refine prod_pos _,
      intros q hq,
      exact prime.pos (h q hq), },
      exact nat.min_fac_prime (ne_of_gt(lt_add_of_pos_right 1 hn)), },
  split,
  { exact hp, },
  { by_contradiction,
    have h_p_div_prod : p ∣ ∏ q in S, q := dvd_prod_of_mem (λ (i : ℕ), i) h,
    have h_p_div_diff : p ∣ n - ∏ q in S, q := dvd_sub' (min_fac_dvd n) h_p_div_prod,
    have h_p_div_one : p ∣ 1 := by finish,
    exact nat.prime.not_dvd_one (hp) h_p_div_one, },
end

/-!
### Second proof

using Fermat numbers
-/
definition F : ℕ → ℕ := λ n, 2^2^n + 1

lemma F₀: F 0 = 3 :=
begin
  rw F,
  simp only [pow_zero, pow_one],
end

lemma fermat_stricly_monotone {n : ℕ} : F n < F n.succ :=
begin
  rw F,
  simp only [add_lt_add_iff_right],
  simp [pow_succ],
  refine (pow_lt_pow_iff one_lt_two).mpr _,
  norm_num,
end

lemma fermat_bounded (n : ℕ) : 2 < F n :=
begin
  induction n with n h,
  { rw F₀,
    norm_num, },
  { exact lt_trans h fermat_stricly_monotone, },
end

lemma fermat_odd {n : ℕ} : odd (F n) :=
begin
  rw F,
  simp,
  rw even_add_one,
  simp,
  rw even_pow,
  split,
  { exact even_two, },
  { exact ne_of_gt (pow_pos zero_lt_two _), },
end

-- We actually prove something slighly stronger that what is in the book:
-- also for n = 0, the statement is true.
lemma fermat_product (n : ℕ) : ∏ k in range n, F k = F n - 2 :=
begin
  induction n with n hn,
  trivial,
  rw prod_range_succ,
  rw hn,
  have h_bounded := le_of_lt (fermat_bounded n),
  have h : (F n)*(F n) + 2 = (F n.succ) + 2 * (F n) := by
  { rw F,
    norm_num,
    simp [add_mul, pow_succ, mul_add, mul_add],
    ring_nf,
    rw [←add_assoc, add_mul],
    norm_num,
    rw [add_comm],
    norm_num,
    rw [←pow_add, two_mul], },
  have h_bounded' := le_of_lt (fermat_bounded n.succ),
  linarith,
end


theorem infinity_of_primes₂  (k n : ℕ) (h : k < n): coprime (F n) (F k) :=
begin
  let m := (F n).gcd (F k),
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k),
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k),
  have h_m : m ∣ 2 :=  by
  { have h_m_prod : m ∣ (∏ k in range n, F k) :=
      dvd_trans h_k (dvd_prod_of_mem F (mem_range.mpr h)),
    have h_prod : (∏ k in range n, F k) + 2 = F n := by
    { rw fermat_product,
      have h_bound := lt_trans one_lt_two (fermat_bounded n),
      linarith, },
    refine (nat.dvd_add_right h_m_prod).mp _,
    rw h_prod,
    exact h_n, },
  have h_one_or_two := (dvd_prime prime_two).mp h_m,
  cases h_one_or_two with h_one h_two,
  { exact h_one, },
  { by_contradiction,
    rw h_two at h_n,
    have h_even : even (F n) := even_iff_two_dvd.mpr h_n,
    have h_odd : odd (F n) := fermat_odd,
    finish, },
end

/-!
### Third proof

using Mersenne numbers
-/
theorem infinity_of_primes₃:
  ¬ (∃ (p : ℕ), nat.prime p ∧ (∀ (q : ℕ), (nat.prime q) → q ≤ p)) :=
begin
  simp only [not_exists, not_and, not_forall, not_le, exists_prop],
  intros p h,
  let m := mersenne p,
  /- This m has a prime factor;
  we pick the minimal one, the argument works with any prime factor -/
  let q := m.min_fac,
  have h_mod_q : 2^p % q = 1 := by
  { have : (2^p - 1) % q = 0 :=  mod_eq_zero_of_dvd (min_fac_dvd m),
    sorry, },
  have h_piv_div_q_sub_one : p ∣ q - 1 := by
  { -- Use Lagrange's theorem here!
    sorry, },
  use q,
  split,
  { refine min_fac_prime _,
    have one_lt_mersenne : 1 < mersenne p := by
    { dsimp [mersenne],
      calc 1 < 2^2 - 1 : by norm_num
         ... ≤ 2^p - 1 : pred_le_pred (pow_le_pow_of_le_right (nat.succ_pos 1) (prime.two_le h)), },
    exact ne.symm (ne_of_lt one_lt_mersenne), },
  { sorry, },
end


/-!
### Fourth proof

using elementary calculus
-/

/-!
### Fifth proof

using topology
-/

/-!
### Sixth proof

using the sum of inverses of primes
-/

/-!
### Appendix: Infinitely many more proofs
-/
