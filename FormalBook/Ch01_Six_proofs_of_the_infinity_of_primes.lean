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
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Parity
--import Mathlib.NumberTheory.LucasLehmer

open Finset Nat
open BigOperators
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
theorem infinity_of_primes₁ (S : Finset ℕ) (h : ∀ {q : ℕ} (_ : q ∈ S), Nat.Prime q):
  ∃ (p : ℕ), Nat.Prime p ∧ p ∉ S := by
  let n := 1 + ∏ q in S, q
  /- This `n` has a prime divisor;
  we pick the minimal one, the argument works with any prime divisor -/
  let p := n.minFac
  use p
  have hp : Nat.Prime p := by
    have hn : 0 < ∏ q in S, q := by
      refine' Finset.prod_pos _
      intros q hq
      refine' Prime.pos <| h hq
    exact Nat.minFac_prime <| Nat.ne_of_gt <| lt_add_of_pos_right 1 hn
  refine' ⟨hp,_⟩
  by_contra a
  have h_p_div_prod : p ∣ ∏ q in S, q := dvd_prod_of_mem (fun (i : ℕ) => i) a
  have h_p_div_diff : p ∣ n - ∏ q in S, q := dvd_sub' (minFac_dvd n) h_p_div_prod
  have h_p_div_one : p ∣ 1 := by aesop
  exact Nat.Prime.not_dvd_one (hp) h_p_div_one


/-!
### Second proof

using Fermat numbers
-/
def F : ℕ → ℕ := fun n => 2^2^n + 1

lemma F₀: F 0 = 3 := by
  rw [F]
  simp only [Nat.pow_zero, pow_one]

lemma fermat_stricly_monotone {n : ℕ} : F n < F n.succ := by
  have : NeZero 1 := by infer_instance
  rw [F, F]
  simp only [add_lt_add_iff_right, Nat.pow_succ]
  refine' (pow_lt_pow_iff one_lt_two).mpr _
  norm_num

lemma fermat_bounded (n : ℕ) : 2 < F n := by
  induction' n with n h
  · rw [F₀]
    norm_num
  · exact lt_trans h fermat_stricly_monotone

lemma fermat_odd {n : ℕ} : Odd (F n) := by
  rw [F, odd_iff_not_even, even_add_one, not_not, even_pow]
  refine' ⟨even_two, Nat.ne_of_gt (pow_pos _ _)⟩
  exact zero_lt_two

-- We actually prove something slighly stronger that what is in the book:
-- also for n = 0, the statement is true.
lemma fermat_product (n : ℕ) : ∏ k in range n, F k = F n - 2 := by
  induction' n with n hn
  · trivial
  rw [prod_range_succ, hn]
  unfold F
  norm_num
  rw [succ_eq_add_one, mul_comm, ← Nat.sq_sub_sq]
  ring_nf

theorem infinity_of_primes₂  (k n : ℕ) (h : k < n): coprime (F n) (F k) := by
  let m := (F n).gcd (F k)
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k)
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k)
  have h_m : m ∣ 2 :=  by
    have h_m_prod : m ∣ (∏ k in range n, F k) :=
      dvd_trans h_k (dvd_prod_of_mem F (mem_range.mpr h))
    have h_prod : (∏ k in range n, F k) + 2 = F n := by
      rw [fermat_product]
      rw [Nat.sub_add_cancel]
      refine' le_of_lt _
      simp [fermat_bounded]
    refine' (Nat.dvd_add_right h_m_prod).mp _
    rw [h_prod]
    exact h_n
  have h_one_or_two := (dvd_prime prime_two).mp h_m
  cases' h_one_or_two with h_one h_two
  · exact h_one
  · by_contra
    rw [h_two] at h_n
    have h_even : Even (F n) := even_iff_two_dvd.mpr h_n
    have h_odd : Odd (F n) := fermat_odd
    aesop
/-!
### Third proof

using Mersenne numbers
-/
theorem infinity_of_primes₃:
  ¬ (∃ (p : ℕ), Nat.Prime p ∧ (∀ (q : ℕ), (Nat.Prime q) → q ≤ p)) := by
  simp only [not_exists, not_and, not_forall, not_le, exists_prop]
  intros p h
  -- Currently port still missing LucasLehmer:
  -- https://github.com/leanprover-community/mathlib4/pull/2988
  sorry
  /- let m := Mersenne p
  /- This m has a prime factor;
  we pick the minimal one, the argument works with any prime factor -/
  let q := m.minFac
  have h_mod_q : 2^p % q = 1 := by
    have : (2^p - 1) % q = 0 :=  mod_eq_zero_of_dvd (min_fac_dvd m)
    sorry
  have h_piv_div_q_sub_one : p ∣ q - 1 := by
  -- Use Lagrange's theorem here!
    sorry
  use q
  split
  · refine min_fac_prime _
    have one_lt_mersenne : 1 < mersenne p := by
      dsimp [mersenne]
      calc 1 < 2^2 - 1 : by norm_num
         ... ≤ 2^p - 1 : pred_le_pred (pow_le_pow_of_le_right (nat.succ_pos 1) (prime.two_le h))
    exact ne.symm (ne_of_lt one_lt_mersenne)
    sorry
  -/


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
