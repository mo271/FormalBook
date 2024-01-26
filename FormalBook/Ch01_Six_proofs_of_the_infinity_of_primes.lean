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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Pow
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Basic

open Finset Nat
open BigOperators
/-!
# Six proofs of the infinity of primes

## TODO
 - Seccond Proof : golf/formatting
 - Third Proof : golf/formatting/comments
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
  refine' ⟨hp, _⟩
  by_contra a
  have h_p_div_prod : p ∣ ∏ q in S, q := dvd_prod_of_mem (fun (i : ℕ) => i) a
  have h_p_div_diff : p ∣ n - ∏ q in S, q := dvd_sub' (minFac_dvd n) h_p_div_prod
  have h_p_div_one : p ∣ 1 := by aesop
  exact Nat.Prime.not_dvd_one hp h_p_div_one


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
  refine' (pow_lt_pow_iff_right one_lt_two).mpr _
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

theorem infinity_of_primes₂  (k n : ℕ) (h : k < n): Coprime (F n) (F k) := by
  let m := (F n).gcd (F k)
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k)
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k)
  have h_m : m ∣ 2 :=  by
    have h_m_prod : m ∣ (∏ k in range n, F k) :=
      dvd_trans h_k (dvd_prod_of_mem F (mem_range.mpr h))
    have h_prod : (∏ k in range n, F k) + 2 = F n := by
      rw [fermat_product, Nat.sub_add_cancel]
      refine' le_of_lt _
      simp [fermat_bounded]
    refine' (Nat.dvd_add_right h_m_prod).mp _
    rw [h_prod]
    exact h_n
  cases' (dvd_prime prime_two).mp h_m with h_one h_two
  · exact h_one
  · by_contra
    rw [h_two] at h_n
    have h_even : Even (F n) := even_iff_two_dvd.mpr h_n
    have h_odd : Odd (F n) := fermat_odd
    exact (odd_iff_not_even.mp h_odd) h_even
/-!
### Third proof

using Mersenne numbers
-/
lemma ZMod.one_ne_zero (q : ℕ) [Fact (1 < q)] : (1 : ZMod q) ≠ 0 := by
  intro h
  have := ZMod.val_one q ▸ (ZMod.val_eq_zero (1 : ZMod q)).mpr h
  linarith

lemma ZMod.two_ne_one (q : ℕ)  [Fact (1 < q)] : (2 : ZMod q) ≠ 1 := by
  intro h1
  have h : (2 - 1 : ZMod q) = 0 := by exact Iff.mpr sub_eq_zero h1
  norm_num at h
  have := ZMod.one_ne_zero q
  exact this h


theorem infinity_of_primes₃:
  ¬ (∃ (p : ℕ), Nat.Prime p ∧ (∀ (q : ℕ), (Nat.Prime q) → q ≤ p)) := by
  simp only [not_exists, not_and, not_forall, not_le, exists_prop]
  intros p hp
  have : Fact (Nat.Prime p) := by exact { out := hp }
  let m := mersenne p
  -- This m has a prime factor;
  -- we pick the minimal one, the argument works with any prime factor
  let q := m.minFac
  have hq : q.Prime := minFac_prime <| Nat.ne_of_gt <| one_lt_mersenne <| Prime.one_lt hp
  have : Fact (Nat.Prime q) := by exact { out := hq }
  have h_mod_q : 2 ^ p  ≡ 1 [MOD q] := by
    have : (2^p - 1) % q = 0 :=  mod_eq_zero_of_dvd (minFac_dvd m)
    change (2^p - 1) ≡ 0 [MOD q] at this
    rw [modEq_iff_dvd, dvd_iff_exists_eq_mul_left] at *
    obtain ⟨c, hc⟩ := this
    use c
    simp only [CharP.cast_eq_zero, ge_iff_le, gt_iff_lt, pow_pos, cast_pred, cast_pow, cast_ofNat,
        zero_sub, neg_sub] at hc
    simp [cast_one, cast_pow, cast_ofNat, hc.symm]
  have h_mod_q' : (2 : (ZMod q)) ^ p = 1 := by
    have := (ZMod.nat_cast_eq_nat_cast_iff _ _ _).mpr h_mod_q
    norm_cast at this
    rw [← this, cast_pow, cast_ofNat]
  have : (2 : (ZMod q)) * (2 ^ (p - 1)) = 1 := by
    convert h_mod_q'
    nth_rw 1 [← pow_one 2]
    rw [← pow_add 2 1 (p - 1)]
    congr
    exact add_sub_of_le <| Prime.pos hp
  let two := Units.mkOfMulEqOne (2 : (ZMod q)) (2 ^ (p - 1)) this
  have two_desc : ↑two = (2 : (ZMod q)) := by
    convert Units.val_mkOfMulEqOne this
  have h_two : two ^ p = 1 := by
    ext
    push_cast
    rw [two_desc]
    exact h_mod_q'
  have two_ne_one : two ≠ 1 := by
    by_contra h
    rw [Units.ext_iff] at h
    push_cast at h
    rw [two_desc] at h
    exact (ZMod.two_ne_one q) h
  have h_piv_div_q_sub_one : p ∣ q - 1 := by
    -- The following shorter proof would work, but we want to use Lagrange's theorem
    -- convert ZMod.orderOf_units_dvd_card_sub_one two
    -- exact (orderOf_eq_prime h_two two_ne_one).symm

    -- Using Lagrange's theorem here!
    convert Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (two))
    · rw [← orderOf_eq_prime h_two two_ne_one]
      exact Fintype.card_zpowers.symm
    · exact ((prime_iff_card_units q).mp hq).symm
  use q
  constructor
  · refine' minFac_prime <| Nat.ne_of_gt _
    dsimp [mersenne]
    calc 1 < 2^2 - 1 := by norm_num
        _  ≤ 2^p - 1 := (pred_eq_sub_one 4).symm ▸ pred_le_pred <|
            pow_le_pow_of_le_right (succ_pos 1) (Prime.two_le hp)
  · have h2q : 2 ≤ q := by
      exact Prime.two_le <| minFac_prime <| Nat.ne_of_gt <| lt_of_succ_lt <|
          Nat.sub_le_sub_right ((pow_le_pow_of_le_right (succ_pos 1) (Prime.two_le hp))) 1
    exact lt_of_le_of_lt (Nat.le_of_dvd  (Nat.sub_pos_of_lt <| h2q) h_piv_div_q_sub_one)
        <| pred_lt <| Nat.ne_of_gt <| Nat.le_of_lt h2q
/-!
### Fourth proof

using elementary calculus
-/
open Filter

theorem infinity_of_primes₄ : Tendsto π atTop atTop := by
  -- two parts:
  -- (1) log x ≤ π x + 1
  -- (2) This implies that it is not bounded
  sorry

/-!
### Fifth proof

using topology
-/


def N : ℕ → ℕ → Set ℤ := fun a b => {a + n * b | n : ℤ}

theorem infinity_of_primes₅ : Fintype { p : ℕ // p.Prime } → False   := by
  sorry

/-!
### Sixth proof

using the sum of inverses of primes
-/
-- see Archive.Wiedijk100Theorems.SumOfPrimeReciprocalsDiverges
theorem infinity_of_primes₆ :
  Tendsto (fun n => ∑ p in Finset.filter (fun p => Nat.Prime p) (range n), 1 / (p : ℝ))
      atTop atTop := by
  sorry

/-!
### Appendix: Infinitely many more proofs
-/

def AlmostInjective (S : ℕ → ℤ) : Prop :=
  ∃ c : ℕ, ∀ k : ℕ, ∃ h : Set.Finite {n : ℕ | S n = k }, (Set.Finite.toFinset h).card ≤ c

variable (fn : NNReal)

open Real NNReal Topology

namespace Asymptotics

def ofSubexponentialGrowth (S : ℕ → ℤ) : Prop := ∃ f : ℕ → ℝ≥0, ∀ n,
  |S n| ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (f n : ℝ)) ∧ Tendsto (fun n => (f n) / (log 2 n)) atTop (𝓝 0)

theorem infinitely_many_more_proofs (S : ℕ → ℤ)
  (h₁ : AlmostInjective S) (h₂ : ofSubexponentialGrowth S) :
  Fintype {p : Nat.Primes // ∃ n : ℕ, (p : ℤ) ∣ S n} → False := by
  sorry
