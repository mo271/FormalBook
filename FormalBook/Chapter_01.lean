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

Authors: Moritz Firsching, Ralf Stephan
-/
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
theorem infinity_of_primes₁ (S : Finset ℕ) (h : ∀ q ∈ S, Nat.Prime q):
  ∃ (p : ℕ), Nat.Prime p ∧ p ∉ S := by
  let n := 1 + ∏ q in S, q
  /- "This `n` has a prime divisor":
  we pick the minimal one, the argument works with any prime divisor -/
  let p := n.minFac
  use p
  have hp : Nat.Prime p := Nat.minFac_prime <| Nat.ne_of_gt <| lt_add_of_pos_right 1
    (Finset.prod_pos fun q hq ↦ Prime.pos <| h q hq)
  refine ⟨hp, ?_⟩
  by_contra a
  have h_p_div_prod : p ∣ ∏ q in S, q := dvd_prod_of_mem (fun (i : ℕ) => i) a
  have h_p_div_diff : p ∣ n - ∏ q in S, q := dvd_sub' (minFac_dvd n) h_p_div_prod
  have h_p_div_one : p ∣ 1 := by aesop
  exact Nat.Prime.not_dvd_one hp h_p_div_one


/-!
### Second proof

using Fermat numbers
TODO: upstream this, see https://github.com/leanprover-community/mathlib4/pull/17000
-/
def F : ℕ → ℕ := fun n => 2^2^n + 1

lemma F₀: F 0 = 3 := by
  rw [F, Nat.pow_zero, pow_one]

lemma fermat_stricly_monotone {n : ℕ} : F n < F n.succ := by
  rw [F, F, add_lt_add_iff_right, Nat.pow_succ]
  exact (pow_lt_pow_iff_right one_lt_two).mpr (by norm_num)

lemma fermat_bounded (n : ℕ) : 2 < F n := by
  induction' n with n h
  · exact Nat.lt_add_one 2
  · exact lt_trans h fermat_stricly_monotone

lemma fermat_odd {n : ℕ} : Odd (F n) := by
  rw [F, ← not_even_iff_odd, even_add_one, not_not, even_pow]
  exact ⟨even_two, Nat.ne_of_gt (pow_pos zero_lt_two _)⟩

-- We actually prove something slighly stronger that what is in the book:
-- also for n = 0, the statement is true.
lemma fermat_product (n : ℕ) : ∏ k in range n, F k = F n - 2 := by
  induction' n with n hn
  · trivial
  · rw [prod_range_succ, hn]
    unfold F
    rw [mul_comm, (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by aesop),  ← Nat.sq_sub_sq]
    ring_nf
    omega

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
    exact (Nat.dvd_add_right h_m_prod).mp (h_prod ▸ h_n)
  cases' (dvd_prime prime_two).mp h_m with h_one h_two
  · exact h_one
  · by_contra
    rw [h_two] at h_n
    exact (not_even_iff_odd.mpr fermat_odd) (even_iff_two_dvd.mpr h_n)
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
  have h : (2 - 1 : ZMod q) = 0 := Iff.mpr sub_eq_zero h1
  norm_num at h

lemma sub_one_le_sub_one {n m : ℕ} : n ≤ m → n - 1 ≤ m - 1 :=
  fun h => pred_le_pred h


theorem infinity_of_primes₃:
  ¬ (∃ (p : ℕ), Nat.Prime p ∧ (∀ (q : ℕ), (Nat.Prime q) → q ≤ p)) := by
  simp only [not_exists, not_and, not_forall, not_le, exists_prop]
  intros p hp
  have : Fact (Nat.Prime p) := by exact { out := hp }
  let m := mersenne p
  -- This m has a prime factor;
  -- we pick the minimal one, the argument works with any prime factor
  let q := m.minFac
  have hq : q.Prime := minFac_prime <| Nat.ne_of_gt <| one_lt_mersenne.mpr <| Prime.one_lt hp
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
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_mod_q
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
    rw [Units.ext_iff, two_desc] at h
    exact (ZMod.two_ne_one q) h
  have h_piv_div_q_sub_one : p ∣ q - 1 := by
    -- The following shorter proof would work, but we want to use Lagrange's theorem
    -- convert ZMod.orderOf_units_dvd_card_sub_one two
    -- exact (orderOf_eq_prime h_two two_ne_one).symm

    -- Using Lagrange's theorem here!
    convert Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (two))
    · rw [← orderOf_eq_prime h_two two_ne_one, card_eq_fintype_card]
      exact Fintype.card_zpowers.symm
    · rw [card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact (totient_prime hq).symm
  refine ⟨q, minFac_prime <| Nat.ne_of_gt ?_, ?_⟩
  · calc 1 < 2^2 - 1 := one_lt_succ_succ 1
        _  ≤ 2^p - 1 := sub_one_le_sub_one <| pow_le_pow_of_le_right (succ_pos 1) (Prime.two_le hp)
  · have h2q : 2 ≤ q := Prime.two_le <| minFac_prime <| Nat.ne_of_gt <| lt_of_succ_lt <|
      Nat.sub_le_sub_right ((pow_le_pow_of_le_right (succ_pos 1) (Prime.two_le hp))) 1
    exact lt_of_le_of_lt (Nat.le_of_dvd  (Nat.sub_pos_of_lt <| h2q) h_piv_div_q_sub_one)
      <| pred_lt <| Nat.ne_of_gt <| Nat.le_of_lt h2q

/-!
### Fourth proof

using elementary calculus
-/
open Filter
open Nat.Prime

noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x ≤ 0) then 0 else primeCounting ⌊x⌋₊

def S₁ (x : ℝ) : Set ℕ :=
 { n | ∀ p, Nat.Prime p → p ∣ n → p ≤ x }

theorem infinity_of_primes₄ : Tendsto π atTop atTop := by
  -- two parts:
  -- (1) log x ≤ π x + 1
  -- (2) This implies that it is not bounded
  have H_log_le_primeCountingReal_add_one (n : ℕ) (x : ℝ) (hxge : x ≥ n) (hxlt : x < n + 1) :
      Real.log x ≤ primeCountingReal x + 1 :=
    calc
      Real.log x ≤ ∑ k in Icc 1 n, (k : ℝ)⁻¹ := by sorry
      _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by sorry
      _ ≤ (∏ p in primesBelow ⌊x⌋.natAbs, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by sorry
      _ ≤ (∏ k in Icc 1 (primeCountingReal x), (nth Nat.Prime k) / ((nth Nat.Prime k) - 1)) := by sorry
      _ ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1) / k) := by sorry
      _ ≤ primeCountingReal x + 1 := by sorry
  sorry

-- This might be useful for the proof. Rename as you like.
theorem monotone_primeCountingReal : Monotone primeCountingReal := by
  intro a b hab
  unfold primeCountingReal
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : b ≤ 0
    · linarith
    · simp only [ha, hb]
      exact monotone_primeCounting <| Nat.floor_mono hab

lemma H_P4_1 {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left, one_div_le_one_div h_p_pred_pos hk,
    @le_sub_iff_add_le]
  exact hp

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x in Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  rw [← Nat.Ico_succ_right]
  induction' n with n h
  · simp
  · rw [Finset.prod_Ico_succ_top <| Nat.le_add_left 1 n]
    norm_num
    cases' lt_or_ge n 2 with _ h2
    · interval_cases n
      · tauto
      · norm_num
    field_simp [Finset.prod_eq_zero_iff] at h ⊢
    rw [h h2]
    ring

lemma H_P4_2 (x : ℕ) (hx : x ≥ 3) :
    (∏ x in Icc 1 (π x), ((x + 1) : ℝ) / x) = (π x) + 1 := by
  rw [prod_Icc_succ_div]
  exact Monotone.imp monotone_primeCounting hx

/-!
### Fifth proof

using topology
-/

def N : ℤ → ℤ → Set ℤ := fun a b => {a + n * b | n : ℤ}

def isOpen : Set ℤ → Prop := fun O => O = ∅ ∨ ∀ a ∈ O, ∃ b > 0, N a b ⊆ O

theorem infinity_of_primes₅ : { p : ℕ | p.Prime }.Finite := by
  have TopoSpace : TopologicalSpace ℤ := by
    refine TopologicalSpace.mk isOpen ?_ ?_ ?_
    · exact Or.inr fun a _ ↦ ⟨1, Int.zero_lt_one, Set.subset_univ _⟩
    · sorry
    · intro S
      intro h
      right
      intros z hz
      obtain ⟨t, ⟨tS, zt⟩⟩ := hz
      have := (h t tS)
      rcases this with empty| ha'
      · aesop
      obtain ⟨b, hb⟩ := ha' z zt
      use b
      simp [hb]
      exact fun ⦃a⦄ a_1 ↦ Set.subset_sUnion_of_subset S t (fun ⦃a⦄ a ↦ a) tS (hb.2 a_1)
  have : ∀ X, ¬ TopoSpace.IsOpen X → X.Infinite := by sorry
  have : ∀ a b, TopoSpace.IsOpen (N a b)ᶜ := by sorry
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
  {p : Nat.Primes | ∃ n : ℕ, (p : ℤ) ∣ S n}.Finite := by
  sorry
