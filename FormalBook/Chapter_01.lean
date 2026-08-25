/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ralf Stephan
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Nat
open BigOperators
/-!
# Six proofs of the infinity of primes

## TODO
 - Second Proof : golf/formatting
 - Third Proof : golf/formatting/comments
 - Fourth Proof
 - Fifth Proof
 - Sixth Proof
 - Appendix: Infinitely many more proofs


### Euclid's Proof

-/
theorem infinity_of_primes₁ (S : Finset ℕ) (h : ∀ q ∈ S, Nat.Prime q):
  ∃ (p : ℕ), Nat.Prime p ∧ p ∉ S := by
  let n := 1 + ∏ q ∈ S, q
  /- "This `n` has a prime divisor":
  we pick the minimal one, the argument works with any prime divisor -/
  let p := n.minFac
  use p
  have hp : Nat.Prime p := Nat.minFac_prime <| Nat.ne_of_gt <| lt_add_of_pos_right 1
    (Finset.prod_pos fun q hq ↦ Prime.pos <| h q hq)
  refine ⟨hp, ?_⟩
  by_contra a
  have h_p_div_prod : p ∣ ∏ q ∈  S, q := dvd_prod_of_mem (fun (i : ℕ) ↦ i) a
  have h_p_div_diff : p ∣ n - ∏ q ∈ S, q := dvd_sub (minFac_dvd n) h_p_div_prod
  have h_p_div_one : p ∣ 1 := by aesop
  exact Nat.Prime.not_dvd_one hp h_p_div_one


/-!
### Second proof

-/

local notation "F" => fermatNumber

-- We actually prove something slighly stronger that what is in the book:
-- also for n = 0, the statement is true.
-- This is in mathlib as `fermatNumber_product`
lemma fermatProduct (n : ℕ) : ∏ k ∈ range n, F k = F n - 2 := by
  induction n with
  | zero => trivial
  | succ n hn =>
    rw [prod_range_succ, hn]
    unfold fermatNumber
    rw [mul_comm, (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by aesop),  ← Nat.sq_sub_sq]
    ring_nf
    omega

-- This is in mathlib as coprime_fermatNumber_fermatNumber
theorem infinity_of_primes₂  (k n : ℕ) (h : k < n) : Coprime (F n) (F k) := by
  let m := (F n).gcd (F k)
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k)
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k)
  have h_m : m ∣ 2 :=  by
    have h_m_prod : m ∣ (∏ k ∈ range n, F k) :=
      dvd_trans h_k (dvd_prod_of_mem F (mem_range.mpr h))
    have h_prod : (∏ k ∈ range n, F k) + 2 = F n := by
      rw [fermatProduct, Nat.sub_add_cancel]
      refine' le_of_lt _
      simp [two_lt_fermatNumber]
    exact (Nat.dvd_add_right h_m_prod).mp (h_prod ▸ h_n)
  rcases (dvd_prime prime_two).mp h_m with h_one | h_two
  · exact h_one
  · by_contra
    rw [h_two] at h_n
    exact (not_even_iff_odd.mpr <| odd_fermatNumber n) (even_iff_two_dvd.mpr h_n)

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
  fun h ↦ pred_le_pred h


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
    simp only [CharP.cast_eq_zero, zero_sub] at hc
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
        _  ≤ 2^p - 1 := sub_one_le_sub_one <| Nat.pow_le_pow_right (succ_pos 1) (Prime.two_le hp)
  · have h2q : 2 ≤ q := Prime.two_le <| minFac_prime <| Nat.ne_of_gt <| lt_of_succ_lt <|
      Nat.sub_le_sub_right ((Nat.pow_le_pow_right (succ_pos 1) (Prime.two_le hp))) 1
    exact lt_of_le_of_lt (Nat.le_of_dvd  (Nat.sub_pos_of_lt <| h2q) h_piv_div_q_sub_one)
      <| pred_lt <| Nat.ne_of_gt <| Nat.le_of_lt h2q

/-!
### Fourth proof

using elementary calculus
-/
open Filter
open Nat.Prime

open Classical

/-- The prime counting function `π(x)` for real `x`. -/
noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x ≤ 0) then 0 else primeCounting ⌊x⌋₊

/-- The set of natural numbers whose prime factors are all less than or equal to `x`. -/
def S₁ (x : ℝ) : Set ℕ :=
 { n | ∀ p, Nat.Prime p → p ∣ n → p ≤ x }
/-- The inferse function is a homomorphism. -/
noncomputable def invRealHom : ℕ →*₀ ℝ :=
  { toFun := fun n => (n : ℝ)⁻¹
    map_one' := by
      -- The inverse of 1 is 1.
      norm_num
    map_zero' := by
      -- By definition of division, we know that $0 / 0 = 0$.
      norm_num
    map_mul' := by
      grind }

lemma S1_eq_smoothNumbers (x : ℝ) : S₁ x = Nat.smoothNumbers (⌊x⌋₊ + 1) := by
  ext n
  simp only [S₁, Nat.smoothNumbers, Set.mem_setOf_eq]
  constructor
  · intro hn
    have hn0 : n ≠ 0 := by
      intro hn0
      obtain ⟨p, hp_le, hp_prime⟩ := Nat.exists_infinite_primes (⌊x⌋₊ + 1)
      have hle := hn p hp_prime (hn0 ▸ dvd_zero p)
      have : (p : ℝ) ≤ x := hle
      have : p ≤ ⌊x⌋₊ := Nat.le_floor this
      omega
    refine ⟨hn0, ?_⟩
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
    have hle : (p : ℝ) ≤ x := hn p hp_prime hp_dvd
    have : p ≤ ⌊x⌋₊ := Nat.le_floor hle
    omega
  · rintro ⟨hn0, hn⟩ p hp_prime hp_dvd
    have hp_mem : p ∈ n.primeFactorsList :=
      (Nat.mem_primeFactorsList hn0).2 ⟨hp_prime, hp_dvd⟩
    have hlt : p < ⌊x⌋₊ + 1 := hn p hp_mem
    have hp_le : p ≤ ⌊x⌋₊ := by omega
    have hx0 : 0 ≤ x := by
      by_contra hneg
      have : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
      have hp_pos := Nat.Prime.pos hp_prime
      omega
    exact le_trans (Nat.cast_le.mpr hp_le) (Nat.floor_le hx0)

lemma norm_invRealHom_prime_lt_one (p : ℕ) (hp : Nat.Prime p) : ‖invRealHom p‖ < 1 := by
  erw [Real.norm_of_nonneg]
  · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.one_lt
  · exact inv_nonneg.2 <| Nat.cast_nonneg _

/-- The inverse function is a monoid homomorphism. -/
noncomputable def invRealMonoidHom : ℕ →* ℝ :=
  { toFun := fun n => (n : ℝ)⁻¹
    map_one' := by simp
    map_mul' := by
      intros x y
      simp [mul_comm] }

lemma summable_invRealHom_smoothNumbers (N : ℕ) : Summable (fun (m : Nat.smoothNumbers N) ↦ ‖invRealHom m‖) := by
  have h : ∀ {p : ℕ}, Nat.Prime p → ‖invRealMonoidHom p‖ < 1 := by
    intro p hp
    have : invRealMonoidHom p = (p : ℝ)⁻¹ := rfl
    rw [this, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)
  have := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric (f := invRealMonoidHom) h N).1
  exact this

theorem f_abs_summable (x : ℝ) (n : ℕ) (hxge : x ≥ ↑n) (hxlt : x < ↑n + 1)
  (f : ArithmeticFunction ℝ) (hf : f.toFun = (S₁ x).indicator fun y ↦ (↑y)⁻¹) :
  Summable fun x ↦ ‖f x‖ := by
  have h_floor : ⌊x⌋₊ = n := by
    have h1 : (n : ℝ) ≤ x := hxge
    have h2 : x < (n : ℝ) + 1 := hxlt
    exact Nat.floor_eq_on_Ico n x ⟨h1, h2⟩
  have hS : S₁ x = Nat.smoothNumbers (n + 1) := by
    rw [S1_eq_smoothNumbers, h_floor]
  have h_summable : Summable (fun m : Nat.smoothNumbers (n + 1) ↦ ‖(m : ℝ)⁻¹‖) :=
    summable_invRealHom_smoothNumbers (n + 1)
  have h_ind : Summable ((Nat.smoothNumbers (n + 1)).indicator (fun m : ℕ ↦ ‖(m : ℝ)⁻¹‖)) :=
    summable_subtype_iff_indicator.mp h_summable
  have h_eq : (fun x ↦ ‖f x‖) = (Nat.smoothNumbers (n + 1)).indicator (fun m : ℕ ↦ ‖(m : ℝ)⁻¹‖) := by
    rw [← hS]
    ext m
    have : f m = f.toFun m := rfl
    rw [this, hf, Set.indicator_apply, Set.indicator_apply]
    split_ifs with hm
    · rfl
    · simp
  rw [h_eq]
  exact h_ind

lemma exists_image_primes_eq_primesBelow (n : ℕ) :
  ∃ (s : Finset Nat.Primes), s.image (fun p : Nat.Primes ↦ p.1) = n.primesBelow := by
  unfold Nat.Primes
  refine ⟨Finset.subtype Nat.Prime n.primesBelow, ?_⟩
  ext a
  simp only [Finset.mem_image, Finset.mem_subtype, Nat.mem_primesBelow]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro ha
    exact ⟨⟨a, ha.2⟩, ha, rfl⟩

lemma arithmetic_f (x: ℝ) (n: ℕ) (hxlt : x < n + 1) : ∃ f: ArithmeticFunction ℝ, f.toFun = (S₁ x).indicator (fun y ↦ (↑y)⁻¹) := by {
    exists ZeroHom.mk ((S₁ x).indicator (fun y: ℕ ↦ (y: ℝ)⁻¹)) (by
  {
    have: ¬ (0 ∈ S₁ x) := by {
      unfold S₁
      intro h
      have: ∃ p, Nat.Prime p ∧ p > x := by {
        have := @Nat.exists_prime_gt_modEq_one 1 (n+1) (by bound)
        obtain ⟨p, hp⟩ := this
        obtain ⟨pprime, ⟨pgt, _⟩⟩ := hp
        have: (p: ℝ) > (n: ℝ)+1 := by {
          rify at pgt
          assumption
        }
        have: ↑p > x := by bound
        exists p
      }
      obtain ⟨p, ⟨pprime, pgt⟩⟩ := this
      have hle := h p pprime (dvd_zero p)
      linarith
    }
    apply Set.indicator_of_notMem
    assumption
  })
  }

theorem euler_product_rearrangement (x: ℝ) (n: ℕ) (hxge : x ≥ n) (hxlt : x < n + 1): ∑' m : (S₁ x), (m : ℝ)⁻¹ = (∏ p ∈ primesBelow (⌊x⌋.natAbs+1), (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by {
  have:= _root_.tsum_subtype (S₁ x) (fun y => (y:ℝ)⁻¹)
  rewrite [this]
  clear this
  have hf:= arithmetic_f x n hxlt
  obtain ⟨f, hf⟩ := hf
  have f_one_eq_one: f.toFun 1 = 1 := by {
        rewrite [hf]; clear hf
        have: 1 ∈ S₁ x := fun p Hp contra => (Nat.Prime.not_dvd_one Hp contra).elim
        simp [this]
      }
  have f_mul: f.IsMultiplicative := by {
    unfold ArithmeticFunction.IsMultiplicative
    constructor
    .
      bound
    . clear hxge hxlt n
      intro m n hmn
      -- By definition of $f$, we know that $f(mn) = 1/(mn)$ if $mn \in S₁(x)$ and $0$ otherwise.
      have h_f_mn : f (m * n) = if m * n ∈ S₁ x then (1 / (m * n : ℝ)) else 0 := by
        aesop;
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all +decide [ S₁ ];
      split_ifs <;> simp_all +decide [ Nat.Prime.dvd_mul ];
      · bound
      · grind +ring
  }
  have f_sum: Summable (fun x: ℕ => ‖f x‖) := by exact f_abs_summable x n hxge hxlt f hf
  have euler_rewrite:= ArithmeticFunction.IsMultiplicative.eulerProduct_tprod f_mul f_sum
  clear f_mul f_sum
  have: ∑' (n : ℕ), f n = ∑' (n : ℕ), (S₁ x).indicator (fun y ↦ (↑y)⁻¹) n := by exact congrFun (congrArg (@tsum ℝ ℕ Real.instAddCommMonoid PseudoMetricSpace.toUniformSpace.toTopologicalSpace) hf) (SummationFilter.unconditional ℕ)
  rewrite [this] at euler_rewrite
  clear this
  rewrite [← euler_rewrite]
  clear euler_rewrite
  have hs : ∃ s : Finset Nat.Primes, s.image (fun i : Nat.Primes ↦ i.1) = (⌊x⌋.natAbs + 1).primesBelow :=
    exists_image_primes_eq_primesBelow (Int.natAbs ⌊x⌋ + 1)
  obtain ⟨s, hs⟩ := hs
  have f_eq_one: ∀ p ∉ s, ∑' (e : ℕ), f (↑p ^ e) = 1 := by
    intro p hp
    have pprime : Nat.Prime (p : ℕ) := p.2
    have hp_not_below : (p : ℕ) ∉ (⌊x⌋.natAbs + 1).primesBelow := by
      intro hmem
      rw [← hs, Finset.mem_image] at hmem
      obtain ⟨q, hq_s, hq_eq⟩ := hmem
      have : q = p := Subtype.ext hq_eq
      exact hp (this ▸ hq_s)
    have pfloor : (p : ℕ) ≥ ⌊x⌋.natAbs + 1 := by
      rw [Nat.mem_primesBelow] at hp_not_below
      by_contra hlt
      have : (p : ℕ) < ⌊x⌋.natAbs + 1 := by omega
      exact hp_not_below ⟨this, pprime⟩
    have h_tsum_zero : ∀ e, e ∉ ({0}: Finset ℕ) → f.toFun (↑p^e) = 0 := by
      intro e he
      have enz : e ≠ 0 := by
        intro he0; subst he0; exact he (Finset.mem_singleton_self 0)
      have pnin : (p : ℕ)^e ∉ S₁ x := by
        intro h
        simp only [S₁, Set.mem_setOf_eq] at h
        have h_dvd : (p : ℕ) ∣ (p : ℕ)^e := dvd_pow_self _ enz
        have hle : (p : ℝ) ≤ x := h (p : ℕ) pprime h_dvd
        have : (p : ℕ) ≤ ⌊x⌋ := Int.le_floor.mpr hle
        have contra : (p : ℕ) > ⌊x⌋ := by
          have : (p : ℕ) > ⌊x⌋.natAbs := by omega
          omega
        linarith
      rw [hf]
      simp [pnin]
    have ht : ∑' e : ℕ, f.toFun (↑p ^ e) = ∑ e ∈ {0}, f.toFun (↑p ^ e) :=
      tsum_eq_sum (s := {0}) h_tsum_zero
    simp only [Finset.sum_singleton, pow_zero, f_one_eq_one] at ht
    exact ht
  have tprod_rewrite := @tprod_eq_prod ℝ Nat.Primes _ _ (fun p : Nat.Primes => ∑' (e : ℕ), f (p.1 ^ e)) (SummationFilter.unconditional Nat.Primes) _ s f_eq_one
  rw [tprod_rewrite]
  have h_prod_img : (∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, ∑' k : ℕ, ((p : ℝ) ^ k)⁻¹) =
      ∏ y ∈ s, ∑' k : ℕ, ((y.1 : ℝ) ^ k)⁻¹ := by
    rw [← hs]
    exact Finset.prod_image (s := s) (g := fun i : Nat.Primes ↦ i.1) (f := fun (p : ℕ) ↦ ∑' k : ℕ, ((p : ℝ) ^ k)⁻¹) (fun i _ j _ hij => Subtype.ext hij)
  rw [h_prod_img]
  refine Finset.prod_congr rfl fun y hy => ?_
  congr 1
  ext e
  have hy_mem : y.1 ∈ (⌊x⌋.natAbs + 1).primesBelow := by
    rw [← hs]
    exact Finset.mem_image_of_mem (fun i : Nat.Primes ↦ i.1) hy
  have hy_le : (y.1 : ℝ) ≤ x := by
    rw [Nat.mem_primesBelow] at hy_mem
    have hx0 : 0 ≤ x := by linarith
    have : (y.1 : ℝ) ≤ ⌊x⌋₊ := by
      have : y.1 < ⌊x⌋.natAbs + 1 := hy_mem.1
      have h1 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
      have h_floor : ⌊x⌋.natAbs = ⌊x⌋₊ := by
        exact_mod_cast (Int.natAbs_of_nonneg h1).trans (Int.toNat_of_nonneg h1).symm
      have : y.1 ≤ ⌊x⌋₊ := by omega
      exact_mod_cast this
    exact le_trans this (Nat.floor_le hx0)
  have h_mem_S1 : (y.1 : ℕ) ^ e ∈ S₁ x := by
    intro p hp_prime hp_dvd
    have hp_eq : p = y.1 := by
      have := hp_prime.dvd_of_dvd_pow hp_dvd
      have hy_prime : y.1.Prime := y.2
      exact (Nat.dvd_prime hy_prime).mp this |>.resolve_left (Nat.Prime.ne_one hp_prime)
    rw [hp_eq]
    exact hy_le
  have : f.toFun (y.1 ^ e) = ((y.1 : ℝ) ^ e)⁻¹ := by
    have : f.toFun = (S₁ x).indicator (fun y ↦ (y : ℝ)⁻¹) := hf
    rw [this, Set.indicator_of_mem h_mem_S1]
    push_cast; rfl
  exact this
}

theorem log_riemann_bound (x: ℝ) (n: ℕ) (hxge : x ≥ n) (hxlt : x < n + 1): Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := by {
  -- We'll use the fact that $\log x \leq \sum_{i=1}^n \frac{1}{i}$ for $x \leq n+1$.
  have h_log_le_sum : Real.log x ≤ Real.log (n + 1) := by
    by_cases hn : n = 0 <;> simp_all +decide;
    · exact Real.log_nonpos hxge hxlt.le;
    · exact Real.log_le_log ( by linarith [ show ( n : ℝ ) > 0 by positivity ] ) hxlt.le;
  refine le_trans h_log_le_sum ?_;
  -- We'll use the fact that $\log(n+1) \leq \sum_{i=1}^n \frac{1}{i}$ for all $n$.
  have h_log_le_sum : ∀ n : ℕ, Real.log (n + 1) ≤ ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) := by
    -- By the properties of the harmonic series and the integral test, we know that $\sum_{i=1}^n \frac{1}{i} \geq \log(n+1)$.
    have h_harmonic : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ≥ Real.log (n + 1) := by
      intro n
      have h_integral : ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ≥ ∑ i ∈ Finset.range n, (Real.log (i + 2) - Real.log (i + 1)) := by
        gcongr;
        rw [ ← Real.log_div ( by positivity ) ( by positivity ) ];
        exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by rw [ div_sub_one, div_le_div_iff₀ ] <;> linarith )
      exact le_trans ( by exact Nat.recOn n ( by norm_num ) fun n ih => by norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith ) h_integral;
    assumption;
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ', h_log_le_sum ];
  simpa using h_log_le_sum n
}

theorem sum_le_infinite_sum (x: ℝ) (n: ℕ) (hxge : x ≥ n) (hxlt : x < n + 1): ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹):= by {
  have:= _root_.tsum_subtype (S₁ x) (fun y => (y:ℝ)⁻¹)
  rewrite [this]
  clear this
  rewrite [sum_eq_tsum_indicator]

  gcongr with i
  . rewrite [← summable_subtype_iff_indicator]
    apply Finset.summable
  . apply Summable.of_norm
    have hf:= arithmetic_f x n hxlt
    obtain ⟨f, hf⟩ := hf
    have sum := f_abs_summable x n hxge hxlt f hf
    have: ∀ i, f i = f.toFun i := by exact fun i ↦ rfl
    conv at sum =>
      left
      ext i
      rewrite [this i]
      rewrite [hf]
    assumption

  . have: i ∈ Set.Icc 1 n ∨ i ∉ Set.Icc 1 n := by exact Decidable.em (i ∈ Set.Icc 1 n)
    rcases this with (case | case)
    . simp [case]
      have: i ∈ S₁ x := by {
        unfold S₁
        have i_lt_n: i ≤ n := by simp_all only [ge_iff_le, Set.mem_Icc]
        have i_ge_one: i ≥ 1 := by simp_all only [ge_iff_le, Set.mem_Icc, and_true]
        have: ∀ p, Nat.Prime p → p ∣ i → ↑ p ≤ x := by {
          intro p pprime pdvd
          have: p ≤ i := by exact le_of_dvd i_ge_one pdvd
          have: p ≤ n := by bound
          have: (p: ℝ) ≤ ↑ n := by gcongr

          bound
        }
        rewrite [Set.mem_setOf]
        assumption
      }
      simp_all only [ge_iff_le, Set.mem_Icc, Set.indicator_of_mem, le_refl]
      sorry
    . simp [case]
      clear case
      have: i ∈ (S₁ x) ∨ i ∉ S₁ x := by exact Decidable.em (i ∈ S₁ x)
      rcases this with (case | case)
      . simp_all only [ge_iff_le, Set.indicator_of_mem, inv_nonneg, cast_nonneg]
        sorry
      . simp_all only [ge_iff_le, not_false_eq_true, Set.indicator_of_notMem, le_refl]
        sorry
}

theorem geom_series_simp (n : ℕ) (x : ℝ) (hxge : x ≥ n) (hxlt : x < n + 1) : (∏ p ∈ primesBelow (⌊x⌋.natAbs+1), (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) = (∏ k ∈ Icc 1 (primeCountingReal x), ((nth Nat.Prime (k-1)):ℝ) / ((nth Nat.Prime (k-1)) - 1)) := by {

  have: ∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, ∑' (k : ℕ), ((p: ℝ) ^ k)⁻¹ = ∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, ∑' (k : ℕ), ((p: ℝ)⁻¹ ^ k) := by {
    have: ∀ p: ℕ, ∀ k: ℕ, ((p: ℝ)^k)⁻¹ = ((p: ℝ)⁻¹)^k := by {
    intro p k
    bound
    }
    apply Finset.prod_congr
    rfl
    intro i hi
    congr
    ext k
    exact this i k
  }

  rewrite [this]
  clear this
  have:  ∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, ∑' (k : ℕ), ((p: ℝ))⁻¹ ^ k =  ∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, (1-(p: ℝ)⁻¹)⁻¹ := by {
    apply Finset.prod_congr
    rfl
    intro p hp

    have: p > 1 := by {
      have: Nat.Prime p := by exact prime_of_mem_primesBelow hp
      exact one_lt this
    }
    apply tsum_geometric_of_lt_one
    bound
    have: (p:ℝ) > 1 := by exact one_lt_cast.mpr this
    bound
  }
  rewrite [this]
  clear this
  have: ∏ p ∈ (⌊x⌋.natAbs + 1).primesBelow, (1 - (p: ℝ)⁻¹)⁻¹ = ∏ k ∈ Icc 1 (primeCountingReal (x)), (1 - ((nth Nat.Prime (k)): ℝ)⁻¹)⁻¹ := by {
    have: (⌊x⌋.natAbs + 1).primesBelow = (Icc 1 (primeCountingReal (x))).image (fun k => nth Nat.Prime (k)) := by {
      sorry
    }
    rewrite [this]
    clear this
    apply Finset.prod_image
    intros i hi j hj hij
    have := Nat.nth_injective (Nat.infinite_setOf_prime) hij
    assumption
  }
  rewrite [this]
  clear this
  apply Finset.prod_congr
  rfl
  intro i hi
  sorry

}

lemma H_P4_1 {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left, one_div_le_one_div h_p_pred_pos hk,
    @le_sub_iff_add_le]
  exact hp

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x ∈ Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  rw [← Finset.Ico_succ_right_eq_Icc]
  induction n with
  | zero => simp
  | succ n h =>
    simp only [succ_eq_succ, succ_eq_add_one] at h ⊢
    rw [Finset.prod_Ico_succ_top <| Nat.le_add_left 1 n]
    rcases lt_or_ge n 2 with _ | h2
    · interval_cases n
      · tauto
      · norm_num
    field_simp [Finset.prod_eq_zero_iff] at h ⊢
    rw [h h2]
    norm_num

lemma prod_Icc_le (n: ℕ) : (∏ x ∈ Icc 1 n, ((x + 1) : ℝ) / x) ≤ n + 1 := by {
  have: n < 2 ∨ 2 ≤ n := by omega
  rcases this with (case | case)
  . have: n = 0 ∨ n = 1 := by omega
    rcases this with (nval | nval) <;> simp [nval]
  . have := prod_Icc_succ_div n case
    linarith

}

lemma prime_counting_lemma (x : ℝ) :
  ∏ k ∈ Icc 1 (primeCountingReal x), ((nth Nat.Prime k):ℝ) / (↑(nth Nat.Prime k) - 1) ≤
    ∏ k ∈ Icc 1 (primeCountingReal x), (k + (1:ℝ)) / ↑k := by
      -- Since each term in the left product is less than the corresponding term in the right product, the entire product is less than or equal.
      have h_term_le : ∀ k ∈ Finset.Icc 1 (primeCountingReal x), ((Nat.nth Nat.Prime k : ℝ) / ((Nat.nth Nat.Prime k) - 1)) ≤ ((k + 1) : ℝ) / (k : ℝ) := by
        intro k hk; rw [ div_le_div_iff₀ ] <;> norm_num;
        · norm_cast;
          rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.Prime.one_lt ( Nat.prime_nth_prime k ), show Nat.nth Nat.Prime k ≥ k + 1 from Nat.recOn k ( Nat.Prime.pos ( Nat.prime_nth_prime 0 ) ) fun n ihn => Nat.succ_le_of_lt ( Nat.lt_of_le_of_lt ihn ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.lt_succ_self _ ) ) ) ];
        · exact Nat.Prime.one_lt ( Nat.prime_nth_prime k );
        · linarith [ Finset.mem_Icc.mp hk ];
      exact Finset.prod_le_prod ( fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) ) ) ) ) h_term_le

theorem infinity_of_primes₄ : Tendsto π atTop atTop := by

  -- two parts:
  -- (1) log x ≤ π x + 1
  -- (2) This implies that it is not bounded
  have H_log_le_primeCountingReal_add_one (n : ℕ) (x : ℝ) (hxge : x ≥ n) (hxlt : x < n + 1) :
      Real.log x ≤ primeCountingReal x + 1 :=
    calc
      Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := by exact log_riemann_bound x n hxge hxlt
      _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by exact sum_le_infinite_sum x n hxge hxlt
      _ ≤ (∏ p ∈ primesBelow (⌊x⌋.natAbs+1), (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by {have := euler_product_rearrangement x n hxge hxlt; bound}
      _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), ((nth Nat.Prime (k-1)):ℝ) / ((nth Nat.Prime (k-1)) - 1)) := by {have := geom_series_simp n x hxge hxlt; bound}
      _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k) / k-1) := by {sorry}
      _ ≤ primeCountingReal x + 1 := by {sorry}
  apply tendsto_atTop.2
  intro b
  apply Filter.eventually_atTop.2
  exists (⌈Real.exp (b+1)⌉.natAbs)
  intro b' hb'
  specialize H_log_le_primeCountingReal_add_one ⌈Real.exp (↑b+1)⌉.natAbs ⌈Real.exp (↑b+1)⌉.natAbs
  simp at H_log_le_primeCountingReal_add_one

  have b_le: Real.log ↑⌈Real.exp (↑b+1)⌉ ≥ Real.log (Real.exp (b+1)) := by {
    have: ⌈Real.exp (↑b+1)⌉ ≥ Real.exp (b+1) := by bound
    gcongr
  }
  simp at b_le
  unfold primeCountingReal at H_log_le_primeCountingReal_add_one
  split at H_log_le_primeCountingReal_add_one
  . rename_i case
    exfalso; exact case.not_gt (abs_pos.mpr (by positivity))
  . rename_i case
    clear case
    have: ⌊|(⌈Real.exp (↑b+1)⌉: ℝ)|⌋₊ = ⌈Real.exp (↑b+1)⌉.natAbs := by
      have: (⌈Real.exp (↑b+1)⌉).natAbs = |(⌈Real.exp (↑b+1)⌉: ℝ)| := by bound
      rewrite [← this]
      rewrite [Nat.floor_natCast]
      rfl
    rewrite [this] at H_log_le_primeCountingReal_add_one
    clear this
    have: (π ⌈Real.exp (↑b+1)⌉.natAbs: ℝ) ≤ π b' := by
      have: π ⌈Real.exp (↑b+1)⌉.natAbs ≤ π b' := by
        have:= Nat.monotone_primeCounting
        unfold Monotone at this
        specialize @this ⌈Real.exp (↑b+1)⌉.natAbs b'
        apply this at hb'
        assumption
      gcongr
    have log_le_b'_succ: Real.log ↑⌈Real.exp (↑b+1)⌉ ≤ ↑(π b') + 1 := by bound
    clear this H_log_le_primeCountingReal_add_one
    have: (b+1: ℝ) ≤ Real.log ↑⌈Real.exp (↑b+1)⌉ := by gcongr
    have b_le_pi_bound: (b+1:ℝ) ≤ ↑(π b') + 1 := by bound
    clear this
    have: (b+1) ≤ (π b') + 1 := by {
      exact_mod_cast b_le_pi_bound
    }
    linarith

/-!
### Fifth proof

using topology
-/

/-- The set of integers of the form `a + n * b` for `n ∈ ℤ`. -/
def N : ℤ → ℤ → Set ℤ := fun a b ↦ {a + n * b | n : ℤ}

/-- A set `O` is open if it is empty or if for any `a ∈ O`, it contains an arithmetic progression centered at `a`. -/
def isOpen : Set ℤ → Prop := fun O ↦ O = ∅ ∨ ∀ a ∈ O, ∃ b > 0, N a b ⊆ O

theorem infinity_of_primes₅ : { p : ℕ | p.Prime }.Infinite := by
  let TopoSpace : TopologicalSpace ℤ := {
    IsOpen := isOpen
    isOpen_univ := Or.inr fun a _ ↦ ⟨1, Int.zero_lt_one, Set.subset_univ _⟩
    isOpen_sUnion := by
      refine fun S hS ↦ Or.inr fun z hz ↦ ?_
      obtain ⟨t, tS, zt⟩ := hz
      rcases (hS t tS) with empty | ha
      · aesop
      obtain ⟨b, hb⟩ := ha z zt
      refine ⟨b, hb.1, Set.subset_sUnion_of_subset S t hb.2 tS⟩
    isOpen_inter := by
      intro O₁ O₂ hO₁ hO₂
      rcases hO₁ with rfl | hO₁
      · unfold isOpen; aesop
      rcases hO₂ with rfl | hO₂
      · unfold isOpen; aesop
      refine Or.inr fun a ⟨haO₁, haO₂⟩ ↦ ?_
      obtain ⟨b₁, hb₁, hNab₁⟩ := hO₁ a haO₁
      obtain ⟨b₂, hb₂, hNab₂⟩ := hO₂ a haO₂
      refine ⟨b₁*b₂, mul_pos hb₁ hb₂,
        Set.subset_inter (subset_trans ?_ hNab₁) (subset_trans ?_ hNab₂)⟩
      <;> simp only [N, Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
        add_right_inj]
      · refine fun k ↦ ⟨b₂*k, by ring⟩
      · refine fun k ↦ ⟨b₁*k, by ring⟩
  }
  have Infinite_of_NonemptyOpen {O : Set ℤ} (hnO : Set.Nonempty O)
      (hO : TopoSpace.IsOpen O): Set.Infinite O := by
    have Infinite_N {a b : ℤ} (ha : 0 < b ) : Set.Infinite (N a b) := by
      have : Function.Injective (fun k ↦ a + b*k) := by
        apply Function.Injective.comp (add_right_injective a)
        refine fun _ _ ↦ mul_left_cancel₀ (Int.ne_of_lt ha).symm
      apply Set.infinite_of_injective_forall_mem this
      unfold N; refine fun x ↦ ⟨x, by ring⟩
    rcases hO with _ | hO
    · aesop
    · obtain ⟨a, ha⟩ := hnO
      obtain ⟨b, hb, hOb⟩ := hO a ha
      apply Set.Infinite.mono hOb (Infinite_N hb)

  have IsClosed_N (a b : ℤ) (hb : 0 < b) : IsClosed (N a b):= by
    refine isOpen_compl_iff.1 (Or.inr fun n hn ↦ ⟨b, hb, fun k hk ↦ ?_⟩)
    simp only [N, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at *
    intro b₁ hb₁
    obtain ⟨m, hm⟩ := hk
    apply hn (b₁ - m)
    rw [sub_mul, add_sub, hb₁, ← hm]
    ring

  have : ⋃ p ∈ { p : ℕ | Nat.Prime p }, N 0 p = {-1, 1}ᶜ := by
    have (n : ℤ) (n_ne_one : n ≠ 1) (n_ne_negone : n ≠ -1):
        ∃ p, Nat.Prime p ∧ ∃m, m * (p : ℤ) = n:= by
      use n.natAbs.minFac
      constructor
      · refine Nat.minFac_prime ?_
        have := @Int.natAbs_eq_iff_sq_eq n 1
        aesop
      use n / n.natAbs.minFac
      rw [Int.ediv_mul_cancel]
      rw [Int.ofNat_dvd_left]
      exact (Nat.minFac_dvd (Int.natAbs n))
    ext n
    simp only [Set.mem_setOf_eq, N, zero_add, Set.mem_iUnion, exists_prop, Int.reduceNeg,
      Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro ⟨p, hp, ⟨k, hk⟩⟩
      have hp := Prime.not_dvd_one (Nat.prime_iff_prime_int.1 hp)
      constructor <;>  (intro h; rw [h] at hk; apply hp)
      · use -k
        nlinarith
      · use k
        nlinarith
    · refine fun hn ↦ this n hn.2 hn.1

  intro primes_finite
  have H : IsClosed (⋃ p ∈ { p : ℕ | Nat.Prime p }, N 0 p) := by
    refine Set.Finite.isClosed_biUnion primes_finite (fun p prime_p ↦ ?_)
    exact IsClosed_N 0 p (by exact_mod_cast Nat.Prime.pos prime_p)
  rw [this] at H
  rw [isClosed_compl_iff] at H
  have contradiction : Set.Infinite {-1, 1} :=
    Infinite_of_NonemptyOpen (show Set.Nonempty {-1, 1} by aesop) H
  exact contradiction (show Set.Finite {-1, 1} by aesop)

/-!
### Sixth proof

using the sum of inverses of primes
-/
-- see Archive.Wiedijk100Theorems.SumOfPrimeReciprocalsDiverges
theorem infinity_of_primes₆ :
  Tendsto (fun n ↦ ∑ p ∈ Finset.filter (fun p ↦ Nat.Prime p) (range n), 1 / (p : ℝ))
      atTop atTop := by
  sorry

/-!
### Appendix: Infinitely many more proofs
-/

/-- A sequence `S` is almost injective if the preimages of singletons are uniformly bounded. -/
def AlmostInjective (S : ℕ → ℤ) : Prop :=
  ∃ c : ℕ, ∀ k : ℕ, ∃ h : Set.Finite {n : ℕ | S n = k }, (Set.Finite.toFinset h).card ≤ c

variable (fn : NNReal)

open Real NNReal Topology

namespace Asymptotics

/-- A sequence `S` has subexponential growth if `|S n|` is bounded by a double exponential whose exponent grows slower than `log n`. -/
def ofSubexponentialGrowth (S : ℕ → ℤ) : Prop := ∃ f : ℕ → ℝ≥0, ∀ n,
  |S n| ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (f n : ℝ)) ∧ Tendsto (fun n ↦ (f n) / (log 2 n)) atTop (𝓝 0)

theorem infinitely_many_more_proofs (S : ℕ → ℤ)
  (h₁ : AlmostInjective S) (h₂ : ofSubexponentialGrowth S) :
  {p : Nat.Primes | ∃ n : ℕ, (p : ℤ) ∣ S n}.Finite := by
  sorry
