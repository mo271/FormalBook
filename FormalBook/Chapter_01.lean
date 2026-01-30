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
  ext n;
  constructor <;> intro hn <;> simp_all +decide [ S₁ ];
  · by_cases hn0 : n = 0 <;> simp_all +decide [ Nat.smoothNumbers ];
    · exact absurd ( hn ( Nat.find ( Nat.exists_infinite_primes ( ⌊x⌋₊ + 1 ) ) ) ( Nat.find_spec ( Nat.exists_infinite_primes ( ⌊x⌋₊ + 1 ) ) |>.2 ) ) ( by exact not_le_of_gt ( Nat.lt_of_floor_lt ( Nat.find_spec ( Nat.exists_infinite_primes ( ⌊x⌋₊ + 1 ) ) |>.1 ) ) );
    · exact fun p pp dp => Nat.lt_succ_of_le <| Nat.le_floor <| hn p pp dp;
  · intro p pp dp;
    -- Since $p$ is a prime factor of $n$ and $n$ is in the set of smooth numbers up to $\lfloor x \rfloor + 1$, it follows that $p \leq \lfloor x \rfloor$.
    have hp_le_floor : p ≤ ⌊x⌋₊ := by
      simp_all +decide [ Nat.smoothNumbers ];
      linarith [ hn.2 p pp dp hn.1 ];
    exact le_trans ( Nat.cast_le.mpr hp_le_floor ) ( Nat.floor_le ( show x ≥ 0 from le_of_not_gt fun h => by { rw [ Nat.floor_of_nonpos h.le ] at hp_le_floor; aesop } ) )

lemma norm_invRealHom_prime_lt_one (p : ℕ) (hp : Nat.Prime p) : ‖invRealHom p‖ < 1 := by
  erw [ Real.norm_of_nonneg ];
  · exact inv_lt_one_of_one_lt₀ <| mod_cast hp.one_lt;
  · exact inv_nonneg.2 <| Nat.cast_nonneg _

noncomputable def invRealMonoidHom : ℕ →* ℝ :=
  { toFun := fun n => (n : ℝ)⁻¹
    map_one' := by simp
    map_mul' := by
      intros x y
      simp [mul_comm] }

lemma summable_invRealHom_smoothNumbers (N : ℕ) : Summable (fun (m : Nat.smoothNumbers N) ↦ ‖invRealHom m‖) := by
  have := @EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric;
  convert this ( show ∀ { p : ℕ }, Nat.Prime p → ‖( invRealMonoidHom : ℕ → ℝ ) p‖ < 1 from ?_ ) N |>.1;
  intro p hp; erw [ Real.norm_of_nonneg ( inv_nonneg.2 <| Nat.cast_nonneg _ ) ] ; exact inv_lt_one_of_one_lt₀ <| mod_cast hp.one_lt;

theorem f_abs_summable (x : ℝ) (n : ℕ) (hxge : x ≥ ↑n) (hxlt : x < ↑n + 1)
  (f : ArithmeticFunction ℝ) (hf : f.toFun = (S₁ x).indicator fun y ↦ (↑y)⁻¹) :
  Summable fun x ↦ ‖f x‖ := by
    -- By Lemma `summable_invRealHom_smoothNumbers`, we know that `Summable (fun m : Nat.smoothNumbers (n + 1) ↦ ‖invRealHom m‖)`.
    have h_summable : Summable (fun m : Nat.smoothNumbers (n + 1) ↦ ‖invRealHom m‖) := by
      convert summable_invRealHom_smoothNumbers ( n + 1 ) using 1;
    have h_summable_f : Summable (fun m : ℕ ↦ ‖(f.toFun m)‖) := by
      have h_eq : ∀ m : ℕ, ‖(f.toFun m)‖ = if m ∈ S₁ x then ‖(invRealHom m)‖ else 0 := by
        unfold invRealHom; aesop;
      have h_eq : ∀ m : ℕ, ‖(f.toFun m)‖ = if m ∈ Nat.smoothNumbers (n + 1) then ‖(invRealHom m)‖ else 0 := by
        convert h_eq using 3;
        rw [ S1_eq_smoothNumbers ];
        norm_num [ show ⌊x⌋₊ = n by exact Nat.floor_eq_iff ( by linarith ) |>.2 ⟨ by linarith, by linarith ⟩ ];
      refine' summable_of_sum_le _ _;
      exact ∑' m : Nat.smoothNumbers ( n + 1 ), ‖invRealHom m‖;
      · exact fun _ => norm_nonneg _;
      · intro u; rw [ Finset.sum_congr rfl fun m hm => h_eq m ] ; simp +decide [ Finset.sum_ite ] ;
        refine' le_trans _ ( Summable.sum_le_tsum _ _ h_summable );
        rotate_left;
        exact Finset.subtype (fun x ↦ x ∈ (n + 1).smoothNumbers) u;
        · exact fun _ _ => abs_nonneg _;
        · refine' le_of_eq _;
          refine' Finset.sum_bij ( fun x hx => ⟨ x, _ ⟩ ) _ _ _ _ <;> aesop;
    convert h_summable_f using 1

lemma exists_image_primes_eq_primesBelow (n : ℕ) :
  ∃ (s : Finset Primes), s.image (fun p ↦ ↑p) = n.primesBelow := by
    use n.primesBelow.attach.image (fun p => ⟨p.val, Nat.prime_of_mem_primesBelow p.property⟩);
    ext; aesop

lemma arithmetic_f (x: ℝ) (n: ℕ) (hxlt : x < n + 1) : ∃ f: ArithmeticFunction ℝ, f.toFun = (S₁ x).indicator (fun y ↦ (↑y)⁻¹) := by {
    exists ZeroHom.mk ((S₁ x).indicator (fun y: ℕ ↦ (y: ℝ)⁻¹)) (by
  {
    have: ¬ (0 ∈ S₁ x) := by {
      unfold S₁
      rewrite [Set.mem_setOf]
      intro h
      contrapose! h
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
      exists p
      have: p ∣ 0 := by bound
      constructor
      . assumption
      . constructor
        . assumption
        . linarith
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
        have: 1 ∈ S₁ x := by {
          unfold S₁
          rewrite [Set.mem_setOf]
          intro p Hp contra
          contrapose! contra
          exact not_dvd_one Hp
        }
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
  have hs: ∃ s: Finset Primes, s.image (fun i: Primes => i.val) = (⌊x⌋.natAbs+1).primesBelow := by convert exists_image_primes_eq_primesBelow ( Int.natAbs ⌊x⌋ + 1 ) using 1
  obtain ⟨s, hs⟩ := hs
  have f_eq_one: ∀ p ∉ s, ∑' (e : ℕ), f (↑p ^ e) = 1 := by {
    intro p hp
    have: ∑' e: ℕ, f.toFun (↑p^e) = 1 := by {
      have pprime: Nat.Prime ↑p := by {
        have: ↑p ∈ { p : ℕ | Nat.Prime p }:= by bound
        rewrite [Set.mem_setOf] at this
        assumption
      }
      have: ↑p ∉ (⌊x⌋.natAbs+1).primesBelow := by {
        contrapose! hp
        rewrite [← hs] at hp
        rewrite [Function.Injective.mem_finset_image] at hp
        assumption
        exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
      }
      rewrite [Nat.mem_primesBelow] at this
      simp at this
      have pfloor: ↑ p ≥ (⌊x⌋.natAbs+1) := by {
        contrapose! pprime
        apply this at pprime; assumption
      }
      clear this
      have: ∀ e, e ∉ ({0}: Finset ℕ) → f.toFun (↑p^e) = 0 := by {
        intro e he
        have enz: e ≠ 0 := by bound
        clear he
        have pnin: (p: ℕ)^e ∉ S₁ x := by {
          unfold S₁
          rewrite [Set.mem_setOf]
          intro h
          specialize h ↑p
          apply h at pprime
          simp [enz] at pprime
          have: p ≤ ⌊x⌋ := by exact Int.le_floor.mpr pprime

          have contra: p > ⌊x⌋ := by {
            have contra: p > ⌊x⌋.natAbs := by bound
            omega
          }
          linarith
        }
        rewrite [hf]
        simp [pnin]
      }
      clear pfloor
      rewrite [tsum_eq_sum this]
      simp
      bound

    }
    bound
  }
  have tprod_rewrite := @tprod_eq_prod ℝ Primes _ _ (fun p => ∑' (e : ℕ), f (↑p ^ e)) (SummationFilter.unconditional Primes) _ (s) f_eq_one
  simp at tprod_rewrite
  rewrite [tprod_rewrite]
  rewrite [← hs]
  have: Set.InjOn (fun i: Primes => (i: Nat)) s := by {
    -- Since primes are unique by their value, if two primes are equal, their values must be the same. So, if i and j are primes in s and i.val = j.val, then i must equal j. That makes sense because each prime has a unique value. So the function is injective.
    intros i hi j hj hij; exact (by
    -- Since primes are unique by their value, if two primes have the same value, they must be the same prime. So, if i.val = j.val, then i = j. That makes sense because each prime has a unique value. So the function is injective.
    apply Subtype.ext; exact hij)
  }
  apply @Finset.prod_image ℕ Primes ℝ _ (fun p => ∑' (k : ℕ), (↑p ^ k)⁻¹) _ s (fun i: Primes => (i: Nat)) at this
  conv =>
    right
    rewrite [this]
  clear this
  apply Finset.prod_congr
  rfl
  intro y hy
  apply congrArg tsum
  ext i
  have: f.toFun (↑y^i) = (↑↑y ^ i)⁻¹ := by {
    rewrite [hf]
    have: (y: ℕ)^i ∈ S₁ x := by {
      intro p pp dp; have := Nat.Prime.dvd_of_dvd_pow pp dp; simp_all +decide [] ;
      -- Since $p$ divides $y.val$ and $y \in s$, we have $p \leq y.val$.
      have hp_le_y : p ≤ y.val := by
        exact Nat.le_of_dvd y.2.pos this;
      -- Since $y$ is a prime in the set $s$, and $s$ is defined as the image of the primes below $\lfloor x \rfloor + 1$, we have $y.val \leq \lfloor x \rfloor$.
      have hy_le_floor : y.val ≤ ⌊x⌋₊ := by
        -- Since $y$ is a prime in the set $s$, and $s$ is defined as the image of the primes below $\lfloor x \rfloor + 1$, we have $y \leq \lfloor x \rfloor$ by definition of `primesBelow`.
        have hy_le_floor : y.val ∈ Nat.primesBelow (⌊x⌋₊ + 1) := by
          convert hs ▸ Finset.mem_image_of_mem _ hy using 1;
          erw [ show ⌊x⌋ = ⌊x⌋₊ by exact Eq.symm <| Int.toNat_of_nonneg <| Int.floor_nonneg.mpr <| by linarith ] ; norm_num [ Int.natAbs_eq_iff ] ;
        exact Nat.le_of_lt_succ ( Nat.lt_of_succ_le ( Nat.succ_le_of_lt ( Nat.lt_of_mem_primesBelow hy_le_floor ) ) );
      exact le_trans ( Nat.cast_le.mpr ( hp_le_y.trans hy_le_floor ) ) ( Nat.floor_le ( show 0 ≤ x by linarith ) )
    }

    simp [this]
  }
  bound


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
    . simp [case]
      clear case
      have: i ∈ (S₁ x) ∨ i ∉ S₁ x := by exact Decidable.em (i ∈ S₁ x)
      rcases this with (case | case)
      . simp_all only [ge_iff_le, Set.indicator_of_mem, inv_nonneg, cast_nonneg]
      . simp_all only [ge_iff_le, not_false_eq_true, Set.indicator_of_notMem, le_refl]
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
