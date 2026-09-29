/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Nikolas Kuhn
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open ZMod Finset
open Polynomial (X)
open BigOperators

/-!
# The law of quadratic reciprocity

## Outline
  - Legendre symbol
  - Euler's criterion
  - First proof
    - Lemma of Gauss
    - proof
  - Second proof
    - A.
    - B.
    - First expression -- TO DO
    - Second expression -- TO DO
    - The multiplicative group of a finite field is cyclic
    - proof
-/

section
namespace book
namespace quadratic_reciprocity




/- Throughout this section, `p` is an odd prime. -/
variable (p : ℕ) (h_p : p ≠ 2) [Fact (Nat.Prime p)]

/-- The Legendre symbol `(a / p)`, where `p` is an odd prime. -/
def legendre_sym (a : ℤ) : ℤ :=
  ite ( (a : ZMod p) = 0) 0 $
    ite (∃ b : ZMod p, a = (b ^ (2 : ℤ) : ZMod p)) 1 (-1)

/--
Fermat's little theorem: If `a` is nonzero modulo the odd prime `p`, then `a ^ (p - 1) = 1`
modulo `p`.
-/
lemma fermat_little (a : ℤ) : (a : ZMod p) ≠ 0 → a ^ (p - 1) = (1 : ZMod p) := by
  intro ha
  let units_finset := (Finset.univ : Finset (ZMod p)).erase 0
  let image_finset := units_finset.image (fun x : ZMod p => (a : ZMod p) * x)
  -- multiplication by `a` permutes the nonzero residues
  have h_eq : units_finset = image_finset := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_erase.mpr
        ⟨mul_ne_zero ha (Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
    · exact (Finset.card_image_of_injective _ (mul_right_injective₀ ha)).ge
  -- hence the products over both sets agree
  have hprod : ∏ x ∈ units_finset, x =
      ∏ x ∈ units_finset.image (fun x : ZMod p => (a : ZMod p) * x), x :=
    congrArg (fun s => ∏ x ∈ s, x) h_eq
  rw [Finset.prod_image (mul_right_injective₀ ha).injOn,
    Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hcard : units_finset.card = p - 1 := by
    show ((Finset.univ : Finset (ZMod p)).erase 0).card = p - 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hne : ∏ x ∈ units_finset, x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x hx => (Finset.mem_erase.mp hx).1
  rw [hcard] at hprod
  -- cancel the (nonzero) product
  exact_mod_cast mul_right_cancel₀ hne (hprod.symm.trans (one_mul _).symm)


/-- Our `legendre_sym` agrees with Mathlib's `legendreSym`. -/
lemma legendre_sym_eq_legendreSym (a : ℤ) : legendre_sym p a = legendreSym p a := by
  unfold legendre_sym legendreSym
  rw [quadraticChar_apply, quadraticCharFun]
  congr 1
  apply if_congr _ rfl rfl
  simp only [zpow_ofNat, IsSquare, sq]

/-- The only nonzero residue modulo `2` is `1`. -/
lemma zmod_two_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem euler_criterion (a : ℤ) :
  (a : ZMod p) ≠ 0 → (legendre_sym p a : ZMod p) = a ^ ((p - 1) / 2) := by
  intro ha
  rw [legendre_sym_eq_legendreSym, legendreSym.eq_pow]
  rcases (Fact.out : p.Prime).eq_two_or_odd' with rfl | ⟨k, rfl⟩
  · -- `p = 2`: the only nonzero residue is `1`
    rw [zmod_two_eq_one_of_ne_zero _ ha]
    simp
  · congr 1; omega

lemma product_rule (a b : ℤ) :
  legendre_sym p (a * b) = (legendre_sym p a) * (legendre_sym p b) := by
  simp only [legendre_sym_eq_legendreSym, legendreSym.mul]

/-!
### First proof
For the statement, see `theorem quadratic_reciprocity_1`.
-/

/-
The original statement of Gauss' lemma, commented out because it is FALSE (and it also
needed a placeholder proof in its statement for the `LocallyFiniteOrder ℤ` instance, which is
not needed: Mathlib provides this instance).

It claims that the Legendre symbol *equals* the cardinality of the set of "negative remainders",
whereas Gauss' lemma says that the Legendre symbol is `-1` raised to the power of that
cardinality. Since the Legendre symbol is `1` or `-1` and a cardinality is a natural number,
the original equation can never hold; see `lemma_of_Gauss_original_false` below, which proves
that its conclusion fails whenever its hypotheses hold. (The hypotheses are satisfiable, e.g. by
taking `r i` to be the representative of `a * i` in `[-(p-1)/2, (p-1)/2]`.)

-/

/-- Auxiliary: for `p = 2k+1` and an integer `z ∈ [-(k+1), k]`, the canonical representative of
`z` in `[0, p)` exceeds `k` iff `z ∈ [-k, -1]`. -/
lemma gauss_val_iff (p k : ℕ) [Fact (Nat.Prime p)] (hpk : p = 2 * k + 1) (z : ℤ)
    (hz : -((k : ℤ) + 1) ≤ z ∧ z ≤ k) :
    k < (z : ZMod p).val ↔ -(k : ℤ) ≤ z ∧ z ≤ -1 := by
  have hv : (((z : ZMod p).val : ℕ) : ℤ) = z % (p : ℤ) := ZMod.val_intCast z
  have hp : (p : ℤ) = 2 * k + 1 := by rw [hpk]; push_cast; ring
  rcases le_or_gt 0 z with h | h
  · have : z % (p : ℤ) = z := Int.emod_eq_of_lt h (by omega)
    omega
  · have : z % (p : ℤ) = z + p := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    omega

/-- For `a ≢ 0 (mod 2)`, the Legendre symbol modulo `2` is `1`. -/
lemma legendre_sym_two (a : ℤ) (h_a : (a : ZMod 2) ≠ 0) : legendre_sym 2 a = 1 := by
  have h1 : (a : ZMod 2) = 1 := zmod_two_eq_one_of_ne_zero _ h_a
  unfold legendre_sym
  split_ifs with h0 hsq
  · exact absurd h0 h_a
  · rfl
  · exact absurd ⟨1, by rw [h1]; norm_num⟩ hsq

/-- **Lemma of Gauss** (corrected version of the original `lemma_of_Gauss`).

Changes with respect to the original statement:
* the conclusion is `legendre_sym p a = (-1) ^ card (...)` instead of
  `legendre_sym p a = card (...)` (the latter is false, see `lemma_of_Gauss_original_false`);
* the `have : LocallyFiniteOrder ℤ := ...` in the statement is removed, as Mathlib
  already provides this instance.

Here `r i` is a representative of `a * i` modulo `p` in `[(-p-1)/2, (p-1)/2]`, and the set
counted is the set of values `r i`, `1 ≤ i ≤ (p-1)/2`, that lie in `[-(p-1)/2, -1]`. -/
lemma lemma_of_Gauss (p : ℕ) [Fact (Nat.Prime p)] (a : ℤ) (h_a : (a : ZMod p) ≠ 0)
  ( r : ℤ → ℤ ) (h_r : (∀ i, (- (p: ℤ) - 1)/2 ≤ r i ∧ r i ≤ ((p : ℤ) - 1)/2))
  ( H : ∀ i, (r i : ℤ) = (a * i : ZMod p) ) :
   legendre_sym p a =
   (-1) ^ Finset.card ((Icc (1 : ℤ) (((p : ℤ)-1)/2)).image r ∩ (Icc (-((p: ℤ) - 1)/2) (-1))) := by
  rcases eq_or_ne p 2 with rfl | hp
  · rw [legendre_sym_two a h_a]
    norm_num
  rw [legendre_sym_eq_legendreSym, ZMod.gauss_lemma hp h_a]
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hk2 : p / 2 = k := by omega
  have hP : (p : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have e1 : ((p : ℤ) - 1) / 2 = k := by omega
  have e2 : (-(p : ℤ) - 1) / 2 = -((k : ℤ) + 1) := by omega
  have e3 : (-((p : ℤ) - 1)) / 2 = -(k : ℤ) := by omega
  rw [hk2, e1, e3]
  simp only [e1, e2] at h_r
  have key : ∀ j : ℤ, k < ((a * j : ℤ) : ZMod p).val ↔ -(k : ℤ) ≤ r j ∧ r j ≤ -1 := by
    intro j
    rw [← gauss_val_iff p k hk (r j) (h_r j), H j]; push_cast; rfl
  congr 1
  apply Finset.card_nbij (fun x : ℕ => r x)
  · intro x hx
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hx
    have := (key x).mp (by push_cast; exact hx.2)
    simp only [coe_inter, coe_image, coe_Icc, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc]
    exact ⟨⟨x, ⟨by omega, by omega⟩, rfl⟩, this⟩
  · intro x hx y hy hxy
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hx hy
    have h1 : ((x : ℤ) : ZMod p) = ((y : ℤ) : ZMod p) := by
      have := congrArg (fun z : ℤ => (z : ZMod p)) hxy
      simp only [H] at this
      exact mul_left_cancel₀ h_a this
    push_cast at h1
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  · intro y hy
    simp only [coe_inter, coe_image, coe_Icc, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc] at hy
    obtain ⟨⟨j, ⟨hj1, hj2⟩, rfl⟩, hy⟩ := hy
    refine ⟨j.toNat, ?_, ?_⟩
    · simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have := (key j).mpr hy
      have hj : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
      rw [← hj] at this; push_cast at this; exact this
    · simp only
      rw [Int.toNat_of_nonneg (by omega)]

/-- The conclusion of the original (commented out) statement of `lemma_of_Gauss` fails
whenever its hypotheses hold: the Legendre symbol is never equal to that cardinality. -/
lemma lemma_of_Gauss_original_false (p : ℕ) [Fact (Nat.Prime p)] (a : ℤ)
  (h_a : (a : ZMod p) ≠ 0)
  ( r : ℤ → ℤ ) (h_r : (∀ i, (- (p: ℤ) - 1)/2 ≤ r i ∧ r i ≤ ((p : ℤ) - 1)/2))
  ( H : ∀ i, (r i : ℤ) = (a * i : ZMod p) ) :
   legendre_sym p a ≠
   Finset.card ((Icc (1 : ℤ) (((p : ℤ)-1)/2)).image r ∩ (Icc (-((p: ℤ) - 1)/2) (-1))) := by
  rw [lemma_of_Gauss p a h_a r h_r H]
  generalize Finset.card _ = c
  intro h
  rcases Nat.even_or_odd c with hc | hc
  · rw [hc.neg_one_pow] at h
    have : c = 1 := by exact_mod_cast h.symm
    rw [this] at hc
    exact absurd hc (by decide)
  · rw [hc.neg_one_pow] at h
    omega

theorem quadratic_reciprocity_1 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (h_pq : p ≠ q) :
  (legendre_sym p q) * (legendre_sym q p) = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  rw [legendre_sym_eq_legendreSym, legendre_sym_eq_legendreSym, mul_comm,
    legendreSym.quadratic_reciprocity hp hq h_pq]
  rcases (Fact.out : p.Prime).eq_two_or_odd' with rfl | ⟨k, rfl⟩
  · exact absurd rfl hp
  rcases (Fact.out : q.Prime).eq_two_or_odd' with rfl | ⟨l, rfl⟩
  · exact absurd rfl hq
  congr 2 <;> omega

/-!
### Second Proof
TODO:
    - A.
    - B.
    - First expression
    - Second expression
    - The multiplicative group of a finite field is cyclic
-/

/- The group of units of a finite field is cyclic, i.e. has a multiplicative generator-/
lemma mult_cyclic (K : Type _) [Field K] [Fintype K] : ∃ ζ : Kˣ, ∀ α : Kˣ, ∃ k : ℤ, α = ζ ^ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, fun a => by obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg a); exact ⟨k, hk.symm⟩⟩


set_option linter.unusedVariables false in
/-- Frobenius is additive in a field with `q ^ (p - 1)` elements. The hypotheses `hp`, `hq` and
`h_pq` from the original statement are kept but turn out to be unnecessary. -/
lemma fact_A (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
  (h_pq : p ≠ q) (K : Type _) [Field K] [Fintype K] (H : Fintype.card K = q ^ (p - 1)) :
  ∀ a b : K, (a + b) ^ q = a ^ q + b ^ q := by
  obtain ⟨r, hr⟩ := CharP.exists K
  obtain ⟨n, hrp, hn⟩ := FiniteField.card K r
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  have : r = q := by
    have h1 : r ∣ q ^ (p - 1) := by rw [← H, hn]; exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp (hrp.dvd_of_dvd_pow h1)
  subst this
  intro a b
  exact add_pow_char a b r

/-
For any element `ζ` of multiplicative order `p` in a field `K`, we have a polynomial
decomposition`X^p - 1 = (X - ζ) * (X - ζ ^ 2) * ... * (X - ζ ^ p)`.
-/
/- The original statement, commented out because it is FALSE: the left-hand side has degree
`p - 1` while the right-hand side is a product of `p` monic linear factors, hence has degree `p`
(see `fact_B_original_false`). The hypotheses are satisfiable, e.g. `p = 2`, `K = ℚ`, `ζ = -1`.

`X ^ (p - 1) - 1 = ∏ i ∈ Icc 1 p, (X - C ζ ^ i)`
-/

/-- The equation in the original (commented out) statement of `fact_B` is false for every
prime `p`, field `K` and unit `ζ`, by comparing degrees (`p - 1` versus `p`). -/
lemma fact_B_original_false (p : ℕ) [hp : Fact (Prime p)] (K : Type _) [Field K] (ζ : Kˣ) :
  (X : Polynomial K) ^ (p - 1) - 1 ≠ ∏ i ∈ Icc 1 p, (X - (Polynomial.C (ζ : K)) ^ i) := by
  have hpp : p.Prime := Nat.prime_iff.mpr hp.out
  intro h
  have := congrArg Polynomial.natDegree h
  simp only [← map_pow] at this
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)] at this
  simp only [Polynomial.natDegree_X_sub_C, sum_const, Nat.card_Icc, smul_eq_mul, mul_one] at this
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] at this
  · simp at this; have := hpp.pos; omega
  · simp; have := hpp.two_le; omega

/-- Corrected version of `fact_B` (as in the book): the exponent on the left-hand side is `p`
instead of `p - 1`.
For any element `ζ ≠ 1` with `ζ ^ p = 1` (`p` prime) in a field `K`, we have
`X^p - 1 = (X - ζ) * (X - ζ ^ 2) * ... * (X - ζ ^ p)`. -/
lemma fact_B (p : ℕ) [hp : Fact (Prime p)] (K : Type _) [Field K] (ζ : Kˣ) (h_1 : ζ ^ p = 1)
  (h_2 : ζ ≠ 1) :
  X ^ p - 1 = ∏ i ∈ Icc 1 p, (X - (Polynomial.C (ζ : K)) ^ i) := by
  classical
  have hpp : p.Prime := Nat.prime_iff.mpr hp.out
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    have h1 : (ζ : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, h_1, Units.val_one]
    refine ⟨h1, fun l hl => ?_⟩
    have hd : orderOf (ζ : K) ∣ p := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime hpp).mp hd with h | h
    · exfalso; apply h_2; rw [orderOf_eq_one_iff] at h; exact Units.val_eq_one.mp h
    · rw [← h]; exact orderOf_dvd_of_pow_eq_one hl
  have hpos := hpp.pos
  have himg : Polynomial.nthRootsFinset p (1 : K) = (range p).image (fun i => (ζ : K) ^ i) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.mp hx
      exact (Polynomial.mem_nthRootsFinset hpos 1).mpr
        (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
    · rw [hprim.card_nthRootsFinset, card_image_of_injOn, card_range]
      intro i hi j hj h
      exact hprim.pow_inj (mem_range.mp hi) (mem_range.mp hj) h
  rw [Polynomial.X_pow_sub_one_eq_prod hpos hprim, himg,
    prod_image (fun i hi j hj h => hprim.pow_inj (mem_range.mp hi) (mem_range.mp hj) h)]
  have hIcc : Icc 1 p = Ico 1 (p + 1) := rfl
  rw [hIcc, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  simp only [← map_pow]
  have key := prod_range_succ (fun k => (X - Polynomial.C ((ζ : K) ^ k))) p
  rw [prod_range_succ'] at key
  rw [hprim.pow_eq_one, pow_zero] at key
  have hne : (X - Polynomial.C (1 : K)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have := mul_right_cancel₀ hne key
  simpa [add_comm] using this.symm

theorem quadratic_reciprocity_2 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (h_pq : p ≠ q) :
  (legendre_sym p q) * (legendre_sym q p) = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) :=
  quadratic_reciprocity_1 p q hp hq h_pq


end quadratic_reciprocity
end book
end --section
