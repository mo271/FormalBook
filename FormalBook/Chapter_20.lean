/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic
public import FormalBook.Mathlib.EdgeFinset

@[expose] public section

/-!
# In praise of inequalities

Formalization of Chapter 20 of "Proofs from THE BOOK" (Aigner & Ziegler), in a single file.

## Contents

- **Theorem I** (Cauchy–Schwarz): `cauchy_schwarz_inequality`;
  equality case: `cauchy_schwarz_eq_iff`, `cauchy_schwarz_eq_iff_not_linearIndependent`,
  `cauchy_schwarz_strict`.
- **Theorem II** (HM ≤ GM ≤ AM, with equality iff all `aᵢ` are equal), three proofs:
  - Proof 1 (Cauchy forward–backward induction, `CauchyAMGM.P_double`, `CauchyAMGM.P_pred`,
    `cauchy_amgm_fintype`): `harmonic_geometric_arithmetic₁`
  - Proof 2 (Alzer/Dacar, `log x ≤ x − 1`): `harmonic_geometric_arithmetic₂`
  - Proof 3 (Hirschhorn, Bernoulli's inequality, `hirschhorn_step`, `amgm_bernoulli_fintype`):
    `harmonic_geometric_arithmetic₃`
- **Theorem 1** (Laguerre): `laguerre_root_bound`, `laguerre_root_interval` (in terms of the roots),
  and `laguerre_polynomial` (in terms of the coefficients `aₙ₋₁`, `aₙ₋₂`, via Vieta).
- **Theorem 2** (Erdős–Gallai, `(2/3) T ≤ A`, Pólya's proof):
  - in the normal form (3) `f(x) = (1 - x²) ∏ (αᵢ - x) ∏ (βⱼ + x)`:
    `erdos_gallai_integral_bound` (A ≥ (4/3)·√(∏(αᵢ²-1)∏(βⱼ²-1))), `erdos_gallai_T_le`
    (HM–GM step), `erdos_gallai_full`, and the equality case `erdos_gallai_eq_iff`;
    `erdos_gallai_hasDerivAt_one` / `_neg_one` check the formulas for `f'(±1)`;
  - for arbitrary real-rooted polynomials: `erdos_gallai_normal_form` (reduction to (3)),
    `erdos_gallai_polynomial`, and equality only in degree 2: `erdos_gallai_polynomial_eq_iff`.
  - The right inequality `A ≤ (2/3) R` is not proved in the book (left as a challenge to the
    reader) and is not formalized here.
- **Theorem 3** (Mantel), two proofs: `mantel` (Cauchy), `mantel_amgm` (AM–GM);
  extremal case: `mantel_eq_adj_degree`, `mantel_eq_regular`, `mantel_eq_bipartite`,
  `mantel_eq_partition`, and `mantel_eq_iso_completeBipartite` (`n` even and `G ≅ K_{n/2,n/2}`).
-/

section CauchyAMGMSection

/-!
# Cauchy's forward–backward induction proof of AM–GM

`P(n)` is the statement `a₁ ⋯ aₙ ≤ ((a₁ + ⋯ + aₙ)/n)ⁿ` for nonnegative reals.
Following "Proofs from THE BOOK", Chapter 20, we prove
* `P(2)` from `(a - b)² ≥ 0`,
* (A) `P(n) → P(n - 1)`,
* (B) `P(n) ∧ P(2) → P(2n)`,
which together give `P(n)` for every `n`.
-/

open Finset

/-- The statement `P(n)` of the AM–GM inequality for `n` nonnegative reals. -/
def CauchyAMGM.P (n : ℕ) : Prop :=
  ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → ∏ i, a i ≤ ((∑ i, a i) / n) ^ n

namespace CauchyAMGM

lemma P_two : P 2 := by
  intro a _
  simp only [Fin.prod_univ_two, Fin.sum_univ_two]
  nlinarith [sq_nonneg (a 0 - a 1)]

lemma P_zero : P 0 := by
  intro a _; simp

/-- Step (B): `P(n)` and `P(2)` imply `P(2n)`. -/
lemma P_double {n : ℕ} (hn : P n) : P (2 * n) := by
  intro a ha
  have h2n : 2 * n = n + n := by ring
  -- reindex `Fin (2 * n)` as `Fin (n + n)`
  set b : Fin (n + n) → ℝ := fun i => a (Fin.cast h2n.symm i) with hb
  have hprod : ∏ i, a i = ∏ i, b i := by
    rw [hb]; exact (Fintype.prod_equiv (finCongr h2n) _ _ (fun i => rfl))
  have hsum : ∑ i, a i = ∑ i, b i := by
    rw [hb]; exact (Fintype.sum_equiv (finCongr h2n) _ _ (fun i => rfl))
  rw [hprod, hsum, Fin.prod_univ_add, Fin.sum_univ_add]
  set S₁ := ∑ i : Fin n, b (Fin.castAdd n i)
  set S₂ := ∑ i : Fin n, b (Fin.natAdd n i)
  have hb0 : ∀ i, 0 ≤ b i := fun i => ha _
  have h1 := hn (fun i => b (Fin.castAdd n i)) (fun i => hb0 _)
  have h2 := hn (fun i => b (Fin.natAdd n i)) (fun i => hb0 _)
  have hX : 0 ≤ S₁ / n := div_nonneg (sum_nonneg fun i _ => hb0 _) (Nat.cast_nonneg _)
  have hY : 0 ≤ S₂ / n := div_nonneg (sum_nonneg fun i _ => hb0 _) (Nat.cast_nonneg _)
  have hP2 : S₁ / n * (S₂ / n) ≤ ((S₁ / n + S₂ / n) / 2) ^ 2 := by
    nlinarith [sq_nonneg (S₁ / n - S₂ / n)]
  calc (∏ i : Fin n, b (Fin.castAdd n i)) * ∏ i : Fin n, b (Fin.natAdd n i)
      ≤ (S₁ / n) ^ n * (S₂ / n) ^ n :=
        mul_le_mul h1 h2 (prod_nonneg fun i _ => hb0 _) (pow_nonneg hX _)
    _ = (S₁ / n * (S₂ / n)) ^ n := by rw [mul_pow]
    _ ≤ (((S₁ / n + S₂ / n) / 2) ^ 2) ^ n :=
        pow_le_pow_left₀ (mul_nonneg hX hY) hP2 _
    _ = ((S₁ + S₂) / ((2 * n : ℕ) : ℝ)) ^ (2 * n) := by
        rw [← pow_mul]; congr 1; push_cast; ring

/-- Step (A): `P(n + 1)` implies `P(n)`. -/
lemma P_pred {n : ℕ} (hn : P (n + 1)) : P n := by
  intro a ha
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  set A := (∑ i, a i) / n with hA
  have hA0 : 0 ≤ A := div_nonneg (sum_nonneg fun i _ => ha i) (Nat.cast_nonneg _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have key := hn (Fin.snoc a A) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hA0
    · simpa using ha j)
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc] at key
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at key
  have hsumA : ∑ i, a i = n * A := by rw [hA]; field_simp
  have hmean : (∑ i, a i + A) / ((n + 1 : ℕ) : ℝ) = A := by
    rw [hsumA]; push_cast; field_simp
  rw [hmean, pow_succ] at key
  rcases hA0.lt_or_eq with hAp | hA0'
  · exact le_of_mul_le_mul_right key hAp
  · -- all `a i` vanish
    have hsum0 : ∑ i, a i = 0 := by rw [hsumA, ← hA0']; ring
    have hall := (sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hsum0
    have hprod0 : ∏ i, a i = 0 :=
      prod_eq_zero (mem_univ ⟨0, hpos⟩) (hall _ (mem_univ _))
    rw [hprod0]; exact pow_nonneg hA0 _

lemma P_pow_two (k : ℕ) : P (2 ^ k) := by
  induction k with
  | zero => intro a _; simp
  | succ k ih => rw [pow_succ, mul_comm]; exact P_double ih

lemma P_all (n : ℕ) : P n := by
  have key : ∀ k, P (2 ^ n - k) := by
    intro k
    induction k with
    | zero => simpa using P_pow_two n
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (2 ^ n - k) with h0 | h0
      · have : 2 ^ n - (k + 1) = 0 := by omega
        rw [this]; exact P_zero
      · have : 2 ^ n - k = (2 ^ n - (k + 1)) + 1 := by omega
        rw [this] at ih; exact P_pred ih
  have hle : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have := key (2 ^ n - n)
  rwa [Nat.sub_sub_self hle] at this

end CauchyAMGM

/-- **AM–GM** (Cauchy's forward–backward induction), for an arbitrary finite index type. -/
theorem cauchy_amgm_fintype {ι : Type*} [Fintype ι] (_hcard : 0 < Fintype.card ι)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ((∑ i, a i) / Fintype.card ι) ^ Fintype.card ι := by
  set e := Fintype.equivFin ι
  have h := CauchyAMGM.P_all (Fintype.card ι) (fun j => a (e.symm j)) (fun j => ha _)
  rwa [Fintype.prod_equiv e.symm _ a (fun _ => rfl),
    Fintype.sum_equiv e.symm _ a (fun _ => rfl)] at h

/-- Taking `n`-th roots: if `0 ≤ P ≤ Mⁿ` with `M ≥ 0` then `P^(1/n) ≤ M`. -/
theorem cauchy_amgm_rpow {n : ℕ} (hn : n ≠ 0) (P M : ℝ) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (h : P ≤ M ^ n) : P ^ ((1 : ℝ) / n) ≤ M := by
  calc P ^ ((1 : ℝ) / n) ≤ (M ^ n) ^ ((1 : ℝ) / n) :=
        Real.rpow_le_rpow hP h (by positivity)
    _ = M := by rw [one_div, Real.pow_rpow_inv_natCast hM hn]

end CauchyAMGMSection

section BernoulliAMGM

/-!
# Hirschhorn's proof of AM–GM via Bernoulli's inequality

Following "Proofs from THE BOOK", Chapter 20: from Bernoulli's inequality
`(1 + t)^(n+1) ≥ 1 + (n+1) t` (for `t ≥ -1`) one gets
`((a₁ + ⋯ + aₙ₊₁)/(n+1))^(n+1) ≥ aₙ₊₁ · ((a₁ + ⋯ + aₙ)/n)ⁿ`,
and AM–GM follows by ordinary induction.
-/

open Finset

/-- **Bernoulli's inequality** `(1 + t)^m ≥ 1 + m t` for real `t ≥ -1`. -/
theorem bernoulli_inequality (m : ℕ) {t : ℝ} (ht : -1 ≤ t) : 1 + m * t ≤ (1 + t) ^ m :=
  one_add_mul_le_pow (by linarith) m

/-- Hirschhorn's key step: for `S > 0`, `a > 0`, `n ≥ 1`,
`a · (S/n)ⁿ ≤ ((S + a)/(n+1))^(n+1)`. -/
theorem hirschhorn_step {n : ℕ} (hn : 0 < n) {S a : ℝ} (hS : 0 < S) (ha : 0 < a) :
    a * (S / n) ^ n ≤ ((S + a) / (n + 1)) ^ (n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m := S / n with hm
  have hm0 : 0 < m := div_pos hS hnR
  set t := (S + a) / (n + 1) / m - 1 with ht
  have ht1 : -1 ≤ t := by
    rw [ht]; have : 0 ≤ (S + a) / (n + 1) / m := by positivity
    linarith
  have hb := bernoulli_inequality (n + 1) ht1
  have h1t : 1 + t = (S + a) / (n + 1) / m := by rw [ht]; ring
  rw [h1t] at hb
  have hrhs : 1 + ((n + 1 : ℕ) : ℝ) * t = n * a / S := by
    rw [ht, hm]; push_cast; field_simp; ring
  rw [hrhs, div_pow] at hb
  have hmp : 0 < m ^ (n + 1) := pow_pos hm0 _
  rw [le_div_iff₀ hmp] at hb
  calc a * m ^ n = n * a / S * m ^ (n + 1) := by
        rw [hm, pow_succ]; field_simp
    _ ≤ ((S + a) / (n + 1)) ^ (n + 1) := hb

/-- AM–GM on `Fin n` by Hirschhorn's induction. -/
theorem amgm_bernoulli_fin : ∀ (n : ℕ) (_ : 0 < n) (a : Fin n → ℝ), (∀ i, 0 < a i) →
    ∏ i, a i ≤ ((∑ i, a i) / n) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro a ha
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have ih' := ih hn0 (fun i => a i.castSucc) (fun i => ha _)
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    set S := ∑ i : Fin n, a i.castSucc
    have hS : 0 < S := sum_pos (fun i _ => ha _) ⟨⟨0, hn0⟩, mem_univ _⟩
    have hstep := hirschhorn_step hn0 hS (ha (Fin.last n))
    calc (∏ i : Fin n, a i.castSucc) * a (Fin.last n)
        ≤ (S / n) ^ n * a (Fin.last n) :=
          mul_le_mul_of_nonneg_right ih' (ha _).le
      _ = a (Fin.last n) * (S / n) ^ n := mul_comm _ _
      _ ≤ ((S + a (Fin.last n)) / (n + 1)) ^ (n + 1) := hstep
      _ = ((S + a (Fin.last n)) / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by push_cast; ring

/-- **AM–GM** (Hirschhorn's Bernoulli proof) for an arbitrary finite index type. -/
theorem amgm_bernoulli_fintype {ι : Type*} [Fintype ι] (hcard : 0 < Fintype.card ι)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∏ i, a i ≤ ((∑ i, a i) / Fintype.card ι) ^ Fintype.card ι := by
  set e := Fintype.equivFin ι
  have h := amgm_bernoulli_fin (Fintype.card ι) hcard (fun j => a (e.symm j)) (fun j => ha _)
  rwa [Fintype.prod_equiv e.symm _ a (fun _ => rfl),
    Fintype.sum_equiv e.symm _ a (fun _ => rfl)] at h

end BernoulliAMGM

section ErdosGallaiDefs

/-!
# Erdős–Gallai: definitions and Pólya's integral estimate

For `α : Fin m → ℝ`, `β : Fin n → ℝ` with all `αᵢ, βⱼ ≥ 1` we consider
  `f(x) = (1 - x²) · ∏ᵢ (αᵢ - x) · ∏ⱼ (βⱼ + x)`,
which (up to a positive constant) is the general real-rooted polynomial that is positive
on `(-1, 1)` and vanishes at `±1` (equation (3) of the chapter).

* `erdosGallaiArea α β = ∫₋₁¹ f`  is the area `A`;
* `erdosGallaiDerivAtOne α β = f'(1)` and `erdosGallaiDerivAtNegOne α β = f'(-1)`
  (see `erdos_gallai_hasDerivAt_one`, `erdos_gallai_hasDerivAt_neg_one`);
* `erdosGallaiT α β = 2 f'(1) f'(-1) / (f'(1) - f'(-1))` is the area of the tangential
  triangle, formula (2) of the chapter (it is `0` when the denominator vanishes);
* `erdosGallaiCSq α β = ∏ᵢ (αᵢ² - 1) · ∏ⱼ (βⱼ² - 1)`.

The main analytic step is Pólya's estimate `A ≥ (4/3) √(∏(αᵢ²-1) ∏(βⱼ²-1))`
(`erdos_gallai_integral_bound`), obtained by symmetrisation `x ↦ -x` and AM–GM.
-/

open Finset

variable {m n : ℕ}

/-- The polynomial `f(x) = (1 - x²) ∏ᵢ (αᵢ - x) ∏ⱼ (βⱼ + x)`. -/
noncomputable def erdosGallaiF (α : Fin m → ℝ) (β : Fin n → ℝ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * (∏ i, (α i - x)) * ∏ j, (β j + x)

/-- The area `A = ∫₋₁¹ f(x) dx`. -/
noncomputable def erdosGallaiArea (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, erdosGallaiF α β x

/-- `f'(1) = -2 ∏ᵢ (αᵢ - 1) ∏ⱼ (βⱼ + 1)`. -/
def erdosGallaiDerivAtOne (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  -2 * (∏ i, (α i - 1)) * ∏ j, (β j + 1)

/-- `f'(-1) = 2 ∏ᵢ (αᵢ + 1) ∏ⱼ (βⱼ - 1)`. -/
def erdosGallaiDerivAtNegOne (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  2 * (∏ i, (α i + 1)) * ∏ j, (β j - 1)

/-- Area of the tangential triangle, `T = 2 f'(1) f'(-1) / (f'(1) - f'(-1))`
(formula (2) of the chapter; `T = 0` when `f'(1) = f'(-1)`). -/
noncomputable def erdosGallaiT (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  2 * erdosGallaiDerivAtOne α β * erdosGallaiDerivAtNegOne α β /
    (erdosGallaiDerivAtOne α β - erdosGallaiDerivAtNegOne α β)

/-- `C² = ∏ᵢ (αᵢ² - 1) ∏ⱼ (βⱼ² - 1)`, so that `-f'(1) f'(-1) = 4 C²`. -/
def erdosGallaiCSq (α : Fin m → ℝ) (β : Fin n → ℝ) : ℝ :=
  (∏ i, (α i ^ 2 - 1)) * ∏ j, (β j ^ 2 - 1)

section VersionStableHelpers

/-! Small product/mean lemmas proved directly, so the file does not depend on lemma names
or argument orders that differ between Mathlib versions. -/

private lemma prod_rpow_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (r : ℝ) : ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma geom_mean_eq_arith_mean_weighted_iff_pos {ι : Type*} (s : Finset ι)
    (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by
  by_cases A : ∃ i ∈ s, z i = 0
  · obtain ⟨i, his, hzi⟩ := A
    have hprod : ∏ i ∈ s, z i ^ w i = 0 :=
      Finset.prod_eq_zero his (by rw [hzi]; exact Real.zero_rpow (hw i his).ne')
    rw [hprod]
    constructor
    · intro h j hj
      rw [← h]
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => mul_nonneg (hw i hi).le (hz i hi))).mp h.symm j hj
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (hw j hj).ne'
      · exact h1
    · intro h
      rw [← h i his, hzi]
  · push Not at A
    have hz' : ∀ i ∈ s, 0 < z i := fun i h => lt_of_le_of_ne (hz i h) (fun a => A i h a.symm)
    have key := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ (Real.log (z i))
    have e1 : Real.exp (∑ i ∈ s, w i • Real.log (z i)) = ∏ i ∈ s, z i ^ w i := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [smul_eq_mul, Real.rpow_def_of_pos (hz' i hi), mul_comm]
    have e2 : ∑ i ∈ s, w i • Real.exp (Real.log (z i)) = ∑ i ∈ s, w i * z i :=
      Finset.sum_congr rfl fun i hi => by rw [smul_eq_mul, Real.exp_log (hz' i hi)]
    rw [e1, e2] at key
    rw [key]
    have hconst : ∀ c : ℝ, ∑ i ∈ s, w i * c = c := fun c => by
      rw [← Finset.sum_mul, hw', one_mul]
    constructor
    · intro h j hj
      have : ∀ i ∈ s, z i = z j := fun i hi =>
        Real.log_injOn_pos (hz' i hi) (hz' j hj) (h i hi ▸ h j hj ▸ rfl)
      rw [Finset.sum_congr rfl fun i hi => by rw [this i hi], hconst]
    · intro h j hj
      have : ∀ i ∈ s, z i = z j := fun i hi => (h i hi).trans (h j hj).symm
      simp only [smul_eq_mul]
      rw [Finset.sum_congr rfl fun i hi => by rw [this i hi], hconst]

private lemma prod_le_prod_aux {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (h1 a (Finset.mem_insert_self a s))
      (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      ((h0 a (Finset.mem_insert_self a s)).trans (h1 a (Finset.mem_insert_self a s)))

private lemma prod_lt_prod_aux {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (hs : s.Nonempty)
    (h0 : ∀ i ∈ s, 0 < f i) (h1 : ∀ i ∈ s, f i < g i) : ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h1 a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact mul_lt_mul'' (h1 a (Finset.mem_cons_self a s))
      (ih (fun i hi => h0 i (Finset.mem_cons_of_mem hi))
        (fun i hi => h1 i (Finset.mem_cons_of_mem hi)))
      (h0 a (Finset.mem_cons_self a s)).le
      (Finset.prod_nonneg fun i hi => (h0 i (Finset.mem_cons_of_mem hi)).le)

end VersionStableHelpers

section Derivatives

/-- An auxiliary derivative computation: if `h(x) = (1 - x) k(x)` then `h'(1) = -k(1)`. -/
private lemma hasDerivAt_one_sub_mul {k : ℝ → ℝ} (hk : DifferentiableAt ℝ k 1) :
    HasDerivAt (fun x => (1 - x) * k x) (-k 1) 1 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
  have h2 : HasDerivAt ((fun x : ℝ => 1 - x) * k) (-k 1) 1 :=
    (h1.mul hk.hasDerivAt).congr_deriv (by ring)
  exact h2

private lemma hasDerivAt_one_add_mul {k : ℝ → ℝ} (hk : DifferentiableAt ℝ k (-1)) :
    HasDerivAt (fun x => (1 + x) * k x) (k (-1)) (-1) := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 (-1) := by
    simpa using (hasDerivAt_id (-1 : ℝ)).const_add 1
  have h2 : HasDerivAt ((fun x : ℝ => 1 + x) * k) (k (-1)) (-1) :=
    (h1.mul hk.hasDerivAt).congr_deriv (by ring)
  exact h2

private lemma differentiable_prods (α : Fin m → ℝ) (β : Fin n → ℝ) :
    Differentiable ℝ (fun x : ℝ => (∏ i, (α i - x)) * ∏ j, (β j + x)) := by
  fun_prop

/-- `erdosGallaiDerivAtOne` is indeed the derivative of `f` at `1`. -/
theorem erdos_gallai_hasDerivAt_one (α : Fin m → ℝ) (β : Fin n → ℝ) :
    HasDerivAt (erdosGallaiF α β) (erdosGallaiDerivAtOne α β) 1 := by
  set k : ℝ → ℝ := fun x => (1 + x) * ((∏ i, (α i - x)) * ∏ j, (β j + x))
  have hk : DifferentiableAt ℝ k 1 :=
    ((differentiable_const _).add differentiable_id).mul (differentiable_prods α β)
      |>.differentiableAt
  have h := hasDerivAt_one_sub_mul hk
  have hf : erdosGallaiF α β = fun x => (1 - x) * k x := by
    funext x; simp only [erdosGallaiF, k]; ring
  rw [hf]
  convert h using 1
  simp only [erdosGallaiDerivAtOne, k]; ring

/-- `erdosGallaiDerivAtNegOne` is indeed the derivative of `f` at `-1`. -/
theorem erdos_gallai_hasDerivAt_neg_one (α : Fin m → ℝ) (β : Fin n → ℝ) :
    HasDerivAt (erdosGallaiF α β) (erdosGallaiDerivAtNegOne α β) (-1) := by
  set k : ℝ → ℝ := fun x => (1 - x) * ((∏ i, (α i - x)) * ∏ j, (β j + x))
  have hk : DifferentiableAt ℝ k (-1) :=
    ((differentiable_const _).sub differentiable_id).mul (differentiable_prods α β)
      |>.differentiableAt
  have h := hasDerivAt_one_add_mul hk
  have hf : erdosGallaiF α β = fun x => (1 + x) * k x := by
    funext x; simp only [erdosGallaiF, k]; ring
  rw [hf]
  convert h using 1
  simp only [erdosGallaiDerivAtNegOne, k]
  norm_num [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

end Derivatives

section IntegralBound

lemma erdos_gallai_C_sq_nonneg (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) : 0 ≤ erdosGallaiCSq α β := by
  unfold erdosGallaiCSq
  apply mul_nonneg
  · exact prod_nonneg fun i _ => by nlinarith [hα i]
  · exact prod_nonneg fun j _ => by nlinarith [hβ j]

/-- Pointwise estimate behind Pólya's argument: for `|x| ≤ 1`,
`(f(x) + f(-x))/2 ≥ (1 - x²) √C²`. -/
lemma erdos_gallai_pointwise (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * Real.sqrt (erdosGallaiCSq α β) ≤
      (erdosGallaiF α β x + erdosGallaiF α β (-x)) / 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hx2' : x ^ 2 ≤ 1 := by nlinarith
  have h1x : 0 ≤ 1 - x ^ 2 := by linarith
  set P := (∏ i, (α i - x)) * ∏ j, (β j + x) with hP
  set Q := (∏ i, (α i + x)) * ∏ j, (β j - x) with hQ
  have hP0 : 0 ≤ P := mul_nonneg (prod_nonneg fun i _ => by linarith [hα i])
    (prod_nonneg fun j _ => by linarith [hβ j])
  have hQ0 : 0 ≤ Q := mul_nonneg (prod_nonneg fun i _ => by linarith [hα i])
    (prod_nonneg fun j _ => by linarith [hβ j])
  have hfx : erdosGallaiF α β x = (1 - x ^ 2) * P := by
    simp only [erdosGallaiF, hP]; ring
  have hfnx : erdosGallaiF α β (-x) = (1 - x ^ 2) * Q := by
    simp only [erdosGallaiF, hQ, sub_neg_eq_add, neg_sq]; ring_nf
  have hPQ : erdosGallaiCSq α β ≤ P * Q := by
    have e : P * Q = (∏ i, (α i ^ 2 - x ^ 2)) * ∏ j, (β j ^ 2 - x ^ 2) := by
      rw [hP, hQ]
      have e1 : ∏ i, (α i ^ 2 - x ^ 2) = (∏ i, (α i - x)) * ∏ i, (α i + x) := by
        rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => by ring
      have e2 : ∏ j, (β j ^ 2 - x ^ 2) = (∏ j, (β j + x)) * ∏ j, (β j - x) := by
        rw [← prod_mul_distrib]; exact prod_congr rfl fun j _ => by ring
      rw [e1, e2]; ring
    rw [e]; unfold erdosGallaiCSq
    apply mul_le_mul
    · exact prod_le_prod_aux (fun i _ => by nlinarith [hα i]) (fun i _ => by linarith)
    · exact prod_le_prod_aux (fun j _ => by nlinarith [hβ j]) (fun j _ => by linarith)
    · exact prod_nonneg fun j _ => by nlinarith [hβ j]
    · exact prod_nonneg fun i _ => by nlinarith [hα i]
  rw [hfx, hfnx]
  set s := Real.sqrt (erdosGallaiCSq α β)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = erdosGallaiCSq α β :=
    Real.sq_sqrt (erdos_gallai_C_sq_nonneg α β hα hβ)
  -- `s ≤ (P + Q)/2` since `s² ≤ PQ ≤ ((P+Q)/2)²`
  have hsPQ : s ≤ (P + Q) / 2 := by
    have : s ^ 2 ≤ ((P + Q) / 2) ^ 2 := by nlinarith [sq_nonneg (P - Q)]
    exact (pow_le_pow_iff_left₀ hs0 (by positivity) two_ne_zero).mp this
  calc (1 - x ^ 2) * s ≤ (1 - x ^ 2) * ((P + Q) / 2) := mul_le_mul_of_nonneg_left hsPQ h1x
    _ = _ := by ring

lemma erdos_gallai_f_continuous (α : Fin m → ℝ) (β : Fin n → ℝ) :
    Continuous (erdosGallaiF α β) := by
  unfold erdosGallaiF
  fun_prop

/-- `∫₋₁¹ (1 - x²) dx = 4/3`. -/
lemma integral_one_sub_sq : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) = 4 / 3 := by
  rw [intervalIntegral.integral_sub (by simp) (by
    exact (continuous_pow 2).intervalIntegrable _ _)]
  simp [integral_pow]
  norm_num

/-- **Pólya's estimate**: `A ≥ (4/3) √(∏ᵢ (αᵢ² - 1) ∏ⱼ (βⱼ² - 1))`. -/
theorem erdos_gallai_integral_bound (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdosGallaiArea α β ≥ 4 / 3 * Real.sqrt (erdosGallaiCSq α β) := by
  have hcont := erdos_gallai_f_continuous α β
  -- symmetrisation: A = ∫ f(-x)
  have hsym : erdosGallaiArea α β = ∫ x in (-1 : ℝ)..1, erdosGallaiF α β (-x) := by
    unfold erdosGallaiArea
    rw [intervalIntegral.integral_comp_neg (fun x => erdosGallaiF α β x)]
    norm_num
  have havg : erdosGallaiArea α β =
      ∫ x in (-1 : ℝ)..1, (erdosGallaiF α β x + erdosGallaiF α β (-x)) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _) ((show Continuous fun x => erdosGallaiF α β (-x) from
        hcont.comp continuous_neg).intervalIntegrable _ _),
      ← hsym]
    unfold erdosGallaiArea; ring
  have hmono : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * Real.sqrt (erdosGallaiCSq α β) ≤
      ∫ x in (-1 : ℝ)..1, (erdosGallaiF α β x + erdosGallaiF α β (-x)) / 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous fun x : ℝ =>
        (1 - x ^ 2) * Real.sqrt (erdosGallaiCSq α β)).intervalIntegrable _ _
    · exact ((hcont.add (hcont.comp continuous_neg)).div_const 2).intervalIntegrable _ _
    · intro x hx; exact erdos_gallai_pointwise α β hα hβ hx
  rw [intervalIntegral.integral_mul_const, integral_one_sub_sq] at hmono
  rw [havg]; linarith

end IntegralBound

section TangentialTriangle

/-- `-f'(1) f'(-1) = 4 C²`. -/
lemma erdos_gallai_neg_deriv_mul (α : Fin m → ℝ) (β : Fin n → ℝ) :
    -(erdosGallaiDerivAtOne α β * erdosGallaiDerivAtNegOne α β) =
      4 * erdosGallaiCSq α β := by
  unfold erdosGallaiDerivAtOne erdosGallaiDerivAtNegOne erdosGallaiCSq
  have e1 : ∏ i, (α i ^ 2 - 1) = (∏ i, (α i - 1)) * ∏ i, (α i + 1) := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => by ring
  have e2 : ∏ j, (β j ^ 2 - 1) = (∏ j, (β j + 1)) * ∏ j, (β j - 1) := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun j _ => by ring
  rw [e1, e2]; ring

/-- Harmonic–geometric mean step: `T ≤ √(-f'(1) f'(-1)) = 2 √C²`. -/
theorem erdos_gallai_T_le (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdosGallaiT α β ≤ 2 * Real.sqrt (erdosGallaiCSq α β) := by
  set a := -erdosGallaiDerivAtOne α β with ha_def
  set b := erdosGallaiDerivAtNegOne α β with hb_def
  have ha : 0 ≤ a := by
    rw [ha_def]; unfold erdosGallaiDerivAtOne
    have h1 : 0 ≤ ∏ i, (α i - 1) := prod_nonneg fun i _ => by linarith [hα i]
    have h2 : 0 ≤ ∏ j, (β j + 1) := prod_nonneg fun j _ => by linarith [hβ j]
    nlinarith [mul_nonneg h1 h2]
  have hb : 0 ≤ b := by
    rw [hb_def]; unfold erdosGallaiDerivAtNegOne
    have h1 : 0 ≤ ∏ i, (α i + 1) := prod_nonneg fun i _ => by linarith [hα i]
    have h2 : 0 ≤ ∏ j, (β j - 1) := prod_nonneg fun j _ => by linarith [hβ j]
    nlinarith [mul_nonneg h1 h2]
  have hab : a * b = 4 * erdosGallaiCSq α β := by
    rw [ha_def, hb_def, ← erdos_gallai_neg_deriv_mul]; ring
  set g := Real.sqrt (erdosGallaiCSq α β)
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = erdosGallaiCSq α β :=
    Real.sq_sqrt (erdos_gallai_C_sq_nonneg α β hα hβ)
  have hT : erdosGallaiT α β = 2 * a * b / (a + b) := by
    unfold erdosGallaiT
    rw [show erdosGallaiDerivAtOne α β = -a by rw [ha_def]; ring, ← hb_def]
    rw [show -a - b = -(a + b) by ring, div_neg]; ring
  rw [hT]
  rcases (add_nonneg ha hb).lt_or_eq with hpos | hzero
  · rw [div_le_iff₀ hpos]
    -- `2ab = 8 g² ≤ 2g (a + b)` since `a + b ≥ 2√(ab) = 4g`
    have h4g : 4 * g ≤ a + b := by
      have : (4 * g) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this
    nlinarith
  · rw [← hzero, div_zero]; positivity

end TangentialTriangle

section Equality

/-- Symmetrisation: `A = ∫₋₁¹ (f(x) + f(-x))/2 dx`. -/
lemma erdos_gallai_area_eq_avg (α : Fin m → ℝ) (β : Fin n → ℝ) :
    erdosGallaiArea α β =
      ∫ x in (-1 : ℝ)..1, (erdosGallaiF α β x + erdosGallaiF α β (-x)) / 2 := by
  have hcont := erdos_gallai_f_continuous α β
  have hsym : erdosGallaiArea α β = ∫ x in (-1 : ℝ)..1, erdosGallaiF α β (-x) := by
    unfold erdosGallaiArea
    rw [intervalIntegral.integral_comp_neg (fun x => erdosGallaiF α β x)]
    norm_num
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (hcont.intervalIntegrable _ _) ((show Continuous fun x => erdosGallaiF α β (-x) from
      hcont.comp continuous_neg).intervalIntegrable _ _), ← hsym]
  unfold erdosGallaiArea; ring

/-- If there is at least one factor `αᵢ - x` or `βⱼ + x`, Pólya's pointwise estimate is strict
at `x = 0`. -/
lemma erdos_gallai_strict_at_zero (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) (hmn : 0 < m + n) :
    (1 - (0 : ℝ) ^ 2) * Real.sqrt (erdosGallaiCSq α β) <
      (erdosGallaiF α β 0 + erdosGallaiF α β (-0)) / 2 := by
  have hf0 : erdosGallaiF α β 0 = (∏ i, α i) * ∏ j, β j := by
    simp [erdosGallaiF]
  simp only [neg_zero, hf0]
  have hX : 0 < ∏ i, α i := prod_pos fun i _ => by linarith [hα i]
  have hY : 0 < ∏ j, β j := prod_pos fun j _ => by linarith [hβ j]
  have hP0 : 0 < (∏ i, α i) * ∏ j, β j := mul_pos hX hY
  rw [show (1 - (0 : ℝ) ^ 2) = 1 by norm_num, one_mul,
    show ((∏ i, α i) * ∏ j, β j + (∏ i, α i) * ∏ j, β j) / 2 = (∏ i, α i) * ∏ j, β j by ring,
    Real.sqrt_lt' hP0]
  have hsq : ((∏ i, α i) * ∏ j, β j) ^ 2 = (∏ i, α i ^ 2) * ∏ j, β j ^ 2 := by
    rw [mul_pow, prod_pow, prod_pow]
  rw [hsq]
  unfold erdosGallaiCSq
  set X1 := ∏ i, (α i ^ 2 - 1)
  set X2 := ∏ j, (β j ^ 2 - 1)
  have hX1 : 0 ≤ X1 := prod_nonneg fun i _ => by nlinarith [hα i]
  have hX2 : 0 ≤ X2 := prod_nonneg fun j _ => by nlinarith [hβ j]
  have hY1 : 0 < ∏ i, α i ^ 2 := prod_pos fun i _ => by nlinarith [hα i]
  have hY2 : 0 < ∏ j, β j ^ 2 := prod_pos fun j _ => by nlinarith [hβ j]
  have hXY1 : X1 ≤ ∏ i, α i ^ 2 :=
    prod_le_prod_aux (fun i _ => by nlinarith [hα i]) (fun i _ => by linarith)
  have hXY2 : X2 ≤ ∏ j, β j ^ 2 :=
    prod_le_prod_aux (fun j _ => by nlinarith [hβ j]) (fun j _ => by linarith)
  by_cases hC : X1 * X2 = 0
  · rw [hC]; exact mul_pos hY1 hY2
  have hX1p : ∀ i, 0 < α i ^ 2 - 1 := by
    intro i
    have hne : α i ^ 2 - 1 ≠ 0 := fun h0 =>
      hC (by rw [show X1 = 0 from prod_eq_zero (mem_univ i) h0, zero_mul])
    exact lt_of_le_of_ne (by nlinarith [hα i]) (Ne.symm hne)
  have hX2p : ∀ j, 0 < β j ^ 2 - 1 := by
    intro j
    have hne : β j ^ 2 - 1 ≠ 0 := fun h0 =>
      hC (by rw [show X2 = 0 from prod_eq_zero (mem_univ j) h0, mul_zero])
    exact lt_of_le_of_ne (by nlinarith [hβ j]) (Ne.symm hne)
  have hX2pos : 0 < X2 := prod_pos fun j _ => hX2p j
  have hX1pos : 0 < X1 := prod_pos fun i _ => hX1p i
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have hn : 0 < n := by omega
    have hlt : X2 < ∏ j, β j ^ 2 :=
      prod_lt_prod_aux ⟨⟨0, hn⟩, mem_univ _⟩ (fun j _ => hX2p j)
        (fun j _ => by linarith)
    exact mul_lt_mul' hXY1 hlt hX2 hY1
  · have hlt : X1 < ∏ i, α i ^ 2 :=
      prod_lt_prod_aux ⟨⟨0, hm⟩, mem_univ _⟩ (fun i _ => hX1p i)
        (fun i _ => by linarith)
    exact mul_lt_mul hlt hXY2 hX2pos hY1.le

/-- **Equality in `(2/3) T ≤ A`** holds exactly when there are no factors besides `1 - x²`,
i.e. when `f` has degree `2` (the parabola). -/
theorem erdos_gallai_eq_iff (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdosGallaiArea α β = 2 / 3 * erdosGallaiT α β ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro heq
    by_contra hmn
    have hmn' : 0 < m + n := by omega
    have hcont := erdos_gallai_f_continuous α β
    have hlt : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * Real.sqrt (erdosGallaiCSq α β) <
        ∫ x in (-1 : ℝ)..1, (erdosGallaiF α β x + erdosGallaiF α β (-x)) / 2 := by
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
      · exact (by fun_prop : Continuous fun x : ℝ =>
          (1 - x ^ 2) * Real.sqrt (erdosGallaiCSq α β)).continuousOn
      · exact ((hcont.add (hcont.comp continuous_neg)).div_const 2).continuousOn
      · intro x hx
        exact erdos_gallai_pointwise α β hα hβ ⟨hx.1.le, hx.2⟩
      · exact ⟨0, by norm_num, erdos_gallai_strict_at_zero α β hα hβ hmn'⟩
    rw [intervalIntegral.integral_mul_const, integral_one_sub_sq,
      ← erdos_gallai_area_eq_avg] at hlt
    have hT := erdos_gallai_T_le α β hα hβ
    linarith
  · rintro ⟨rfl, rfl⟩
    have hA : erdosGallaiArea α β = 4 / 3 := by
      unfold erdosGallaiArea erdosGallaiF
      simpa using integral_one_sub_sq
    rw [hA]
    simp [erdosGallaiT, erdosGallaiDerivAtOne, erdosGallaiDerivAtNegOne]
    norm_num

end Equality

end ErdosGallaiDefs

open Real
open RealInnerProductSpace
open BigOperators
open Classical


section Inequalities

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq V]

theorem cauchy_schwarz_inequality (a b : V) : ⟪ a, b ⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have h: ∀ (x : ℝ), ‖x • a + b‖ ^ 2 = x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
    simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
    simp only [inner_add_add_self, inner_smul_right, inner_smul_left, conj_trivial,
        add_left_inj, real_inner_comm]
    intro x
    ring_nf
  by_cases ha : a = 0
  · rw [ha]
    simp
  · by_cases hl : (∃ (l : ℝ),  b = l • a)
    · obtain ⟨l, hb⟩ := hl
      rw [hb]
      simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
      simp only [inner_smul_right, inner_smul_left, conj_trivial]
      ring_nf
      rfl
    · have : ∀ (x : ℝ), 0 < ‖x • a + b‖ := by
        intro x
        by_contra hx
        simp only [norm_pos_iff, ne_eq, Decidable.not_not] at hx
        absurd hl
        use -x
        rw [← add_zero (-x•a), ← hx]
        simp only [neg_smul, neg_add_cancel_left]
      have : ∀ (x : ℝ), 0 < ‖x • a + b‖ ^ 2 := by
        exact fun x ↦ sq_pos_of_pos (this x)
      have : ∀ (x : ℝ), 0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
        convert this
        exact (h _).symm
      have : ∀ (x : ℝ), 0 <  ‖a‖ ^ 2 * (x * x)  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2 := by
        intro x
        calc
          0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := this x
          _ = ‖a‖ ^ 2 * (x * x)  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2  := by ring_nf
      have ha_sq : ‖a‖ ^ 2 ≠ 0 := by aesop
      have := discrim_lt_zero ha_sq this
      unfold discrim at this
      have  : (2 * inner _ a b) ^ 2 < 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by linarith
      linarith
/-! ### Proof ₁: Cauchy forward-backward style
  Uses the Cauchy forward-backward induction for AM-GM (no Mathlib weighted AM-GM),
  with Mathlib's equality conditions. -/
set_option maxHeartbeats 3200000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem harmonic_geometric_arithmetic₁ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by
  /-  Proof ₁: Cauchy forward-backward induction
      The AM-GM inequality ∏aᵢ ≤ (∑aᵢ/n)ⁿ is proved by:
      Base P(2): from (a-b)² ≥ 0
      Forward: P(n) → P(2n) by doubling
      Backward: P(n+1) → P(n) by extending with the mean
      Then HM ≤ GM from applying AM-GM to 1/aᵢ.
      Equality conditions use Mathlib's weighted characterization. -/
  intro harmonic geometric arithmetic all_equal
  set S := Finset.univ (α := Finset.Icc 1 n)
  set w : Finset.Icc 1 n → ℝ := fun _ => (1 : ℝ) / n
  set i₁ : Finset.Icc 1 n := ⟨1, Finset.mem_Icc.mpr ⟨NeZero.one_le, hn⟩⟩
  set a₁ := a i₁
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hS_card : S.card = n := by simp [S, Fintype.card_coe, Nat.card_Icc]
  have hw_pos : ∀ i ∈ S, (0 : ℝ) < w i := fun _ _ => div_pos one_pos hn_pos
  have hw_nn : ∀ i ∈ S, (0 : ℝ) ≤ w i := fun i hi => le_of_lt (hw_pos i hi)
  have hw_sum : ∑ i ∈ S, w i = 1 := by
    simp only [w, Finset.sum_const, nsmul_eq_mul, hS_card]; field_simp
  have ha_nn : ∀ i ∈ S, (0 : ℝ) ≤ a i := fun i _ => le_of_lt (hpos i)
  have prod_a_pos : 0 < ∏ i ∈ S, a i := Finset.prod_pos (fun i _ => hpos i)
  have geom_pos : 0 < geometric := rpow_pos_of_pos prod_a_pos _
  have sum_inv_pos : 0 < ∑ i : Finset.Icc 1 n, 1 / a i :=
    Finset.sum_pos (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩
  -- Cardinality of Finset.Icc 1 n
  have hcard : Fintype.card (Finset.Icc 1 n) = n := by
    simp [Fintype.card_coe, Nat.card_Icc]
  have hcard_pos : 0 < Fintype.card (Finset.Icc 1 n) := by rw [hcard]; omega
  -- GM ≤ AM via Cauchy forward-backward induction (no geom_mean_le_arith_mean_weighted!)
  have amgm_a : ∏ i : Finset.Icc 1 n, a i ≤
      ((∑ i : Finset.Icc 1 n, a i) / n) ^ n := by
    have := cauchy_amgm_fintype hcard_pos a (fun i => le_of_lt (hpos i))
    rwa [hcard] at this
  have gm_le_am : geometric ≤ arithmetic := by
    exact cauchy_amgm_rpow (by omega) _ _ (le_of_lt prod_a_pos)
      (div_nonneg (Finset.sum_nonneg fun i _ => le_of_lt (hpos i)) hn_pos.le) amgm_a
  -- HM ≤ GM via Cauchy AM-GM applied to 1/aᵢ (no geom_mean_le_arith_mean_weighted!)
  set b : Finset.Icc 1 n → ℝ := fun i => (a i)⁻¹
  have hb_pos : ∀ i, 0 < b i := fun i => inv_pos.mpr (hpos i)
  have amgm_b : ∏ i : Finset.Icc 1 n, b i ≤
      ((∑ i : Finset.Icc 1 n, b i) / n) ^ n := by
    have := cauchy_amgm_fintype hcard_pos b (fun i => le_of_lt (hb_pos i))
    rwa [hcard] at this
  -- ∏ b i = (∏ a i)⁻¹
  have prod_b_eq : ∏ i : Finset.Icc 1 n, b i = (∏ i : Finset.Icc 1 n, a i)⁻¹ := by
    simp only [b]; exact Finset.prod_inv_distrib a
  -- ∑ b i = ∑ 1/a i
  have sum_b_eq : ∑ i : Finset.Icc 1 n, b i = ∑ i : Finset.Icc 1 n, 1 / a i := by
    congr 1; ext i; simp [b, one_div]
  -- From amgm_b: (∏ a)⁻¹ ≤ ((∑ 1/a)/n)^n
  -- Taking 1/n-th power: (∏ a)^(-1/n) ≤ (∑ 1/a)/n
  -- i.e. geometric⁻¹ ≤ (∑ 1/a)/n
  -- i.e. HM = n/(∑ 1/a) ≤ geometric
  have inv_gm_le : geometric⁻¹ ≤ (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    rw [← sum_b_eq]
    rw [prod_b_eq] at amgm_b
    have hge := cauchy_amgm_rpow (by omega) _ _
      (inv_nonneg.mpr (le_of_lt prod_a_pos))
      (div_nonneg (Finset.sum_nonneg fun i _ => le_of_lt (hb_pos i)) hn_pos.le) amgm_b
    rwa [Real.inv_rpow (le_of_lt prod_a_pos)] at hge
  have hm_le_gm : harmonic ≤ geometric := by
    change ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) ≤ geometric
    have : ((∑ i : Finset.Icc 1 n, 1 / a i) / ↑n)⁻¹ ≤ geometric⁻¹⁻¹ :=
      inv_anti₀ (by positivity) inv_gm_le
    rwa [inv_inv, inv_div] at this
  -- Equality conditions via Mathlib's weighted AM-GM characterization
  have lhs_a : ∏ i ∈ S, a i ^ w i = geometric :=
    prod_rpow_aux _ _ (fun i _ => le_of_lt (hpos i)) _
  have rhs_a : ∑ i ∈ S, w i * a i = arithmetic := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * a i = (∑ i : Finset.Icc 1 n, a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul]; simp [S, Finset.sum_div]
  have eq_a := geom_mean_eq_arith_mean_weighted_iff_pos S w a hw_pos hw_sum ha_nn
  have gm_eq_am : (geometric = arithmetic) ↔ all_equal := by
    rw [← lhs_a, ← rhs_a, eq_a]
    constructor
    · intro h i; linarith [h i₁ (Finset.mem_univ _), h i (Finset.mem_univ _)]
    · intro h j _
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := h
      simp_rw [hall]; rw [← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul, hS_card, hn_ne]
  have hb_nn : ∀ i ∈ S, (0 : ℝ) ≤ b i := fun i _ => le_of_lt (hb_pos i)
  have lhs_b : ∏ i ∈ S, b i ^ w i = geometric⁻¹ := by
    rw [prod_rpow_aux _ _ (fun i _ => le_of_lt (hb_pos i)) _]
    have : ∏ i ∈ S, b i = (∏ i ∈ S, a i)⁻¹ := by
      simp only [b]; exact Finset.prod_inv_distrib a
    rw [this, Real.inv_rpow (le_of_lt prod_a_pos)]
  have rhs_b : ∑ i ∈ S, w i * b i = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * (a i)⁻¹ = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul, one_div]; simp [S, Finset.sum_div]
  have eq_b := geom_mean_eq_arith_mean_weighted_iff_pos S w b hw_pos hw_sum hb_nn
  have hm_eq_gm : (harmonic = geometric) ↔ all_equal := by
    constructor
    · intro heq
      have geom_inv_eq : ∏ i ∈ S, b i ^ w i = ∑ i ∈ S, w i * b i := by
        rw [lhs_b, rhs_b]
        have heq' : geometric = ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) := heq.symm
        rw [heq', inv_div]
      rw [eq_b] at geom_inv_eq
      intro i
      have h1 := geom_inv_eq i₁ (Finset.mem_univ _)
      have hi := geom_inv_eq i (Finset.mem_univ _)
      have hbi : b i = b i₁ := by linarith
      exact inv_inj.mp hbi
    · intro heq
      change ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) =
        (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / ↑n)
      have hall : ∀ i : Finset.Icc 1 n, a i = a₁ := by
        intro i; exact heq i
      simp_rw [show a₁ = a i₁ from rfl] at hall
      simp_rw [hall]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.prod_const, Nat.card_Icc,
        Fintype.card_coe, show n + 1 - 1 = n from by omega]
      rw [← rpow_natCast a₁ n, ← rpow_mul (le_of_lt (hpos i₁))]
      have : (↑n : ℝ) * (1 / ↑n) = 1 := by field_simp
      rw [this, rpow_one]; field_simp
  exact ⟨hm_le_gm, gm_le_am, hm_eq_gm, gm_eq_am⟩

/-! ### Proof ₂: Alzer/Dacar approach via log x ≤ x - 1
  The key lemma is `Real.log_le_sub_one_of_pos`: for x > 0, log x ≤ x - 1.
  For GM ≤ AM: substitute x = aᵢ/AM, sum over i to get log(GM/AM) ≤ 0.
  For HM ≤ GM: apply the same argument to bᵢ = 1/aᵢ.
  Equality conditions use Mathlib's weighted characterization. -/
set_option maxHeartbeats 3200000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem harmonic_geometric_arithmetic₂ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by
  intro harmonic geometric arithmetic all_equal
  set S := Finset.univ (α := Finset.Icc 1 n)
  set w : Finset.Icc 1 n → ℝ := fun _ => (1 : ℝ) / n
  set i₁ : Finset.Icc 1 n := ⟨1, Finset.mem_Icc.mpr ⟨NeZero.one_le, hn⟩⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hS_card : S.card = n := by simp [S, Fintype.card_coe, Nat.card_Icc]
  have hw_pos : ∀ i ∈ S, (0 : ℝ) < w i := fun _ _ => div_pos one_pos hn_pos
  have hw_nn : ∀ i ∈ S, (0 : ℝ) ≤ w i := fun i hi => le_of_lt (hw_pos i hi)
  have hw_sum : ∑ i ∈ S, w i = 1 := by
    simp only [w, Finset.sum_const, nsmul_eq_mul, hS_card]; field_simp
  have ha_nn : ∀ i ∈ S, (0 : ℝ) ≤ a i := fun i _ => le_of_lt (hpos i)
  have prod_a_pos : 0 < ∏ i ∈ S, a i := Finset.prod_pos (fun i _ => hpos i)
  -- Rewriting lemmas
  have lhs_a : ∏ i ∈ S, a i ^ w i = geometric :=
    prod_rpow_aux _ _ (fun i _ => le_of_lt (hpos i)) _
  have rhs_a : ∑ i ∈ S, w i * a i = arithmetic := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * a i = (∑ i : Finset.Icc 1 n, a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul]; simp [S, Finset.sum_div]
  -- Part A: GM ≤ AM (Alzer/Dacar: via log x ≤ x - 1)
  have arith_pos : 0 < arithmetic :=
    div_pos (Finset.sum_pos (fun i _ => hpos i) ⟨i₁, Finset.mem_univ _⟩) hn_pos
  have gm_le_am : geometric ≤ arithmetic := by
    have geom_pos : 0 < geometric := rpow_pos_of_pos prod_a_pos _
    -- Suffices to show log GM ≤ log AM
    rw [← Real.log_le_log_iff geom_pos arith_pos]
    -- log GM = (1/n) * ∑ log aᵢ
    have log_geom : Real.log geometric = (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (a i) := by
      show Real.log ((∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / ↑n)) = _
      rw [Real.log_rpow prod_a_pos, Real.log_prod (s := Finset.univ) (fun i _ => ne_of_gt (hpos i))]
    -- For each i: log(aᵢ/AM) ≤ aᵢ/AM - 1, i.e. log aᵢ - log AM ≤ aᵢ/AM - 1
    have per_term : ∀ i : Finset.Icc 1 n,
        Real.log (a i) ≤ a i / arithmetic - 1 + Real.log arithmetic := by
      intro i
      have h1 := Real.log_le_sub_one_of_pos (div_pos (hpos i) arith_pos)
      rw [Real.log_div (ne_of_gt (hpos i)) (ne_of_gt arith_pos)] at h1
      linarith
    -- Sum: ∑ log aᵢ ≤ n * log AM
    have sum_bound : ∑ i : Finset.Icc 1 n, Real.log (a i) ≤ ↑n * Real.log arithmetic := by
      have h1 : ∑ i : Finset.Icc 1 n, Real.log (a i) ≤
          ∑ i : Finset.Icc 1 n, (a i / arithmetic - 1 + Real.log arithmetic) :=
        Finset.sum_le_sum (fun i _ => per_term i)
      have h2 : ∑ i : Finset.Icc 1 n, (a i / arithmetic - 1 + Real.log arithmetic) =
          (∑ i : Finset.Icc 1 n, a i) / arithmetic - ↑n + ↑n * Real.log arithmetic := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc,
          show n + 1 - 1 = n from by omega, nsmul_eq_mul]
        ring
      have h3 : (∑ i : Finset.Icc 1 n, a i) / arithmetic = ↑n := by
        show (∑ i : Finset.Icc 1 n, a i) / ((∑ i : Finset.Icc 1 n, a i) / ↑n) = ↑n
        exact div_div_cancel₀
          (ne_of_gt (Finset.sum_pos (fun i _ => hpos i) ⟨i₁, Finset.mem_univ _⟩))
      linarith
    rw [log_geom]
    have : (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (a i) ≤
        (1 / ↑n) * (↑n * Real.log arithmetic) :=
      mul_le_mul_of_nonneg_left sum_bound (by positivity)
    calc (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (a i)
        ≤ (1 / ↑n) * (↑n * Real.log arithmetic) := this
      _ = Real.log arithmetic := by field_simp
  -- Part B: GM = AM ↔ all_equal
  have gm_eq_am : (geometric = arithmetic) ↔ all_equal := by
    rw [← lhs_a, ← rhs_a,
      geom_mean_eq_arith_mean_weighted_iff_pos S w a hw_pos hw_sum ha_nn]
    constructor
    · intro h i; linarith [h i₁ (Finset.mem_univ _), h i (Finset.mem_univ _)]
    · intro h j _
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := h
      simp_rw [hall]; rw [← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul, hS_card, hn_ne]
  -- Part C: HM ≤ GM via reciprocal duality
  -- Define b_i = 1/a_i and apply AM-GM to b
  set b : Finset.Icc 1 n → ℝ := fun i => (a i)⁻¹
  have hb_pos : ∀ i, 0 < b i := fun i => inv_pos.mpr (hpos i)
  have hb_nn : ∀ i ∈ S, (0 : ℝ) ≤ b i := fun i _ => le_of_lt (hb_pos i)
  have lhs_b : ∏ i ∈ S, b i ^ w i = geometric⁻¹ := by
    rw [prod_rpow_aux _ _ (fun i _ => le_of_lt (hb_pos i)) _]
    have : ∏ i ∈ S, b i = (∏ i ∈ S, a i)⁻¹ := by
      simp only [b]; exact Finset.prod_inv_distrib a
    rw [this, Real.inv_rpow (le_of_lt prod_a_pos)]
  have rhs_b : ∑ i ∈ S, w i * b i = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * (a i)⁻¹ = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul, one_div]; simp [S, Finset.sum_div]
  have inv_gm_le : geometric⁻¹ ≤ (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    -- Apply the same log argument to bᵢ = 1/aᵢ: GM(b) ≤ AM(b)
    -- GM(b) = GM(a)⁻¹ = geometric⁻¹, AM(b) = (∑ 1/aᵢ)/n
    have sum_inv_pos' : 0 < ∑ i : Finset.Icc 1 n, 1 / a i :=
      Finset.sum_pos (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩
    have am_b_pos : 0 < (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n :=
      div_pos sum_inv_pos' hn_pos
    have geom_pos : 0 < geometric := rpow_pos_of_pos prod_a_pos _
    have inv_geom_pos : 0 < geometric⁻¹ := inv_pos.mpr geom_pos
    rw [← Real.log_le_log_iff inv_geom_pos am_b_pos]
    -- log(geometric⁻¹) = -log(geometric) = -(1/n)∑ log aᵢ = (1/n)∑ log(1/aᵢ)
    have prod_b_pos : 0 < ∏ i ∈ S, b i := Finset.prod_pos (fun i _ => hb_pos i)
    have log_inv_geom : Real.log geometric⁻¹ =
        (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (b i) := by
      have : ∀ i : Finset.Icc 1 n, Real.log (b i) = -Real.log (a i) := by
        intro i; simp [b, Real.log_inv]
      simp_rw [this, Finset.sum_neg_distrib, mul_neg]
      rw [Real.log_inv, show geometric = (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / ↑n) from rfl,
        Real.log_rpow prod_a_pos,
        Real.log_prod (s := Finset.univ) (fun i _ => ne_of_gt (hpos i))]
    -- For each i: log(bᵢ/AM_b) ≤ bᵢ/AM_b - 1
    set am_b := (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n
    have per_term_b : ∀ i : Finset.Icc 1 n,
        Real.log (b i) ≤ b i / am_b - 1 + Real.log am_b := by
      intro i
      have h1 := Real.log_le_sub_one_of_pos (div_pos (hb_pos i) am_b_pos)
      rw [Real.log_div (ne_of_gt (hb_pos i)) (ne_of_gt am_b_pos)] at h1
      linarith
    have sum_bound_b : ∑ i : Finset.Icc 1 n, Real.log (b i) ≤ ↑n * Real.log am_b := by
      have h1 : ∑ i : Finset.Icc 1 n, Real.log (b i) ≤
          ∑ i : Finset.Icc 1 n, (b i / am_b - 1 + Real.log am_b) :=
        Finset.sum_le_sum (fun i _ => per_term_b i)
      have h2 : ∑ i : Finset.Icc 1 n, (b i / am_b - 1 + Real.log am_b) =
          (∑ i : Finset.Icc 1 n, b i) / am_b - ↑n + ↑n * Real.log am_b := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc,
          show n + 1 - 1 = n from by omega, nsmul_eq_mul]
        ring
      have sum_b_eq : ∑ i : Finset.Icc 1 n, b i = ∑ i : Finset.Icc 1 n, 1 / a i := by
        congr 1; ext i; simp [b, one_div]
      have h3 : (∑ i : Finset.Icc 1 n, b i) / am_b = ↑n := by
        rw [sum_b_eq]
        show (∑ i : Finset.Icc 1 n, 1 / a i) / ((∑ i : Finset.Icc 1 n, 1 / a i) / ↑n) = ↑n
        exact div_div_cancel₀ (ne_of_gt (Finset.sum_pos
          (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩))
      linarith
    rw [log_inv_geom]
    have : (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (b i) ≤
        (1 / ↑n) * (↑n * Real.log am_b) :=
      mul_le_mul_of_nonneg_left sum_bound_b (by positivity)
    calc (1 / ↑n) * ∑ i : Finset.Icc 1 n, Real.log (b i)
        ≤ (1 / ↑n) * (↑n * Real.log am_b) := this
      _ = Real.log am_b := by field_simp
  have sum_inv_pos : 0 < ∑ i : Finset.Icc 1 n, 1 / a i :=
    Finset.sum_pos (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩
  have hm_le_gm : harmonic ≤ geometric := by
    change ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) ≤ geometric
    have : ((∑ i : Finset.Icc 1 n, 1 / a i) / ↑n)⁻¹ ≤ geometric⁻¹⁻¹ :=
      inv_anti₀ (by positivity) inv_gm_le
    rwa [inv_inv, inv_div] at this
  -- Part D: HM = GM ↔ all_equal
  have eq_b := geom_mean_eq_arith_mean_weighted_iff_pos S w b hw_pos hw_sum hb_nn
  have hm_eq_gm : (harmonic = geometric) ↔ all_equal := by
    constructor
    · intro heq
      have geom_inv_eq : ∏ i ∈ S, b i ^ w i = ∑ i ∈ S, w i * b i := by
        rw [lhs_b, rhs_b]
        have heq' : geometric = ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) := heq.symm
        rw [heq', inv_div]
      rw [eq_b] at geom_inv_eq
      intro i
      have h1 := geom_inv_eq i₁ (Finset.mem_univ _)
      have hi := geom_inv_eq i (Finset.mem_univ _)
      have hbi : b i = b i₁ := by linarith
      exact inv_inj.mp hbi
    · intro heq
      change ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) =
        (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / ↑n)
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := heq
      simp_rw [hall]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.prod_const, Nat.card_Icc,
        Fintype.card_coe, show n + 1 - 1 = n from by omega]
      rw [← rpow_natCast (a i₁) n, ← rpow_mul (le_of_lt (hpos i₁))]
      have : (↑n : ℝ) * (1 / ↑n) = 1 := by field_simp
      rw [this, rpow_one]; field_simp
  exact ⟨hm_le_gm, gm_le_am, hm_eq_gm, gm_eq_am⟩

/-! ### Proof ₃: Hirschhorn's Bernoulli induction proof
  AM-GM is proved by ordinary induction using Bernoulli's inequality (1+t)^n ≥ 1+nt.
  HM ≤ GM follows by applying AM-GM to the reciprocals.
  Equality conditions use Mathlib's weighted characterization. -/
set_option maxHeartbeats 3200000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem harmonic_geometric_arithmetic₃ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by
  intro harmonic geometric arithmetic all_equal
  -- Common setup
  set S := Finset.univ (α := Finset.Icc 1 n)
  set w : Finset.Icc 1 n → ℝ := fun _ => (1 : ℝ) / n
  set i₁ : Finset.Icc 1 n := ⟨1, Finset.mem_Icc.mpr ⟨NeZero.one_le, hn⟩⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hS_card : S.card = n := by simp [S, Fintype.card_coe, Nat.card_Icc]
  have hw_pos : ∀ i ∈ S, (0 : ℝ) < w i := fun _ _ => div_pos one_pos hn_pos
  have hw_nn : ∀ i ∈ S, (0 : ℝ) ≤ w i := fun i hi => le_of_lt (hw_pos i hi)
  have hw_sum : ∑ i ∈ S, w i = 1 := by
    simp only [w, Finset.sum_const, nsmul_eq_mul, hS_card]; field_simp
  have ha_nn : ∀ i ∈ S, (0 : ℝ) ≤ a i := fun i _ => le_of_lt (hpos i)
  have prod_a_pos : 0 < ∏ i ∈ S, a i := Finset.prod_pos (fun i _ => hpos i)
  -- Reciprocal sequence
  set b : Finset.Icc 1 n → ℝ := fun i => (a i)⁻¹
  have hb_pos : ∀ i, 0 < b i := fun i => inv_pos.mpr (hpos i)
  have hb_nn : ∀ i ∈ S, (0 : ℝ) ≤ b i := fun i _ => le_of_lt (hb_pos i)
  -- Key rewriting lemmas
  have lhs_a : ∏ i ∈ S, a i ^ w i = geometric :=
    prod_rpow_aux _ _ (fun i _ => le_of_lt (hpos i)) _
  have rhs_a : ∑ i ∈ S, w i * a i = arithmetic := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * a i = (∑ i : Finset.Icc 1 n, a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul]; simp [S, Finset.sum_div]
  have lhs_b : ∏ i ∈ S, b i ^ w i = geometric⁻¹ := by
    rw [prod_rpow_aux _ _ (fun i _ => le_of_lt (hb_pos i)) _]
    have : ∏ i ∈ S, b i = (∏ i ∈ S, a i)⁻¹ := by
      simp only [b]; exact Finset.prod_inv_distrib a
    rw [this, Real.inv_rpow (le_of_lt prod_a_pos)]
  have rhs_b : ∑ i ∈ S, w i * b i = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * (a i)⁻¹ = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul, one_div]; simp [S, Finset.sum_div]
  -- Split into four goals and prove each directly
  refine ⟨?hm_gm, ?gm_am, ?hm_eq, ?gm_eq⟩
  case gm_am =>
    -- GM ≤ AM via Bernoulli induction (no geom_mean_le_arith_mean_weighted!)
    have hcard : Fintype.card (Finset.Icc 1 n) = n := by
      simp [Fintype.card_coe, Nat.card_Icc]
    have hcard_pos : 0 < Fintype.card (Finset.Icc 1 n) := by rw [hcard]; omega
    have amgm_a : ∏ i : Finset.Icc 1 n, a i ≤
        ((∑ i : Finset.Icc 1 n, a i) / n) ^ n := by
      have := amgm_bernoulli_fintype hcard_pos a (fun i => hpos i)
      rwa [hcard] at this
    exact cauchy_amgm_rpow (by omega) _ _ (le_of_lt prod_a_pos)
      (div_nonneg (Finset.sum_nonneg fun i _ => le_of_lt (hpos i)) hn_pos.le) amgm_a
  case hm_gm =>
    -- HM ≤ GM via Bernoulli AM-GM applied to 1/aᵢ (no geom_mean_le_arith_mean_weighted!)
    show ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) ≤ geometric
    have sum_inv_pos : 0 < ∑ i : Finset.Icc 1 n, 1 / a i :=
      Finset.sum_pos (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩
    have hcard : Fintype.card (Finset.Icc 1 n) = n := by
      simp [Fintype.card_coe, Nat.card_Icc]
    have hcard_pos : 0 < Fintype.card (Finset.Icc 1 n) := by rw [hcard]; omega
    have amgm_b : ∏ i : Finset.Icc 1 n, b i ≤
        ((∑ i : Finset.Icc 1 n, b i) / n) ^ n := by
      have := amgm_bernoulli_fintype hcard_pos b (fun i => hb_pos i)
      rwa [hcard] at this
    have prod_b_eq : ∏ i : Finset.Icc 1 n, b i = (∏ i : Finset.Icc 1 n, a i)⁻¹ := by
      simp only [b]; exact Finset.prod_inv_distrib a
    have sum_b_eq : ∑ i : Finset.Icc 1 n, b i = ∑ i : Finset.Icc 1 n, 1 / a i := by
      congr 1; ext i; simp [b, one_div]
    have inv_gm_le : geometric⁻¹ ≤ (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
      rw [← sum_b_eq]; rw [prod_b_eq] at amgm_b
      have hge := cauchy_amgm_rpow (by omega) _ _
        (inv_nonneg.mpr (le_of_lt prod_a_pos))
        (div_nonneg (Finset.sum_nonneg fun i _ => le_of_lt (hb_pos i)) hn_pos.le) amgm_b
      rwa [Real.inv_rpow (le_of_lt prod_a_pos)] at hge
    have : ((∑ i : Finset.Icc 1 n, 1 / a i) / ↑n)⁻¹ ≤ geometric⁻¹⁻¹ :=
      inv_anti₀ (by positivity) inv_gm_le
    rwa [inv_inv, inv_div] at this
  case gm_eq =>
    rw [← lhs_a, ← rhs_a,
      geom_mean_eq_arith_mean_weighted_iff_pos S w a hw_pos hw_sum ha_nn]
    constructor
    · intro h i; linarith [h i₁ (Finset.mem_univ _), h i (Finset.mem_univ _)]
    · intro h j _
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := h
      simp_rw [hall]; rw [← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul, hS_card, hn_ne]
  case hm_eq =>
    have eq_b := geom_mean_eq_arith_mean_weighted_iff_pos S w b hw_pos hw_sum hb_nn
    have sum_inv_pos : 0 < ∑ i : Finset.Icc 1 n, 1 / a i :=
      Finset.sum_pos (fun i _ => div_pos one_pos (hpos i)) ⟨i₁, Finset.mem_univ _⟩
    constructor
    · intro heq
      have geom_inv_eq : ∏ i ∈ S, b i ^ w i = ∑ i ∈ S, w i * b i := by
        rw [lhs_b, rhs_b]
        have heq' : geometric = ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) := heq.symm
        rw [heq', inv_div]
      rw [eq_b] at geom_inv_eq
      intro i
      have h1 := geom_inv_eq i₁ (Finset.mem_univ _)
      have hi := geom_inv_eq i (Finset.mem_univ _)
      have hbi : b i = b i₁ := by linarith
      exact inv_inj.mp hbi
    · intro heq
      show ↑n / (∑ i : Finset.Icc 1 n, 1 / a i) =
        (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / ↑n)
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := heq
      simp_rw [hall]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.prod_const, Nat.card_Icc,
        Fintype.card_coe, show n + 1 - 1 = n from by omega]
      rw [← rpow_natCast (a i₁) n, ← rpow_mul (le_of_lt (hpos i₁))]
      have : (↑n : ℝ) * (1 / ↑n) = 1 := by field_simp
      rw [this, rpow_one]; field_simp

end Inequalities



section MantelCauchyProof

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

/-- **Mantel's theorem** (Proof 1, Cauchy inequality): A triangle-free graph on `n` vertices
has at most `n² / 4` edges. The original book also proves equality iff `G = K_{⌊n/2⌋,⌈n/2⌉}`;
this characterization is not yet formalized. -/
theorem mantel (h: G.CliqueFree 3) : #E ≤ (n^2 / 4) := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have adj_degree_bnd (i j : α) (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Assume the contrary ...
    by_contra hc; simp at hc

    -- ... then by pigeonhole there would exist a vertex k adjacent to both i and j ...
    obtain ⟨k, h⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (by simp) (by simp) hc
    simp at h
    obtain ⟨hik, hjk⟩ := h

    -- ... but then i, j, k would form a triangle, contradicting that G is triangle-free
    exact h {k, j, i} ⟨by aesop (add safe G.adj_symm), by simp [hij.ne', hik.ne', hjk.ne']⟩

  -- We need to define the sum of the degrees of the vertices of an edge ...
  let sum_deg (e : Sym2 α) : ℕ := Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  -- ... and establish a variant of adj_degree_bnd ...
  have adj_degree_bnd' (e : Sym2 α) (he: e ∈ E) : sum_deg e ≤ n := by
    induction e with | _ v w => simp at he; exact adj_degree_bnd v w (by simp [he])

  -- ... and the identity for the sum of the squares of the degrees ...
  have sum_sum_deg_eq_sum_deg_sq : ∑ e ∈ E, sum_deg e = ∑ v ∈ V, d(v)^2 := by
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ e.toFinset, d(v)                  :=
        Finset.sum_congr rfl (λ e he ↦ by
          induction e with
          | _ v w => simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v)  :=
        Finset.sum_congr rfl (by intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v)    :=
        Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v)               :=
        Finset.sum_congr rfl (λ v ↦ by simp [G.incidenceFinset_eq_filter v])
      _ = ∑ v ∈ V, d(v)^2                         := by simp [Nat.pow_two]

  -- We now slightly modify the main argument to avoid division by a potentially zero n ...
  have := calc #E * n^2
    _ = (n * (∑ e ∈ E, 1)) * n               := by simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm]
    _ = (∑ _ ∈ E, n) * n                     := by rw [Finset.mul_sum]; simp
    _ ≥ (∑ e ∈ E, sum_deg e) * n             :=
      Nat.mul_le_mul_right n (Finset.sum_le_sum adj_degree_bnd')
    _ = (∑ v ∈ V, d(v)^2) * (∑ v ∈ V, 1^2)   := by simp [sum_sum_deg_eq_sum_deg_sq]
    _ ≥ (∑ v ∈ V, d(v) * 1)^2                := (Finset.sum_mul_sq_le_sq_mul_sq V (λ v ↦ d(v)) 1)
    _ = (2 * #E)^2                           := by simp [G.sum_degrees_eq_twice_card_edges]
    _ = 4 * #E^2                             := by ring

  -- .. and clean up the inequality.
  rw [Nat.pow_two (#E)] at this
  rw [(Nat.mul_assoc 4 (#E) (#E)).symm] at this
  rw [Nat.mul_comm (4 * #E) (#E)] at this

  -- Now we can show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · simp [hE]
  · apply Nat.zero_lt_of_ne_zero at hE
    apply Nat.le_of_mul_le_mul_left this at hE
    rw [Nat.mul_comm] at hE
    exact (Nat.le_div_iff_mul_le (Nat.zero_lt_succ 3)).mpr hE

end MantelCauchyProof

section MantelEquality

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

/-- Equality condition for Mantel's theorem: if `G` is triangle-free and has exactly `n² / 4`
edges (encoded as `#E * 4 = n²` to avoid integer-division issues), then every edge has
endpoint degrees summing to `n`. -/
theorem mantel_eq_adj_degree (h : G.CliqueFree 3) (heq : #E * 4 = n ^ 2)
    (i j : α) (hij : G.Adj i j) : d(i) + d(j) = n := by

  -- Sum of degrees of edge endpoints
  let sum_deg (e : Sym2 α) : ℕ :=
    Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  -- Triangle-free ⟹ sum_deg e ≤ n for each edge
  have adj_degree_bnd' : ∀ e ∈ E, sum_deg e ≤ n := by
    intro e he
    induction e with | _ v w =>
      simp at he
      by_contra hc; push Not at hc
      obtain ⟨k, hk⟩ :=
        Finset.inter_nonempty_of_card_lt_card_add_card (by simp) (by simp) hc
      simp at hk; obtain ⟨hvk, hwk⟩ := hk
      exact h {k, w, v} ⟨by aesop (add safe G.adj_symm), by simp [he.ne', hvk.ne', hwk.ne']⟩

  -- Identity: ∑ sum_deg = ∑ d²
  have sum_sum_deg_eq : ∑ e ∈ E, sum_deg e = ∑ v ∈ V, d(v) ^ 2 := by
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ e.toFinset, d(v)                  :=
        Finset.sum_congr rfl (λ e he ↦ by
          induction e with
          | _ v w => simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v)  :=
        Finset.sum_congr rfl (by intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v)    :=
        Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v)               :=
        Finset.sum_congr rfl (λ v ↦ by simp [G.incidenceFinset_eq_filter v])
      _ = ∑ v ∈ V, d(v) ^ 2                       := by simp [Nat.pow_two]

  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨i⟩

  -- Cauchy–Schwarz + handshake: 4 * #E² ≤ (∑ sum_deg) * n
  have hcs : 4 * #E ^ 2 ≤ (∑ e ∈ E, sum_deg e) * n := by
    calc 4 * #E ^ 2
      _ = (2 * #E) ^ 2                             := by ring
      _ = (∑ v ∈ V, d(v) * 1) ^ 2                  := by simp [G.sum_degrees_eq_twice_card_edges]
      _ ≤ (∑ v ∈ V, d(v) ^ 2) * (∑ v ∈ V, 1 ^ 2)   :=
        Finset.sum_mul_sq_le_sq_mul_sq V (λ v ↦ d(v)) 1
      _ = (∑ e ∈ E, sum_deg e) * n                  := by simp [sum_sum_deg_eq]

  -- From heq: (∑ _ ∈ E, n) * n = 4 * #E²
  have hsum_n : (∑ _ ∈ E, n) * n = 4 * #E ^ 2 := by
    simp only [Finset.sum_const, smul_eq_mul]
    calc #E * n * n
      _ = #E * (n * n) := by ring
      _ = #E * n ^ 2   := by rw [Nat.pow_two]
      _ = #E * (#E * 4) := by rw [← heq]
      _ = 4 * #E ^ 2   := by ring

  -- Each sum_deg e = n: if any were strictly less, the total sum would be too small for
  -- Cauchy–Schwarz, contradicting the edge-count hypothesis.
  have hforall : ∀ e ∈ E, sum_deg e = n := by
    by_contra hc
    push Not at hc
    obtain ⟨e₀, he₀, hne⟩ := hc
    have hlt : sum_deg e₀ < n := lt_of_le_of_ne (adj_degree_bnd' e₀ he₀) hne
    have h1 : ∑ e ∈ E, sum_deg e < ∑ _ ∈ E, n :=
      Finset.sum_lt_sum adj_degree_bnd' ⟨e₀, he₀, hlt⟩
    have h2 : (∑ e ∈ E, sum_deg e) * n < (∑ _ ∈ E, n) * n :=
      Nat.mul_lt_mul_of_pos_right h1 hn
    linarith

  -- Apply to the edge {i, j}
  have hedge : s(i, j) ∈ E := G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hij)
  exact hforall s(i, j) hedge

/-- If G is triangle-free and #E * 4 = n², then every vertex has degree n / 2. -/
theorem mantel_eq_regular (h : G.CliqueFree 3) (heq : #E * 4 = n ^ 2)
    (v : α) : d(v) = n / 2 := by
  have hadj := mantel_eq_adj_degree h heq
  -- We show 4 * ∑ d(v)² = n² * n and use handshaking to derive 2*d(v)=n for all v.

  -- Identity: ∑_{e∈E} (d(i)+d(j)) = ∑_v d(v)²  (double counting)
  let sum_deg (e : Sym2 α) : ℕ :=
    Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  have sum_eq_sq : ∑ e ∈ E, sum_deg e = ∑ w ∈ V, d(w) ^ 2 := by
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ e.toFinset, d(v) := Finset.sum_congr rfl (λ e he ↦ by
          induction e with | _ v w =>
            simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v) := Finset.sum_congr rfl (by
          intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v) :=
          Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v) := Finset.sum_congr rfl (λ v ↦ by
          simp [G.incidenceFinset_eq_filter v])
      _ = ∑ w ∈ V, d(w) ^ 2 := by simp [Nat.pow_two]

  have hforall : ∀ e ∈ E, sum_deg e = n := by
    intro e he; induction e with | _ i j => simp at he; exact hadj i j he

  have hsumsq : ∑ w ∈ V, d(w) ^ 2 = #E * n := by
    rw [← sum_eq_sq, Finset.sum_congr rfl hforall]; simp [Finset.sum_const]

  suffices h2d : 2 * d(v) = n by omega

  -- Cast everything to ℤ
  have hsumsq_z : (∑ w : α, (d(w) : ℤ) ^ 2) = ↑(#E) * ↑n := by
    exact_mod_cast hsumsq
  have hsumdeg_z : (∑ w : α, (d(w) : ℤ)) = 2 * ↑(#E) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this
  have heq_z : (↑(#E) : ℤ) * 4 = ↑n ^ 2 := by exact_mod_cast heq

  -- ∑ (2d - n)² = 4 ∑ d² - 4n ∑d + n²·n = 4·#E·n - 4n·2#E + n³ = 4n#E - 8n#E + n³
  --             = n³ - 4n#E = n·(n² - 4#E) = 0
  have key : ∑ w : α, ((2 * (d(w) : ℤ) - ↑n) ^ 2) = 0 := by
    have expand : ∀ w : α, (2 * (d(w) : ℤ) - ↑n) ^ 2 =
        4 * (d(w) : ℤ) ^ 2 - 4 * ↑n * (d(w) : ℤ) + ↑n ^ 2 := by intro; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    nlinarith [hsumsq_z, hsumdeg_z, heq_z]

  have hv_sq : (2 * (d(v) : ℤ) - ↑n) ^ 2 = 0 := by
    have hnn := Finset.sum_eq_zero_iff_of_nonneg
      (f := fun w => (2 * (d(w) : ℤ) - ↑n) ^ 2) (s := Finset.univ)
      (fun w _ => sq_nonneg _)
    rw [hnn] at key
    exact key v (Finset.mem_univ v)
  have h0 : 2 * (d(v) : ℤ) - ↑n = 0 := by
    nlinarith [sq_nonneg (2 * (d(v) : ℤ) - ↑n)]
  linarith

/-- If G is triangle-free and #E * 4 = n², then G is a complete bipartite graph:
there exist disjoint sets A, B partitioning V with |A| = |B| = n/2 such that
every vertex in A is adjacent to every vertex in B. -/
theorem mantel_eq_bipartite (h : G.CliqueFree 3) (heq : #E * 4 = n ^ 2)
    [Nonempty α] :
    ∃ (A B : Finset α), A ∩ B = ∅ ∧ A ∪ B = Finset.univ ∧
      #A = n / 2 ∧ #B = n / 2 ∧ ∀ i ∈ A, ∀ j ∈ B, G.Adj i j := by
  have hreg := mantel_eq_regular h heq
  -- Triangle-free: neighbor sets are independent
  have hind : ∀ v : α, G.IsIndepSet (G.neighborFinset v : Set α) := fun v => by
    rw [SimpleGraph.neighborFinset_def, Set.coe_toFinset]
    exact G.isIndepSet_neighborSet_of_triangleFree h v
  -- Pick any vertex v₀
  obtain ⟨v₀⟩ := ‹Nonempty α›
  set A := G.neighborFinset v₀
  set B := Aᶜ
  have hA_card : #A = n / 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg v₀
  have h2n : 2 ∣ n := by
    have h4 : 4 ∣ n ^ 2 := ⟨#E, by linarith⟩
    have h2sq : 2 ∣ n ^ 2 := dvd_trans ⟨2, rfl⟩ h4
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2sq
  have hB_card : #B = n / 2 := by
    have hc : #B = n - #A := Finset.card_compl A
    obtain ⟨k, hk⟩ := h2n
    omega
  refine ⟨A, B, Finset.inter_compl A, Finset.union_compl A, hA_card, hB_card, ?_⟩
  intro i hi j hj
  -- i ∈ A = N(v₀), so A is independent. N(i) ∩ A = ∅, so N(i) ⊆ B.
  -- |N(i)| = n/2 = |B|, so N(i) = B, hence j ∈ N(i).
  have hA_indep := hind v₀
  have hNi_sub : G.neighborFinset i ⊆ B := by
    intro w hw
    rw [Finset.mem_compl]
    intro ha
    have hadj_iw : G.Adj i w := by rwa [SimpleGraph.mem_neighborFinset] at hw
    by_cases hiw : i = w
    · exact G.irrefl (hiw ▸ hadj_iw)
    · exact absurd hadj_iw (hA_indep hi ha hiw)
  have hNi_eq : G.neighborFinset i = B :=
    Finset.eq_of_subset_of_card_le hNi_sub (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hreg i]; omega)
  rw [← hNi_eq] at hj
  rwa [SimpleGraph.mem_neighborFinset] at hj

end MantelEquality

section MantelAMGMProof

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

-- Helper: a*b ≤ (a+b)^2/4 for natural numbers
private lemma nat_mul_le_sq_div4 (a b : ℕ) : a * b ≤ (a + b) ^ 2 / 4 := by
  have h : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b : ℤ)]
  omega

-- For triangle-free G, each vertex degree ≤ indepNum
omit [DecidableEq α] in
private lemma degree_le_indepNum (h : G.CliqueFree 3) (v : α) :
    G.degree v ≤ G.indepNum := by
  have hind : G.IsIndepSet (G.neighborSet v) :=
    G.isIndepSet_neighborSet_of_triangleFree h v
  have hind' : G.IsIndepSet (G.neighborFinset v : Set α) := by
    intro x hx y hy hne
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx hy
    exact hind hx hy hne
  exact hind'.card_le_indepNum

theorem mantel_amgm (h: G.CliqueFree 3) : G.edgeFinset.card ≤ (Fintype.card α)^2 / 4 := by
  -- Obtain a maximum independent set A
  obtain ⟨A, hA⟩ := G.maximumIndepSet_exists
  set n := Fintype.card α
  set α_val := G.indepNum
  -- Every edge has at least one endpoint in Aᶜ
  -- Count: |E| ≤ ∑_{v ∈ Aᶜ} deg(v) ≤ |Aᶜ| * α_val ≤ n²/4
  -- Step 1: |E| ≤ ∑_{v ∈ Aᶜ} deg(v)
  -- Each edge has an endpoint in Aᶜ, so the sum of degrees over Aᶜ counts every edge.
  have h_cover : ∀ e ∈ G.edgeFinset, ∃ v ∈ Aᶜ, v ∈ e := by
    intro e he
    have he_edge : e ∈ G.edgeSet := G.mem_edgeFinset.mp he
    have hindA : G.IsIndepSet (↑A : Set α) := hA.isIndepSet
    -- Since A is independent, every edge has an endpoint in Aᶜ
    revert he he_edge
    refine Sym2.ind (fun v w => ?_) e
    intro he he_edge
    simp only [SimpleGraph.mem_edgeSet] at he_edge
    by_cases hv : v ∈ A
    · by_cases hw : w ∈ A
      · exact absurd he_edge (hindA hv hw he_edge.ne)
      · exact ⟨w, Finset.mem_compl.mpr hw, Sym2.mem_mk_right v w⟩
    · exact ⟨v, Finset.mem_compl.mpr hv, Sym2.mem_mk_left v w⟩
  -- Step 2: Bound |E| via degree and independence number
  -- deg(v) ≤ α for all v, and #Aᶜ = n - α, so |E| ≤ α·(n - α) ≤ n²/4
  have hdeg : ∀ v : α, G.degree v ≤ α_val := degree_le_indepNum h
  -- The sum of degrees over all vertices = 2 * |E|
  have hsum := G.sum_degrees_eq_twice_card_edges
  -- Sum over Aᶜ ≤ #Aᶜ * α_val
  have hAc_bound : ∑ v ∈ Aᶜ, G.degree v ≤ Aᶜ.card * α_val := by
    calc ∑ v ∈ Aᶜ, G.degree v ≤ ∑ _v ∈ Aᶜ, α_val :=
          Finset.sum_le_sum (fun v _ => hdeg v)
      _ = Aᶜ.card * α_val := by simp [Finset.sum_const]
  -- |E| ≤ ∑_{v ∈ Aᶜ} deg(v) by double counting (each edge contributes at least 1 to LHS)
  have hE_le : G.edgeFinset.card ≤ ∑ v ∈ Aᶜ, G.degree v := by
    -- Every edge has at least one endpoint in Aᶜ, so E ⊆ ⋃_{v ∈ Aᶜ} incidence(v)
    have hsub : G.edgeFinset ⊆ Aᶜ.biUnion (fun v => G.incidenceFinset v) := by
      intro e he
      rw [Finset.mem_biUnion]
      obtain ⟨v, hv_mem, hv_in⟩ := h_cover e he
      exact ⟨v, hv_mem, by
        rw [SimpleGraph.mem_incidenceFinset]; exact ⟨G.mem_edgeFinset.mp he, hv_in⟩⟩
    calc G.edgeFinset.card
        ≤ (Aᶜ.biUnion (fun v => G.incidenceFinset v)).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ Aᶜ, (G.incidenceFinset v).card := Finset.card_biUnion_le
      _ = ∑ v ∈ Aᶜ, G.degree v := by
          congr 1; ext v; exact G.card_incidenceFinset_eq_degree v
  -- #Aᶜ = n - α_val
  have hAcard : A.card = α_val := G.maximumIndepSet_card_eq_indepNum A hA
  have hAc_card : Aᶜ.card = n - α_val := by
    rw [Finset.card_compl, hAcard]
  -- Combine: |E| ≤ Aᶜ.card * α_val = (n - α_val) * α_val ≤ n²/4
  have hαβ : α_val ≤ n := by
    rw [← hAcard]; exact Finset.card_le_card (Finset.subset_univ _)
  calc G.edgeFinset.card
      ≤ ∑ v ∈ Aᶜ, G.degree v := hE_le
    _ ≤ Aᶜ.card * α_val := hAc_bound
    _ = (n - α_val) * α_val := by rw [hAc_card]
    _ ≤ n ^ 2 / 4 := by
        have := nat_mul_le_sq_div4 (n - α_val) α_val
        rwa [Nat.sub_add_cancel hαβ] at this

end MantelAMGMProof

section Laguerre

/-- **Laguerre's root bound** (quadratic form): For any n ≥ 2 real numbers y₀, …, yₙ₋₁
    and any index i, the Cauchy–Schwarz inequality on the remaining n − 1 values gives
    n · yᵢ² − 2 · S · yᵢ + S² ≤ (n − 1) · Q,
    where S = ∑ yⱼ and Q = ∑ yⱼ².
    When the yⱼ are all real roots of xⁿ + aₙ₋₁ xⁿ⁻¹ + ⋯ + a₀ (so S = −aₙ₋₁ and
    (S² − Q)/2 = aₙ₋₂), solving the quadratic in yᵢ recovers Laguerre's interval
    −aₙ₋₁/n ± ((n−1)/n)√(aₙ₋₁² − 2n·aₙ₋₂/(n−1)). -/
theorem laguerre_root_bound (n : ℕ) (hn : 2 ≤ n) (y : Fin n → ℝ) (i : Fin n) :
    ↑n * (y i) ^ 2 - 2 * (∑ j, y j) * (y i) + (∑ j, y j) ^ 2 ≤
    (↑n - 1) * ∑ j, (y j) ^ 2 := by
  -- The key is Cauchy-Schwarz: (∑_{j≠i} y j)² ≤ (n-1) · ∑_{j≠i} (y j)²
  set S := Finset.univ.erase i
  have hcard : S.card = n - 1 := by simp [S, Finset.card_erase_of_mem]
  -- Rewrite sums over univ as sums over S plus the i-th term
  have hsum : ∑ j, y j = y i + ∑ j ∈ S, y j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hsumsq : ∑ j, (y j) ^ 2 = (y i) ^ 2 + ∑ j ∈ S, (y j) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- Apply Cauchy-Schwarz: (∑_{j∈S} yⱼ·1)² ≤ (∑_{j∈S} yⱼ²)(∑_{j∈S} 1²)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => y j) (fun _ => (1 : ℝ))
  simp only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at cs
  -- cs : (∑ j ∈ S, y j) ^ 2 ≤ (∑ j ∈ S, y j ^ 2) * ↑(n - 1)
  rw [hsum, hsumsq]
  have hn1 : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  rw [hn1] at cs
  nlinarith [cs, sq_nonneg (∑ j ∈ S, y j)]

/-- Auxiliary: solving a quadratic inequality `a * x² + b * x + c ≤ 0` with `a > 0`
    yields `(−b − √(b²−4ac))/(2a) ≤ x ≤ (−b + √(b²−4ac))/(2a)`. -/
private theorem quadratic_le_zero_interval (a b c x : ℝ) (ha : 0 < a)
    (hD : 0 ≤ b ^ 2 - 4 * a * c) (hle : a * x ^ 2 + b * x + c ≤ 0) :
    (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ≤ x ∧
    x ≤ (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  have ha2 : 0 < 2 * a := by linarith
  have hsq := Real.sq_sqrt hD
  set D := Real.sqrt (b ^ 2 - 4 * a * c) with hD_def
  have hD_nn : 0 ≤ D := Real.sqrt_nonneg _
  constructor
  · rw [div_le_iff₀ ha2]
    nlinarith [sq_nonneg (2 * a * x + b + D)]
  · rw [le_div_iff₀ ha2]
    nlinarith [sq_nonneg (2 * a * x + b - D)]

/-- **Laguerre's root interval**: From the quadratic-form bound, every root yᵢ satisfies
    (S − √((n−1)(nQ−S²))) / n ≤ yᵢ ≤ (S + √((n−1)(nQ−S²))) / n,
    where S = ∑ yⱼ and Q = ∑ yⱼ².

    In terms of polynomial coefficients (S = −aₙ₋₁, Q = aₙ₋₁² − 2aₙ₋₂),
    this recovers Laguerre's classical interval
    −aₙ₋₁/n ± ((n−1)/n)√(aₙ₋₁² − 2n·aₙ₋₂/(n−1)). -/
theorem laguerre_root_interval (n : ℕ) (hn : 2 ≤ n) (y : Fin n → ℝ) (i : Fin n)
    (hD : 0 ≤ (↑n - 1) * (↑n * (∑ j, (y j) ^ 2) - (∑ j, y j) ^ 2)) :
    ((∑ j, y j) - Real.sqrt ((↑n - 1) * (↑n * (∑ j, (y j) ^ 2) - (∑ j, y j) ^ 2))) / ↑n
      ≤ y i ∧
    y i ≤
    ((∑ j, y j) + Real.sqrt ((↑n - 1) * (↑n * (∑ j, (y j) ^ 2) - (∑ j, y j) ^ 2))) / ↑n := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  -- Apply the quadratic bound
  have hqf := laguerre_root_bound n hn y i
  -- Rewrite as: n * (y i)² − 2 * S * (y i) + (S² − (n−1) * Q) ≤ 0
  set S := ∑ j, y j
  set Q := ∑ j, (y j) ^ 2
  -- hqf : n * (y i)² − 2 * S * (y i) + S² ≤ (n − 1) * Q
  -- i.e. n * (y i)² + (−2 * S) * (y i) + (S² − (n − 1) * Q) ≤ 0
  have hle : ↑n * (y i) ^ 2 + (-2 * S) * (y i) + (S ^ 2 - (↑n - 1) * Q) ≤ 0 := by linarith
  -- Discriminant: (−2S)² − 4n(S² − (n−1)Q) = 4(n−1)(nQ − S²)
  have hdisc : (-2 * S) ^ 2 - 4 * ↑n * (S ^ 2 - (↑n - 1) * Q) =
      4 * ((↑n - 1) * (↑n * Q - S ^ 2)) := by ring
  have hD4 : 0 ≤ (-2 * S) ^ 2 - 4 * ↑n * (S ^ 2 - (↑n - 1) * Q) := by
    rw [hdisc]; linarith [hD]
  have h := quadratic_le_zero_interval ↑n (-2 * S) (S ^ 2 - (↑n - 1) * Q) (y i) hn_pos hD4 hle
  -- Now simplify the bounds
  -- The bounds are: (2S ∓ √(4(n−1)(nQ−S²))) / (2n)
  -- = (S ∓ √((n−1)(nQ−S²))) / n
  have hsqrt_factor : Real.sqrt ((-2 * S) ^ 2 - 4 * ↑n * (S ^ 2 - (↑n - 1) * Q)) =
      2 * Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2)) := by
    rw [hdisc]
    have : (4 : ℝ) * ((↑n - 1) * (↑n * Q - S ^ 2)) =
        (2 * Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hD]; ring
    rw [this]
    exact Real.sqrt_sq (by positivity)
  constructor
  · have h1 := h.1
    rw [hsqrt_factor] at h1
    have : (- (-2 * S) - 2 * Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2))) / (2 * ↑n) =
        (S - Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2))) / ↑n := by ring
    linarith
  · have h2 := h.2
    rw [hsqrt_factor] at h2
    have : (- (-2 * S) + 2 * Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2))) / (2 * ↑n) =
        (S + Real.sqrt ((↑n - 1) * (↑n * Q - S ^ 2))) / ↑n := by ring
    linarith

end Laguerre

/-!
## Theorem 2: Erdős–Gallai inequality  A ≥ (2/3)T

We formalize Pólya's proof that for a polynomial
  f(x) = (1 - x²) · ∏ᵢ (αᵢ - x) · ∏ⱼ (βⱼ + x),  αᵢ, βⱼ ≥ 1,
the area A = ∫₋₁¹ f(x) dx satisfies  A ≥ (2/3) T,
where T is the "tangential trapezoid"  T = -2 f'(1) f'(-1) / (f'(1) - f'(-1)).

### Structure

The proof has two layers:
1. **Algebraic layer** (fully proved): HM-GM inequality relating T to f'(±1).
2. **Integral layer** (`erdos_gallai_integral_bound`): symmetrisation and AM-GM
   give A ≥ (4/3)C.
-/

section ErdosGallai

open Finset


/-- The main inequality A ≥ (2/3) T.

    This is the full Erdős–Gallai theorem. The proof combines:
    1. Symmetrization + AM-GM to get A ≥ (4/3)C  [integral layer, `erdos_gallai_integral_bound`]
    2. C = √(-f'(1)f'(-1))/2  [algebraic, proved above]
    3. HM-GM: T ≤ √(-f'(1)f'(-1))  [algebraic]

    We state it in terms of the area A (given as a parameter, with the
    integral lower bound as a hypothesis). -/
theorem erdos_gallai_A_ge_two_thirds_T {m n : ℕ}
    (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j)
    (A : ℝ)
    -- The integral layer hypothesis: A ≥ (4/3) · C
    (hA : A ≥ 4 / 3 * Real.sqrt (erdosGallaiCSq α β))
    -- Note: The tex also assumes f'(1) ≠ f'(-1) (non-degeneracy), but the proof
    -- doesn't need it — the inequality A ≥ (2/3)T holds regardless.
    :
    A ≥ 2 / 3 * erdosGallaiT α β := by
  -- Harmonic–geometric mean inequality applied to `-f'(1)` and `f'(-1)`:
  -- `T = 2 f'(1) f'(-1) / (f'(1) - f'(-1)) ≤ √(-f'(1) f'(-1)) = 2 √C²`.
  have hT := erdos_gallai_T_le α β hα hβ
  linarith

/-- The full Erdős–Gallai theorem without the integral hypothesis.
    A ≥ (2/3) T where A is the actual integral area.
    Note: The tex assumes f'(1) ≠ f'(-1) but the inequality holds unconditionally. -/
theorem erdos_gallai_full {m n : ℕ}
    (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdosGallaiArea α β ≥ 2 / 3 * erdosGallaiT α β :=
  erdos_gallai_A_ge_two_thirds_T α β hα hβ
    (erdosGallaiArea α β) (erdos_gallai_integral_bound α β hα hβ)

end ErdosGallai

section Supplement

/-!
# Chapter 20 — complements

Statements of the chapter that are not covered in `Chapter_20.lean`:

* equality case of the Cauchy–Schwarz inequality (Theorem I);
* the extremal case of Mantel's theorem (Theorem 3): equality forces `n` even and
  `G ≅ K_{n/2,n/2}`.
-/

open Real RealInnerProductSpace Finset

section CauchySchwarzEquality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Theorem I, equality case**: `⟪a, b⟫² = |a|² |b|²` if and only if `a` and `b` are
linearly dependent (here: `a = 0` or `b` is a multiple of `a`). -/
theorem cauchy_schwarz_eq_iff (a b : V) :
    ⟪a, b⟫ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 ↔ a = 0 ∨ ∃ l : ℝ, b = l • a := by
  have key : ‖⟪a, b⟫‖ = ‖a‖ * ‖b‖ ↔ a = 0 ∨ ∃ l : ℝ, b = l • a := by
    by_cases ha : a = 0
    · subst ha; simp
    by_cases hb : b = 0
    · subst hb; simp only [inner_zero_right, norm_zero, mul_zero, true_iff]
      exact Or.inr ⟨0, (zero_smul ℝ a).symm⟩
    rw [norm_inner_eq_norm_iff ha hb]
    simp only [ha, false_or]
    exact ⟨fun ⟨r, _, h⟩ => ⟨r, h⟩, fun ⟨r, h⟩ =>
      ⟨r, fun hr => hb (by rw [h, hr, zero_smul]), h⟩⟩
  rw [← key, ← mul_pow, Real.norm_eq_abs, ← sq_abs]
  exact pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero

/-- **Theorem I, equality case** phrased with linear independence:
`⟪a, b⟫² = |a|² |b|²` if and only if `a, b` are linearly dependent. -/
theorem cauchy_schwarz_eq_iff_not_linearIndependent (a b : V) :
    ⟪a, b⟫ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 ↔ ¬ LinearIndependent ℝ ![a, b] := by
  rw [cauchy_schwarz_eq_iff]
  by_cases ha : a = 0
  · subst ha
    simp only [true_or, true_iff]
    intro hli
    exact hli.ne_zero 0 rfl
  · rw [LinearIndependent.pair_iff' ha]
    simp only [ha, false_or, not_forall, not_not]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, hl.symm⟩, fun ⟨l, hl⟩ => ⟨l, hl.symm⟩⟩

/-- **Theorem I, strict form**: if `a, b` are linearly independent then
`⟪a, b⟫² < |a|² |b|²`. -/
theorem cauchy_schwarz_strict (a b : V) (h : LinearIndependent ℝ ![a, b]) :
    ⟪a, b⟫ ^ 2 < ‖a‖ ^ 2 * ‖b‖ ^ 2 :=
  by
    classical
    exact lt_of_le_of_ne (cauchy_schwarz_inequality V a b)
      (fun heq => (cauchy_schwarz_eq_iff_not_linearIndependent a b).mp heq h)

end CauchySchwarzEquality

section MantelExtremal

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- In the extremal case of Mantel's theorem, `n` is even and the vertex set splits into two
halves `A`, `B` of size `n/2` such that two vertices are adjacent exactly when they lie in
different halves. -/
theorem mantel_eq_partition (h : G.CliqueFree 3)
    (heq : G.edgeFinset.card * 4 = Fintype.card α ^ 2) :
    Even (Fintype.card α) ∧
    ∃ A : Finset α, A.card = Fintype.card α / 2 ∧ Aᶜ.card = Fintype.card α / 2 ∧
      ∀ i j, G.Adj i j ↔ (i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A) := by
  set n := Fintype.card α
  have h2n : 2 ∣ n := by
    have h4 : 4 ∣ n ^ 2 := ⟨G.edgeFinset.card, by linarith⟩
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two (dvd_trans ⟨2, rfl⟩ h4)
  refine ⟨even_iff_two_dvd.mpr h2n, ?_⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨∅, ?_, ?_, fun i => isEmptyElim i⟩ <;> simp [n]
  have hreg := mantel_eq_regular h heq
  obtain ⟨v₀⟩ := hα
  set A := G.neighborFinset v₀ with hAdef
  have hA_card : A.card = n / 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg v₀
  have hB_card : Aᶜ.card = n / 2 := by
    rw [Finset.card_compl, hA_card]; obtain ⟨k, hk⟩ := h2n; omega
  have hindA : ∀ i ∈ A, ∀ j ∈ A, ¬ G.Adj i j := by
    intro i hi j hj hij
    have hind := G.isIndepSet_neighborSet_of_triangleFree h v₀
    rw [hAdef, SimpleGraph.mem_neighborFinset] at hi hj
    exact hind hi hj hij.ne hij
  -- every vertex outside `A` is adjacent to all of `A`, hence its neighbourhood is exactly `A`
  have hNB : ∀ j ∉ A, G.neighborFinset j = A := by
    intro j hj
    have hsub : A ⊆ G.neighborFinset j := by
      intro i hi
      rw [SimpleGraph.mem_neighborFinset]
      -- `N(i) ⊆ Aᶜ` and `|N(i)| = n/2 = |Aᶜ|`, so `N(i) = Aᶜ ∋ j`
      have hNi_sub : G.neighborFinset i ⊆ Aᶜ := by
        intro w hw
        rw [Finset.mem_compl]
        intro hwA
        exact hindA i hi w hwA ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)
      have hNi : G.neighborFinset i = Aᶜ :=
        Finset.eq_of_subset_of_card_le hNi_sub (by
          rw [SimpleGraph.card_neighborFinset_eq_degree, hreg i, hB_card])
      have : j ∈ G.neighborFinset i := by rw [hNi]; exact Finset.mem_compl.mpr hj
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
    exact (Finset.eq_of_subset_of_card_le hsub (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hreg j, hA_card])).symm
  refine ⟨A, hA_card, hB_card, fun i j => ?_⟩
  constructor
  · intro hij
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · exact absurd hij (hindA i hi j hj)
      · exact Or.inl ⟨hi, hj⟩
    · have : j ∈ G.neighborFinset i := (SimpleGraph.mem_neighborFinset _ _ _).mpr hij
      rw [hNB i hi] at this
      exact Or.inr ⟨hi, this⟩
  · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · have : i ∈ G.neighborFinset j := by rw [hNB j hj]; exact hi
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
    · have : j ∈ G.neighborFinset i := by rw [hNB i hi]; exact hj
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp this

/-- **Theorem 3, extremal case**: a triangle-free graph on `n` vertices with exactly `n²/4`
edges has `n` even and is isomorphic to the complete bipartite graph `K_{n/2,n/2}`. -/
theorem mantel_eq_iso_completeBipartite (h : G.CliqueFree 3)
    (heq : G.edgeFinset.card * 4 = Fintype.card α ^ 2) :
    Even (Fintype.card α) ∧
    Nonempty (G ≃g completeBipartiteGraph (Fin (Fintype.card α / 2))
      (Fin (Fintype.card α / 2))) := by
  obtain ⟨heven, A, hA, hB, hadj⟩ := mantel_eq_partition h heq
  refine ⟨heven, ?_⟩
  have eA : {x // x ∈ A} ≃ Fin (Fintype.card α / 2) :=
    Fintype.equivFinOfCardEq (by simpa using hA)
  have eB : {x // x ∉ A} ≃ Fin (Fintype.card α / 2) :=
    Fintype.equivFinOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
      rw [Finset.card_compl] at hB; exact hB)
  let e : α ≃ Fin (Fintype.card α / 2) ⊕ Fin (Fintype.card α / 2) :=
    (Equiv.sumCompl (fun x => x ∈ A)).symm.trans (Equiv.sumCongr eA eB)
  have hleft : ∀ x, (e x).isLeft ↔ x ∈ A := by
    intro x
    by_cases hx : x ∈ A
    · simp [e, Equiv.sumCompl, hx]
    · simp [e, Equiv.sumCompl, hx]
  refine ⟨⟨e, fun {a b} => ?_⟩⟩
  simp only [completeBipartiteGraph_adj]
  rw [hadj a b, ← Sum.not_isLeft, ← Sum.not_isLeft, hleft a, hleft b]

end MantelExtremal

end Supplement

section ErdosGallaiPolynomial

/-!
# Theorem 2 (left inequality) for arbitrary real-rooted polynomials

Let `p` be a real polynomial with only real roots such that `p(x) > 0` for `-1 < x < 1` and
`p(-1) = p(1) = 0`.  Then `(2/3) T ≤ A`, where `A = ∫₋₁¹ p` and
`T = 2 p'(1) p'(-1) / (p'(1) - p'(-1))` is the area of the tangential triangle;
equality holds only for `deg p = 2`.

The proof reduces to the normal form (3) of the chapter,
`p(x) = K · (1 - x²) ∏ᵢ (αᵢ - x) ∏ⱼ (βⱼ + x)` with `K > 0`, `αᵢ, βⱼ ≥ 1`,
and then applies the normal-form estimates proved earlier in this file.
-/

open Polynomial Finset

/-- Area of the tangential triangle of `p` over `[-1, 1]`:
`T = 2 p'(1) p'(-1) / (p'(1) - p'(-1))` (and `T = 0` if `p'(1) = p'(-1)`). -/
noncomputable def tangentialTriangleArea (p : ℝ[X]) : ℝ :=
  2 * (derivative p).eval 1 * (derivative p).eval (-1) /
    ((derivative p).eval 1 - (derivative p).eval (-1))

private lemma prod_fin_toList (s : Multiset ℝ) (f : ℝ → ℝ) :
    ∏ i : Fin s.toList.length, f s.toList[i.1] = (s.map f).prod := by
  rw [Fin.prod_univ_fun_getElem, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

/-- **Normal form (3)**: a real-rooted polynomial which is positive on `(-1, 1)` and vanishes
at `±1` is a positive multiple of `(1 - x²) ∏ᵢ (αᵢ - x) ∏ⱼ (βⱼ + x)` with `αᵢ, βⱼ ≥ 1`. -/
theorem erdos_gallai_normal_form (p : ℝ[X]) (hsplit : p.Splits)
    (h1 : p.eval 1 = 0) (hm1 : p.eval (-1) = 0)
    (hpos : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < p.eval x) :
    ∃ (K : ℝ) (m n : ℕ) (α : Fin m → ℝ) (β : Fin n → ℝ), 0 < K ∧ (∀ i, 1 ≤ α i) ∧
      (∀ j, 1 ≤ β j) ∧ (∀ x, p.eval x = K * erdosGallaiF α β x) ∧
      p.natDegree = m + n + 2 := by
  have hp0 : p ≠ 0 := by
    intro h; have := hpos 0 (by norm_num); simp [h] at this
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hsplit
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have heval : ∀ x, p.eval x = p.leadingCoeff * (p.roots.map (fun r => x - r)).prod := by
    intro x
    conv_lhs => rw [← hprod]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro r _; simp
  -- `1` and `-1` are roots
  have hr1 : (1 : ℝ) ∈ p.roots := (mem_roots hp0).mpr h1
  obtain ⟨s1, hs1⟩ := Multiset.exists_cons_of_mem hr1
  have hrm1 : (-1 : ℝ) ∈ s1 := by
    have : (-1 : ℝ) ∈ p.roots := (mem_roots hp0).mpr hm1
    rw [hs1, Multiset.mem_cons] at this
    rcases this with h | h
    · norm_num at h
    · exact h
  obtain ⟨s2, hs2⟩ := Multiset.exists_cons_of_mem hrm1
  -- the remaining roots lie outside `(-1, 1)`
  have hout : ∀ r ∈ s2, r ≤ -1 ∨ 1 ≤ r := by
    intro r hr
    have hroot : p.eval r = 0 := by
      have : r ∈ p.roots := by rw [hs1, hs2]; simp [hr]
      exact (mem_roots hp0).mp this
    by_contra hc
    push Not at hc
    have := hpos r ⟨hc.1, hc.2⟩
    linarith
  set sa := s2.filter (fun r => 1 ≤ r) with hsa
  set sb := s2.filter (fun r => ¬ 1 ≤ r) with hsb
  have hsplit2 : sa + sb = s2 := Multiset.filter_add_not _ _
  set la := sa.toList
  set lb := (sb.map Neg.neg).toList
  let α : Fin la.length → ℝ := fun i => la[i.1]
  let β : Fin lb.length → ℝ := fun j => lb[j.1]
  have hα : ∀ i, 1 ≤ α i := by
    intro i
    have hmem : la[i.1] ∈ sa := by
      rw [← Multiset.mem_toList]; exact List.getElem_mem _
    exact (Multiset.mem_filter.mp hmem).2
  have hβ : ∀ j, 1 ≤ β j := by
    intro j
    have hmem : lb[j.1] ∈ sb.map Neg.neg := by
      rw [← Multiset.mem_toList]; exact List.getElem_mem _
    obtain ⟨r, hr, hreq⟩ := Multiset.mem_map.mp hmem
    have hr' := Multiset.mem_filter.mp hr
    rcases hout r hr'.1 with h | h
    · show 1 ≤ lb[j.1]; rw [← hreq]; linarith
    · exact absurd h hr'.2
  have hprodα : ∀ x, ∏ i, (α i - x) = (sa.map (fun r => r - x)).prod := fun x =>
    prod_fin_toList sa (fun r => r - x)
  have hprodβ : ∀ x, ∏ j, (β j + x) = (sb.map (fun r => x - r)).prod := by
    intro x
    rw [prod_fin_toList (sb.map Neg.neg) (fun r => r + x), Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _; simp; ring
  set K := p.leadingCoeff * (-1) * (-1) ^ sa.card with hK
  have hrepr : ∀ x, p.eval x = K * erdosGallaiF α β x := by
    intro x
    rw [heval x, hs1, hs2, ← hsplit2]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add, Multiset.prod_add]
    unfold erdosGallaiF
    rw [hprodα, hprodβ]
    have hneg : (sa.map (fun r => x - r)).prod = (-1) ^ sa.card * (sa.map (fun r => r - x)).prod :=
      by
      have : sa.map (fun r => x - r) = (sa.map (fun r => r - x)).map Neg.neg := by
        rw [Multiset.map_map]; apply Multiset.map_congr rfl; intro r _; simp
      rw [this, Multiset.prod_map_neg, Multiset.card_map]
    rw [hneg, hK]
    ring
  have hf0 : 0 < erdosGallaiF α β 0 := by
    unfold erdosGallaiF
    have ha0 : 0 < ∏ i, (α i - 0) := prod_pos fun i _ => by linarith [hα i]
    have hb0 : 0 < ∏ j, (β j + 0) := prod_pos fun j _ => by linarith [hβ j]
    exact mul_pos (mul_pos (by norm_num) ha0) hb0
  have hKpos : 0 < K := by
    have h0 := hpos 0 (by norm_num)
    rw [hrepr 0] at h0
    exact pos_of_mul_pos_left h0 hf0.le
  refine ⟨K, la.length, lb.length, α, β, hKpos, hα, hβ, hrepr, ?_⟩
  rw [← hcard, hs1, hs2, ← hsplit2]
  simp [la, lb]

private lemma tangential_scale {K a b : ℝ} (hK : K ≠ 0) :
    2 * (K * a) * (K * b) / (K * a - K * b) = K * (2 * a * b / (a - b)) := by
  by_cases hab : a - b = 0
  · have : a = b := by linarith
    subst this; simp
  · have : K * a - K * b ≠ 0 := by rw [← mul_sub]; exact mul_ne_zero hK hab
    field_simp

/-- Transfer of `A`, `T` from a polynomial to its normal form. -/
private lemma area_T_of_repr (p : ℝ[X]) {K : ℝ} {m n : ℕ} {α : Fin m → ℝ} {β : Fin n → ℝ}
    (hK : 0 < K) (hrepr : ∀ x, p.eval x = K * erdosGallaiF α β x) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = K * erdosGallaiArea α β ∧
      tangentialTriangleArea p = K * erdosGallaiT α β := by
  have hfun : (fun x => p.eval x) = fun x => K * erdosGallaiF α β x := funext hrepr
  constructor
  · rw [hfun, intervalIntegral.integral_const_mul]; rfl
  · have hd : ∀ y, (derivative p).eval y = deriv (fun x => K * erdosGallaiF α β x) y := by
      intro y; rw [← hfun, Polynomial.deriv]
    have hd1 : (derivative p).eval 1 = K * erdosGallaiDerivAtOne α β := by
      rw [hd]; exact ((erdos_gallai_hasDerivAt_one α β).const_mul K).deriv
    have hdm1 : (derivative p).eval (-1) = K * erdosGallaiDerivAtNegOne α β := by
      rw [hd]; exact ((erdos_gallai_hasDerivAt_neg_one α β).const_mul K).deriv
    unfold tangentialTriangleArea erdosGallaiT
    rw [hd1, hdm1, tangential_scale hK.ne']

/-- **Theorem 2, left inequality** (Pólya's proof): for a real polynomial `p` with only real
roots, `p(x) > 0` on `(-1, 1)` and `p(-1) = p(1) = 0`, we have `(2/3) T ≤ A`. -/
theorem erdos_gallai_polynomial (p : ℝ[X]) (hsplit : p.Splits)
    (h1 : p.eval 1 = 0) (hm1 : p.eval (-1) = 0)
    (hpos : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < p.eval x) :
    2 / 3 * tangentialTriangleArea p ≤ ∫ x in (-1 : ℝ)..1, p.eval x := by
  obtain ⟨K, m, n, α, β, hK, hα, hβ, hrepr, -⟩ := erdos_gallai_normal_form p hsplit h1 hm1 hpos
  obtain ⟨hA, hT⟩ := area_T_of_repr p hK hrepr
  rw [hA, hT]
  have h := erdos_gallai_integral_bound α β hα hβ
  have h' := erdos_gallai_T_le α β hα hβ
  nlinarith

/-- **Theorem 2, equality case of the left inequality**: under the hypotheses of
`erdos_gallai_polynomial`, `A = (2/3) T` holds if and only if `p` has degree `2`. -/
theorem erdos_gallai_polynomial_eq_iff (p : ℝ[X]) (hsplit : p.Splits)
    (h1 : p.eval 1 = 0) (hm1 : p.eval (-1) = 0)
    (hpos : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < p.eval x) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = 2 / 3 * tangentialTriangleArea p ↔ p.natDegree = 2 := by
  obtain ⟨K, m, n, α, β, hK, hα, hβ, hrepr, hdeg⟩ :=
    erdos_gallai_normal_form p hsplit h1 hm1 hpos
  obtain ⟨hA, hT⟩ := area_T_of_repr p hK hrepr
  rw [hA, hT, hdeg]
  have key := erdos_gallai_eq_iff α β hα hβ
  constructor
  · intro h
    have : erdosGallaiArea α β = 2 / 3 * erdosGallaiT α β := by
      have h' : K * erdosGallaiArea α β = K * (2 / 3 * erdosGallaiT α β) := by
        rw [h]; ring
      exact mul_left_cancel₀ hK.ne' h'
    obtain ⟨rfl, rfl⟩ := key.mp this
    rfl
  · intro h
    have hmn : m = 0 ∧ n = 0 := by omega
    rw [key.mpr hmn]; ring

end ErdosGallaiPolynomial

section LaguerrePolynomial

/-!
### Theorem 1 in terms of the coefficients

If all roots of the monic polynomial `xⁿ + aₙ₋₁ xⁿ⁻¹ + ⋯ + a₀` (`n ≥ 2`) are real, then every
root lies in the interval with endpoints
`-aₙ₋₁/n ± ((n-1)/n) √(aₙ₋₁² - 2n/(n-1) · aₙ₋₂)`.
-/

open Polynomial

private lemma multiset_esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

private lemma multiset_esymm_two_cons (a : ℝ) (s : Multiset ℝ) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one, Multiset.map_map]
  simpa using (Multiset.sum_map_mul_left (s := s) (a := a) (f := id))

/-- `(∑ yᵢ)² = ∑ yᵢ² + 2 ∑_{i<j} yᵢ yⱼ`. -/
private lemma multiset_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 = (s.map (· ^ 2)).sum + 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty =>
    have h0 : (0 : Multiset ℝ).esymm 2 = 0 := rfl
    rw [h0]; simp
  | cons a s ih =>
    rw [multiset_esymm_two_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    nlinarith [ih]

/-- **Theorem 1 (Laguerre)**: if the monic polynomial `p = xⁿ + aₙ₋₁ xⁿ⁻¹ + ⋯ + a₀`, `n ≥ 2`,
has only real roots, then each root `y` satisfies
`-aₙ₋₁/n - ((n-1)/n) √(aₙ₋₁² - 2n/(n-1) aₙ₋₂) ≤ y` and
`y ≤ -aₙ₋₁/n + ((n-1)/n) √(aₙ₋₁² - 2n/(n-1) aₙ₋₂)`. -/
theorem laguerre_polynomial (p : ℝ[X]) (hmonic : p.Monic) (hn : 2 ≤ p.natDegree)
    (hsplit : p.Splits) (y : ℝ) (hy : p.IsRoot y) :
    -p.coeff (p.natDegree - 1) / p.natDegree - (p.natDegree - 1) / p.natDegree *
        Real.sqrt (p.coeff (p.natDegree - 1) ^ 2 -
          2 * p.natDegree / (p.natDegree - 1) * p.coeff (p.natDegree - 2)) ≤ y ∧
    y ≤ -p.coeff (p.natDegree - 1) / p.natDegree + (p.natDegree - 1) / p.natDegree *
        Real.sqrt (p.coeff (p.natDegree - 1) ^ 2 -
          2 * p.natDegree / (p.natDegree - 1) * p.coeff (p.natDegree - 2)) := by
  set n := p.natDegree with hn_def
  have hcard : p.roots.card = n := splits_iff_card_roots.mp hsplit
  set s := p.roots
  have hp0 : p ≠ 0 := hmonic.ne_zero
  -- Vieta
  have ha : p.coeff (n - 1) = -s.sum := by
    rw [coeff_eq_esymm_roots_of_card hcard (by omega), hmonic.leadingCoeff,
      show n - (n - 1) = 1 by omega, multiset_esymm_one]; ring
  have hb : p.coeff (n - 2) = s.esymm 2 := by
    rw [coeff_eq_esymm_roots_of_card hcard (by omega), hmonic.leadingCoeff,
      show n - (n - 2) = 2 by omega]; ring
  set l := s.toList with hl
  have hlen : l.length = n := by rw [hl, Multiset.length_toList, hcard]
  have hyl : y ∈ l := by rw [hl, Multiset.mem_toList]; exact (mem_roots hp0).mpr hy
  obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hyl
  have hS : ∑ j : Fin l.length, l[j.1] = s.sum := by
    rw [Fin.sum_univ_getElem, hl, Multiset.sum_toList]
  have hQ : ∑ j : Fin l.length, l[j.1] ^ 2 = (s.map (· ^ 2)).sum := by
    rw [Fin.sum_univ_fun_getElem (f := fun x : ℝ => x ^ 2), ← Multiset.sum_coe,
      ← Multiset.map_coe, hl, Multiset.coe_toList]
  have hn2 : 2 ≤ l.length := by omega
  -- the Cauchy–Schwarz discriminant is nonnegative
  have hCS : (∑ j : Fin l.length, l[j.1]) ^ 2 ≤ l.length * ∑ j : Fin l.length, l[j.1] ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin l.length => l[j.1])
      (fun _ => (1 : ℝ))
    simpa [mul_comm] using this
  have hnR : (2 : ℝ) ≤ l.length := by exact_mod_cast hn2
  have hD : 0 ≤ ((l.length : ℝ) - 1) * (l.length * (∑ j : Fin l.length, l[j.1] ^ 2) -
      (∑ j : Fin l.length, l[j.1]) ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hint := laguerre_root_interval l.length hn2 (fun j => l[j.1]) ⟨i, hi⟩ hD
  have hD' := hD
  rw [hS, hQ, hlen] at hD'
  simp only [hiy] at hint
  rw [hS, hQ] at hint
  rw [hlen] at hint
  -- rewrite the bounds in terms of the coefficients
  rw [ha, hb]
  have hsq := multiset_sum_sq s
  set S := s.sum
  set Q := (s.map (· ^ 2)).sum
  have hnR' : (2 : ℝ) ≤ n := by rw [← hlen]; exact hnR
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hX : ((n : ℝ) - 1) * (n * Q - S ^ 2) =
      ((n : ℝ) - 1) ^ 2 * ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2) := by
    field_simp
    nlinarith [hsq]
  have hXnn : 0 ≤ (-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2 := by
    have h0 : 0 ≤ ((n : ℝ) - 1) * (n * Q - S ^ 2) := hD'
    rw [hX] at h0
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0
  have hsqrt : Real.sqrt (((n : ℝ) - 1) * (n * Q - S ^ 2)) =
      ((n : ℝ) - 1) * Real.sqrt ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2) := by
    rw [hX, Real.sqrt_mul (by positivity), Real.sqrt_sq hn1.le]
  rw [hsqrt] at hint
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨h1, h2⟩ := hint
  constructor
  · calc -(-S) / n - (n - 1) / n * Real.sqrt ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2)
        = (S - (n - 1) * Real.sqrt ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2)) / n := by
          field_simp
      _ ≤ y := h1
  · calc y ≤ (S + (n - 1) * Real.sqrt ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2)) / n := h2
      _ = -(-S) / n + (n - 1) / n * Real.sqrt ((-S) ^ 2 - 2 * n / (n - 1) * s.esymm 2) := by
          field_simp

end LaguerrePolynomial
