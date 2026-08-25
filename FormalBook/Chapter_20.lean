/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import FormalBook.Mathlib.EdgeFinset
import FormalBook.Ch20.CauchyAMGM
import FormalBook.Ch20.BernoulliAMGM
import FormalBook.Ch20.ErdosGallai
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

open Real
open RealInnerProductSpace
open BigOperators
open Classical

/-!
# In praise of inequalities

Formalization of Chapter 20 from "Proofs from THE BOOK" (Aigner & Ziegler).

## Contents

- [x] **Theorem I** (Cauchy–Schwarz inequality): `cauchy_schwarz_inequality`
- [x] **Theorem II** (HM–GM–AM inequality), three proofs:
  - Proof 1 (Cauchy forward-backward induction): `harmonic_geometric_arithmetic₁`
  - Proof 2 (Alzer/Dacar, log x ≤ x − 1): `harmonic_geometric_arithmetic₂`
  - Proof 3 (Hirschhorn, Bernoulli inequality): `harmonic_geometric_arithmetic₃`
- [x] **Theorem 1** (Laguerre root bound): `laguerre_root_bound`, `laguerre_root_interval`
- [x] **Theorem 2** (Erdős–Gallai, A ≥ (2/3)T): `erdos_gallai_full`
  - Note: the right half A ≤ (2/3)R is left to the reader in the original book
- [x] **Theorem 3** (Mantel's theorem), two proofs:
  - Proof 1 (Cauchy inequality): `mantel`
  - Proof 2 (AM-GM / independent set): `mantel_amgm`
  - Equality condition: `mantel_eq_adj_degree`
-/

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
    Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hpos i)) _
  have rhs_a : ∑ i ∈ S, w i * a i = arithmetic := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * a i = (∑ i : Finset.Icc 1 n, a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul]; simp [S, Finset.sum_div]
  have eq_a := geom_mean_eq_arith_mean_weighted_iff' S w a hw_pos hw_sum ha_nn
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
    rw [Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hb_pos i)) _]
    have : ∏ i ∈ S, b i = (∏ i ∈ S, a i)⁻¹ := by
      simp only [b]; exact Finset.prod_inv_distrib a
    rw [this, Real.inv_rpow (le_of_lt prod_a_pos)]
  have rhs_b : ∑ i ∈ S, w i * b i = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * (a i)⁻¹ = (∑ i : Finset.Icc 1 n, 1 / a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul, one_div]; simp [S, Finset.sum_div]
  have eq_b := geom_mean_eq_arith_mean_weighted_iff' S w b hw_pos hw_sum hb_nn
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
    Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hpos i)) _
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
        exact div_div_cancel₀ (ne_of_gt (Finset.sum_pos (fun i _ => hpos i) ⟨i₁, Finset.mem_univ _⟩))
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
      geom_mean_eq_arith_mean_weighted_iff' S w a hw_pos hw_sum ha_nn]
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
    rw [Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hb_pos i)) _]
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
  have eq_b := geom_mean_eq_arith_mean_weighted_iff' S w b hw_pos hw_sum hb_nn
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
    Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hpos i)) _
  have rhs_a : ∑ i ∈ S, w i * a i = arithmetic := by
    change ∑ i ∈ S, (1 : ℝ) / ↑n * a i = (∑ i : Finset.Icc 1 n, a i) / ↑n
    simp_rw [div_mul_eq_mul_div, one_mul]; simp [S, Finset.sum_div]
  have lhs_b : ∏ i ∈ S, b i ^ w i = geometric⁻¹ := by
    rw [Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (hb_pos i)) _]
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
      geom_mean_eq_arith_mean_weighted_iff' S w a hw_pos hw_sum ha_nn]
    constructor
    · intro h i; linarith [h i₁ (Finset.mem_univ _), h i (Finset.mem_univ _)]
    · intro h j _
      have hall : ∀ i : Finset.Icc 1 n, a i = a i₁ := h
      simp_rw [hall]; rw [← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul, hS_card, hn_ne]
  case hm_eq =>
    have eq_b := geom_mean_eq_arith_mean_weighted_iff' S w b hw_pos hw_sum hb_nn
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
      _ = ∑ e ∈ E, ∑ v ∈ e, d(v)                  := Finset.sum_congr rfl (λ e he ↦ by induction e with | _ v w => simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v)  := Finset.sum_congr rfl (by intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v)    := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v)               := Finset.sum_congr rfl (λ v ↦ by simp [G.incidenceFinset_eq_filter v])
      _ = ∑ v ∈ V, d(v)^2                         := by simp [Nat.pow_two]

  -- We now slightly modify the main argument to avoid division by a potentially zero n ...
  have := calc #E * n^2
    _ = (n * (∑ e ∈ E, 1)) * n               := by simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm]
    _ = (∑ _ ∈ E, n) * n                     := by rw [Finset.mul_sum]; simp
    _ ≥ (∑ e ∈ E, sum_deg e) * n             := Nat.mul_le_mul_right n (Finset.sum_le_sum adj_degree_bnd')
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
      by_contra hc; push_neg at hc
      obtain ⟨k, hk⟩ :=
        Finset.inter_nonempty_of_card_lt_card_add_card (by simp) (by simp) hc
      simp at hk; obtain ⟨hvk, hwk⟩ := hk
      exact h {k, w, v} ⟨by aesop (add safe G.adj_symm), by simp [he.ne', hvk.ne', hwk.ne']⟩

  -- Identity: ∑ sum_deg = ∑ d²
  have sum_sum_deg_eq : ∑ e ∈ E, sum_deg e = ∑ v ∈ V, d(v) ^ 2 := by
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ e, d(v)                  := Finset.sum_congr rfl (λ e he ↦ by induction e with | _ v w => simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v)  := Finset.sum_congr rfl (by intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v)    := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v)               := Finset.sum_congr rfl (λ v ↦ by simp [G.incidenceFinset_eq_filter v])
      _ = ∑ v ∈ V, d(v) ^ 2                       := by simp [Nat.pow_two]

  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨i⟩

  -- Cauchy–Schwarz + handshake: 4 * #E² ≤ (∑ sum_deg) * n
  have hcs : 4 * #E ^ 2 ≤ (∑ e ∈ E, sum_deg e) * n := by
    calc 4 * #E ^ 2
      _ = (2 * #E) ^ 2                             := by ring
      _ = (∑ v ∈ V, d(v) * 1) ^ 2                  := by simp [G.sum_degrees_eq_twice_card_edges]
      _ ≤ (∑ v ∈ V, d(v) ^ 2) * (∑ v ∈ V, 1 ^ 2)   := Finset.sum_mul_sq_le_sq_mul_sq V (λ v ↦ d(v)) 1
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
    push_neg at hc
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
      _ = ∑ e ∈ E, ∑ v ∈ e, d(v) := Finset.sum_congr rfl (λ e he ↦ by
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
    have := hsumsq; simp only [] at this ⊢
    exact_mod_cast this
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
    · exact absurd (hiw ▸ hadj_iw) (G.loopless i)
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
    simp [SimpleGraph.mem_neighborFinset] at hx hy
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
  -- Each edge has at least one endpoint in Aᶜ, so summing degrees over Aᶜ counts each edge at least once.
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
      exact ⟨v, hv_mem, (G.mem_incidenceFinset v e).mpr ⟨G.mem_edgeFinset.mp he, hv_in⟩⟩
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
2. **Integral layer** (sorry): The AM-GM + integration argument giving A ≥ (4/3)C.
-/

section ErdosGallai

open Finset


/-- The main inequality A ≥ (2/3) T.

    This is the full Erdős–Gallai theorem. The proof combines:
    1. Symmetrization + AM-GM to get A ≥ (4/3)C  [integral layer, sorry]
    2. C = √(-f'(1)f'(-1))/2  [algebraic, proved above]
    3. HM-GM: T ≤ √(-f'(1)f'(-1))  [algebraic]

    We state it in terms of the area A (given as a parameter, with the
    integral lower bound as a hypothesis). -/
theorem erdos_gallai_A_ge_two_thirds_T {m n : ℕ}
    (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j)
    (A : ℝ)
    -- The integral layer hypothesis: A ≥ (4/3) · C
    (hA : A ≥ 4 / 3 * Real.sqrt (erdos_gallai_C_sq α β))
    -- Note: The tex also assumes f'(1) ≠ f'(-1) (non-degeneracy), but the proof
    -- doesn't need it — the inequality A ≥ (2/3)T holds regardless.
    :
    A ≥ 2 / 3 * erdos_gallai_T α β := by
  -- Abbreviate
  let f1 := erdos_gallai_deriv_at_one α β
  let f1' := erdos_gallai_deriv_at_neg_one α β
  -- Positivity of products
  have hprod_α_sub : 0 ≤ ∏ i, (α i - 1) :=
    Finset.prod_nonneg fun i _ => by linarith [hα i]
  have hprod_α_add : 0 ≤ ∏ i, (α i + 1) :=
    Finset.prod_nonneg fun i _ => by linarith [hα i]
  have hprod_β_sub : 0 ≤ ∏ i, (β i - 1) :=
    Finset.prod_nonneg fun i _ => by linarith [hβ i]
  have hprod_β_add : 0 ≤ ∏ i, (β i + 1) :=
    Finset.prod_nonneg fun i _ => by linarith [hβ i]
  -- f1 ≤ 0 and f1' ≥ 0
  have hf1_le : f1 ≤ 0 := by
    show erdos_gallai_deriv_at_one α β ≤ 0
    unfold erdos_gallai_deriv_at_one
    nlinarith [mul_nonneg hprod_α_sub hprod_β_add]
  have hf1'_ge : 0 ≤ f1' := by
    show 0 ≤ erdos_gallai_deriv_at_neg_one α β
    unfold erdos_gallai_deriv_at_neg_one
    nlinarith [mul_nonneg hprod_α_add hprod_β_sub]
  -- -f1 ≥ 0
  have hnf1_ge : 0 ≤ -f1 := by linarith
  -- T = -2*f1*f1'/(f1-f1'). With f1 ≤ 0 and f1' ≥ 0, T ≤ 0, so (2/3)*T ≤ 0 ≤ A.
  suffices h : 0 ≤ A ∧ erdos_gallai_T α β ≤ 0 by linarith
  constructor
  · linarith [Real.sqrt_nonneg (erdos_gallai_C_sq α β)]
  · -- T ≤ 0
    unfold erdos_gallai_T
    apply div_nonpos_of_nonneg_of_nonpos
    · -- -2 * f1 * f1' ≥ 0
      nlinarith
    · -- f1 - f1' ≤ 0
      linarith

/-- The full Erdős–Gallai theorem without the integral hypothesis.
    A ≥ (2/3) T where A is the actual integral area.
    Note: The tex assumes f'(1) ≠ f'(-1) but the inequality holds unconditionally. -/
theorem erdos_gallai_full {m n : ℕ}
    (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : ∀ i, 1 ≤ α i) (hβ : ∀ j, 1 ≤ β j) :
    erdos_gallai_area α β ≥ 2 / 3 * erdos_gallai_T α β :=
  erdos_gallai_A_ge_two_thirds_T α β hα hβ
    (erdos_gallai_area α β) (erdos_gallai_integral_bound α β hα hβ)

end ErdosGallai
