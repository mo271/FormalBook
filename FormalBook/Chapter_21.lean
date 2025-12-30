/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Julien Michel
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Topology.Algebra.Polynomial

/-!
# The fundamental theorem of algebra
D'Alembert and Argand's proof
-/

open Complex Polynomial Filter Finset Finsupp ComplexConjugate

theorem dalembert_lemma {p : Polynomial ℂ} (hp : p.natDegree > 0)
    {a : ℂ} (hpa : p.eval a ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ b, ‖b - a‖ < R ∧ ‖p.eval b‖ < ‖p.eval a‖ := by
  wlog h1 : a = 0 ∧ p.eval a = 1
  · let q := C (p.eval a)⁻¹ * p.comp (X + C a)
    have hq0 : q.eval 0 = 1 := by simp [q, hpa]
    have hq0ne0 : q.eval 0 ≠ 0 := by simp [hq0]
    have hdegq : q.natDegree > 0 := by
      unfold q
      rw [natDegree_mul', natDegree_comp]
      · simpa using hp
      · contrapose! hq0
        simp [hpa, comp_eq_zero_iff] at hq0
        simp [q, hq0]
    specialize this hdegq hq0ne0 hR ⟨rfl, hq0⟩
    obtain ⟨b, hb1, hb2⟩ := this
    use b + a, by simpa using hb1
    simp [q, hpa] at hb2
    field_simp at hb2
    simpa using hb2
  obtain ⟨ha, hpa2⟩ := h1
  subst ha
  suffices ∃ b, ‖b‖ < R ∧ ‖p.eval b‖ < 1 by simpa [hpa2] using this
  have hpne0 : p ≠ 0 := by
    contrapose! hpa
    simp [hpa]
  let c := p.coeff
  let n := p.natDegree
  have hcnne0 : c n ≠ 0 := by simp [c, n, hpne0]
  let s := {k ∈ Icc 1 n | c k ≠ 0}
  have h1 : s.Nonempty := by
    use n
    simp only [s, mem_filter, mem_Icc]
    split_ands
    · simpa using hp
    · simp
    · exact hcnne0
  let m := s.min' h1
  have hm1 : ∀ x ∈ s, m ≤ _ := s.min'_le
  have hm2 : m ∈ s := s.min'_mem h1
  simp [s] at hm1 hm2
  let r := ofFinsupp (indicator (Icc (m + 1) n) (fun k _ => c k))
  have h2 : p = C 1 + C (c m) * X ^ m + r := by
    symm
    calc
    _ = C 1 + 0 + C (c m) * X ^ m + r := by simp
    _ =
      (ofFinsupp (indicator {0} (fun k _ => p.coeff k))) +
      (ofFinsupp (indicator (Ico 1 m) (fun k _ => p.coeff k))) +
      (ofFinsupp (indicator {m} (fun k _ => p.coeff k))) +
      (ofFinsupp (indicator (Icc (m + 1) n) (fun k _ => p.coeff k))) := by
      congr 3
      · ext k; simp [coeff_one]; grind only [coeff_zero_eq_eval_zero]
      · ext k; simp; grind
      · ext k; simp [c]; grind
    _ = (ofFinsupp (indicator (Icc 0 n) (fun k _ => p.coeff k))) := by ext k; simp; grind
    _ = p := by
      ext k
      symm
      simpa using coeff_eq_zero_of_natDegree_lt
  obtain ⟨ρ, hρ1, hρ2, hρ3, h3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ < R ∧ ∀ z : ℂ, ‖z‖ > 0 → ‖z‖ ≤ ρ →
    ‖r.eval z‖ < ‖c m * z ^ m‖ ∧ ‖c m * z ^ m‖ < 1 := by
    let ρ2 := ‖c m‖ ^ (-(1 : ℝ) / m)
    have hρ2_pos : 0 < ρ2 := by
      apply Real.rpow_pos_of_pos
      simp [hm2]
    by_cases hmn : m = n
    · use (1 ⊓ ρ2 ⊓ R) / 2
      split_ands
      · simp [hρ2_pos, hR]
      · field_simp
        simp
      · field_simp
        simp [hR]
      · intro z hz1 hz2
        field_simp at hz2
        simp at hz2
        rw [hmn]
        split_ands
        · suffices r = 0 by simp [this, hz1, hcnne0]
          ext k
          simp [r]
          omega
        · have hn : (n : ℝ) ≠ 0 := by simp [n]; omega
          calc
            _ = ‖c n‖ * ‖z‖ ^ n := by simp
            _ = ‖c n‖ * (‖z‖ * 2 / 2) ^ n := by simp
            _ < ‖c n‖ * (‖z‖ * 2) ^ n := by gcongr 2; linarith only [hz1]
            _ ≤ ‖c n‖ * ρ2 ^ n := by gcongr 2; linarith only [hz2]
            _ = ‖c n‖ * (‖c n‖ ^ (-(1 : ℝ) / n)) ^ n := by simp [ρ2, hmn]
            _ = ‖c n‖ * (‖c n‖ ^ ((-(1 : ℝ) / n) * n)) := by simp [Real.rpow_mul_natCast]
            _ = ‖c n‖ * (‖c n‖ ^ (-1 : ℝ)) := by simp [hn]
            _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀]; simp [hcnne0]
    have hsum_pos : 0 < ∑ k ∈ Icc (m + 1) n, ‖c k‖ := by
      rw [sum_pos_iff_of_nonneg]
      · use n, by simp; omega, by simp [hcnne0]
      · simp
    let ρ1 := ‖c m‖ / ∑ k ∈ Icc (m + 1) n, ‖c k‖
    have hρ1_pos : 0 < ρ1 := by
      apply div_pos
      · simp [hm2]
      · exact hsum_pos
    use (1 ⊓ ρ1 ⊓ ρ2 ⊓ R) / 2
    split_ands
    · simp [hρ1_pos, hρ2_pos, hR]
    · field_simp
      simp
    · field_simp
      simp [hR]
    · intro z hz1 hz2
      field_simp at hz2
      simp at hz2
      split_ands
      · calc
          _ = ‖(∑ k ∈ Icc (m + 1) n, C (c k) * X ^ k).eval z‖ := by congr 2; ext i; simp [r]
          _ = ‖∑ k ∈ Icc (m + 1) n, c k * z ^ k‖ := by simp [eval_finset_sum]
          _ ≤ ∑ k ∈ Icc (m + 1) n, ‖c k * z ^ k‖ := by apply norm_sum_le
          _ ≤ ∑ k ∈ Icc (m + 1) n, ‖c k‖ * ‖z‖ ^ k := by simp
          _ ≤ (∑ k ∈ Icc (m + 1) n, ‖c k‖) * ‖z‖ ^ (m + 1) := by
            rw [Finset.sum_mul]
            gcongr 2 with k hk
            iterate 2 rw [← Real.rpow_natCast]
            rw [Real.rpow_le_rpow_left_iff_of_base_lt_one]
            · simp at hk
              norm_cast
              linarith only [hk]
            · linarith only [hz1]
            · linarith only [hz2]
          _ = ‖c m‖ / ρ1 * ‖z‖ ^ (m + 1) := by
            congr 1
            unfold ρ1
            field_simp
            simp [hm2]
          _ = ‖c m‖ * (‖z‖ / ρ1) * ‖z‖ ^ m := by ring
          _ < ‖c m‖ * 1 * ‖z‖ ^ m := by
            gcongr 2
            · simp [hm2]
            · field_simp
              linarith only [hz1, hz2]
          _ = _ := by simp
      · have hm : (m : ℝ) ≠ 0 := by norm_cast; linarith only [hm2]
        calc
          _ = ‖c m‖ * ‖z‖ ^ m := by simp
          _ = ‖c m‖ * (‖z‖ * 2 / 2) ^ m := by simp
          _ < ‖c m‖ * (‖z‖ * 2) ^ m := by
            gcongr 2
            · simp [hm2]
            · linarith only [hm2]
            · linarith only [hz1]
          _ ≤ ‖c m‖ * ρ2 ^ m := by gcongr 2; linarith only [hz2]
          _ = ‖c m‖ * (‖c m‖ ^ (-(1 : ℝ) / m)) ^ m := by simp [ρ2]
          _ = ‖c m‖ * (‖c m‖ ^ ((-(1 : ℝ) / m) * m)) := by simp [Real.rpow_mul_natCast]
          _ = ‖c m‖ * (‖c m‖ ^ (-1 : ℝ)) := by simp [hm]
          _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀]; simp [hm2]
  let ζ := (-conj (c m) / ‖c m‖) ^ ((1 : ℂ) / m)
  let b := ρ * ζ
  have hb : ‖b‖ = ρ := by simp [b, ζ, hm2, hρ1.le]
  use b
  split_ands
  · simp [hb, hρ3]
  · specialize h3 b (by simp [hb, hρ1]) (by simp [hb])
    have hm : (m : ℂ) ≠ 0 := by norm_cast; linarith only [hm2]
    have h4 : c m * b ^ m = -‖c m‖ * ρ ^ m := by
      calc
        _ = c m * ((-conj (c m) / ‖c m‖) ^ ((1 : ℂ) / m)) ^ m * ρ ^ m := by
          simp [ζ, b, mul_pow]
          ring
        _ = c m * (-conj (c m) / ‖c m‖) * ρ ^ m := by
          congr 2
          rw [← Complex.cpow_nat_mul]
          field_simp
          simp
        _ = -(c m * conj (c m)) / ‖c m‖ * ρ ^ m := by ring
        _ = -‖c m‖ ^ 2 / ‖c m‖ * ρ ^ m := by simp [mul_conj, normSq_eq_norm_sq]
        _ = -‖c m‖ * ρ ^ m := by field_simp
    have hρ4 : |ρ| = ρ := by apply abs_of_nonneg; linarith only [hρ1]
    simp [h4, hρ4] at h3
    calc
      _ = ‖1 + c m * b ^ m + eval b r‖ := by simp [h2]
      _ ≤ ‖1 + c m * b ^ m‖ + ‖eval b r‖ := by apply norm_add_le
      _ = |1 + -‖c m‖ * ρ ^ m| + ‖eval b r‖ := by rw [h4]; norm_cast
      _ = 1 + -‖c m‖ * ρ ^ m + ‖eval b r‖ := by
        congr 1
        apply abs_of_nonneg
        linarith only [h3]
      _ < _ := by linarith only [h3]

theorem tendsto_cocompact_atTop {f : ℂ → ℝ} :
    Tendsto f (cocompact ℂ) atTop ↔ ∀ ε : ℝ, ∃ r : ℝ, ∀ z : ℂ, r < ‖z‖ → ε < f z := by
  rw [tendsto_def]
  constructor
  · intro h ε
    specialize h (Set.Ioi ε) (by rw [mem_atTop_sets]; use ε + 1; simp; grind)
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset 0] at h
    obtain ⟨r, h⟩ := h
    use r
    intro z hz
    simpa using h (by simpa using hz)
  · intro h s hs
    rw [mem_atTop_sets] at hs
    obtain ⟨ε, hs⟩ := hs
    specialize h ε
    obtain ⟨r, hr⟩ := h
    apply Metric.mem_cocompact_of_closedBall_compl_subset 0
    use r
    intro x hx
    apply hs
    linarith only [hr x (by simpa using hx)]

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : p.natDegree > 0) :
    ∃ z : ℂ, p.eval z = 0 := by
  have h1 := p.tendsto_norm_atTop (natDegree_pos_iff_degree_pos.mp hp) tendsto_norm_cocompact_atTop
  rw [tendsto_cocompact_atTop] at h1
  specialize h1 (‖p.eval 0‖)
  obtain ⟨R0, h2⟩ := h1
  let R1 := R0 ⊔ 1
  have R1_pos : 0 < R1 := by simp [R1]
  replace h2 z (h : R1 < ‖z‖) : ‖eval 0 p‖ < ‖eval z p‖ := h2 z (by grind)
  set f := fun z : ℂ => ‖p.eval z‖
  let s := Metric.closedBall (0 : ℂ) R1
  have nonempty_fs : (f '' s).Nonempty := by
    use f 0
    rw [Set.mem_image]
    use 0
    simp [s, R1_pos.le]
  have hinfmem : sInf (f '' s) ∈ f '' s := by
    apply IsCompact.sInf_mem
    · refine IsCompact.image_of_continuousOn ?_ ?_
      · exact isCompact_closedBall 0 R1
      · fun_prop
    · exact nonempty_fs
  rw [Set.mem_image] at hinfmem
  obtain ⟨z0, hz0_mem, hfz0_le⟩ := hinfmem
  replace hfz0_le z (hz : z ∈ s) : f z0 ≤ f z := by
    rw [hfz0_le]
    rw [Real.sInf_le_iff]
    · intro ε hε
      use f z
      grind
    · use 0
      simp [lowerBounds, f]
    · exact nonempty_fs
  replace hfz0_le z : f z0 ≤ f z := by
    by_cases hR1 : R1 < ‖z‖
    · replace h2 : f 0 < f z := h2 z hR1
      specialize hfz0_le 0 (by simpa [s] using R1_pos.le)
      linarith only [h2, hfz0_le]
    · exact hfz0_le z (by simpa [s] using hR1)
  use z0
  by_contra! hz0_ne0
  obtain ⟨b, hb1, hb2 : f b < f z0⟩ := dalembert_lemma hp hz0_ne0 R1_pos
  specialize hfz0_le b
  linarith only [hb2, hfz0_le]
