/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Auxiliary lemmas for Chapter 44 (Friendship Theorem)

Lemmas extracted from the main file that don't directly correspond to the tex blueprint.
-/

set_option maxHeartbeats 6400000

namespace chapter44

open scoped Classical
open Finset Matrix

/-! ### Dedekind's lemma (1858): √m rational ⟹ √m integer -/

/-- **Dedekind's lemma (1858), infinite descent proof (the book's proof).**
If `p² = m * q²` with `q > 0`, then `q ∣ p` (and hence `m` is a perfect square). -/
lemma Nat.sqrt_rational_is_integer (m p q : ℕ) (hq : 0 < q)
    (hsq : p ^ 2 = m * q ^ 2) : q ∣ p := by
  suffices h : ∀ q : ℕ, 0 < q → ∀ p : ℕ, p ^ 2 = m * q ^ 2 → q ∣ p from h q hq p hsq
  intro q; induction q using Nat.strongRecOn with
  | ind q ih =>
    intro hq p hsq
    by_cases hdvd : q ∣ p
    · exact hdvd
    · exfalso
      set ℓ := p / q
      set q₁ := p % q
      have hq1_pos : 0 < q₁ :=
        Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
      have hq1_lt : q₁ < q := Nat.mod_lt p hq
      set p₁_z : ℤ := (m : ℤ) * q - (ℓ : ℤ) * p
      have hq1_z : (q₁ : ℤ) = (p : ℤ) - (ℓ : ℤ) * q := by
        have h := Nat.div_add_mod p q
        have : q * ℓ + q₁ = p := h
        zify at this ⊢; linarith
      have hsq_z : (p : ℤ) ^ 2 = (m : ℤ) * (q : ℤ) ^ 2 := by exact_mod_cast hsq
      have hsq1_z : p₁_z ^ 2 = (m : ℤ) * (q₁ : ℤ) ^ 2 := by
        have hp : p₁_z = (m : ℤ) * q - (ℓ : ℤ) * p := rfl
        have hq : (q₁ : ℤ) = (p : ℤ) - (ℓ : ℤ) * q := hq1_z
        rw [hp, hq]
        ring_nf
        nlinarith
      have hp1_nn : 0 ≤ p₁_z := by nlinarith [sq_nonneg p₁_z, sq_nonneg (q₁ : ℤ)]
      set p₁ := p₁_z.toNat
      have hp1_cast : (p₁ : ℤ) = p₁_z := Int.toNat_of_nonneg hp1_nn
      have hsq1 : p₁ ^ 2 = m * q₁ ^ 2 := by
        exact_mod_cast (show (p₁ : ℤ) ^ 2 = (m : ℤ) * (q₁ : ℤ) ^ 2 by rw [hp1_cast]; exact hsq1_z)
      have hdvd1 : q₁ ∣ p₁ := ih q₁ hq1_lt hq1_pos p₁ hsq1
      obtain ⟨k, hk⟩ := hdvd1
      have hm_sq : m = k ^ 2 := by
        have h1 : (q₁ * k) ^ 2 = m * q₁ ^ 2 := by rw [← hk]; exact hsq1
        have h2 : k ^ 2 * q₁ ^ 2 = m * q₁ ^ 2 := by nlinarith
        have := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < q₁ ^ 2) h2
        exact this.symm
      have hpsq : p ^ 2 = (k * q) ^ 2 := by nlinarith
      have hpeq : p = k * q := by
        nlinarith [Nat.sqrt_le_sqrt (le_of_eq hpsq), sq_nonneg (p - k * q), sq_nonneg (k * q - p)]
      exact hdvd ⟨k, by linarith⟩

/-- **Dedekind's lemma (1858), alternative proof (coprime version).** -/
lemma Nat.sqrt_rational_is_integer_coprime (m p q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hsq : p ^ 2 = m * q ^ 2) : q = 1 := by
  have h1 : q ^ 2 ∣ p ^ 2 := ⟨m, by linarith⟩
  have h3 : q ^ 2 ∣ 1 := by
    have h4 : q ^ 2 ∣ Nat.gcd (q ^ 2) (p ^ 2) := Nat.dvd_gcd dvd_rfl h1
    rwa [Nat.coprime_comm.mp (hcop.pow 2 2)] at h4
  nlinarith [Nat.le_of_dvd Nat.one_pos h3, sq_nonneg q]

/-! ### Number-theoretic endgame -/

lemma false_of_sq_mul_pred_eq_sq (d k : ℕ) (hd : 3 ≤ d) (hk : 0 < k)
    (heq : k ^ 2 * (d - 1) = d ^ 2) : False := by
  obtain ⟨a, b, g, hg, had, hbk, hcop⟩ :
      ∃ a b g : ℕ, 0 < g ∧ d = a * g ∧ k = b * g ∧ Nat.Coprime a b := by
    refine ⟨d / Nat.gcd d k, k / Nat.gcd d k, Nat.gcd d k, ?_, ?_, ?_, ?_⟩
    · exact Nat.pos_of_ne_zero (by intro h; simp [Nat.gcd_eq_zero_iff.mp h] at hk)
    · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left d k)).symm
    · exact (Nat.div_mul_cancel (Nat.gcd_dvd_right d k)).symm
    · exact Nat.coprime_div_gcd_div_gcd
        (Nat.pos_of_ne_zero (by intro h; simp [Nat.gcd_eq_zero_iff.mp h] at hk))
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [zero_mul] at had; omega
    · exact ha
  have hb_pos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [zero_mul] at hbk; omega
    · exact hb
  have heq2 : b ^ 2 * (d - 1) = a ^ 2 := by
    have h2 : g ^ 2 * (b ^ 2 * (d - 1)) = g ^ 2 * a ^ 2 := by
      have : (b * g) ^ 2 * (d - 1) = (a * g) ^ 2 := by rw [← had, ← hbk]; exact heq
      nlinarith
    exact mul_left_cancel₀ (by positivity : (g : ℕ) ^ 2 ≠ 0) h2
  have hb1 : b = 1 := Nat.sqrt_rational_is_integer_coprime (d - 1) a b hb_pos hcop (by linarith)
  subst hb1; rw [one_mul] at hbk; subst hbk
  simp only [one_pow, one_mul] at heq2
  have hak : a * k = a ^ 2 + 1 := by omega
  have ha1 : a ∣ 1 := by
    have h : a ∣ a * k := dvd_mul_right a k
    rw [hak] at h
    exact (Nat.dvd_add_right (dvd_pow_self a two_ne_zero)).mp h
  have : a ≤ 1 := Nat.le_of_dvd Nat.one_pos ha1
  interval_cases a; all_goals omega

/-! ### Auxiliary lemmas for eigenvalue analysis -/

lemma sq_sum_eq_sq_mul {ι : Type*} (S : Finset ι) (f : ι → ℝ) (c : ℕ)
    (hc : 0 < c) (hf : ∀ i ∈ S, f i ^ 2 = (c : ℝ)) :
    ∃ k : ℕ, (∑ i ∈ S, f i) ^ 2 = ↑c * (k : ℝ) ^ 2 := by
  have hcr : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  set g := fun i => f i / Real.sqrt c
  have hg_pm : ∀ i ∈ S, g i = 1 ∨ g i = -1 := by
    intro i hi
    have hg1 : g i ^ 2 = 1 := by
      simp only [g, div_pow]; rw [hf i hi, Real.sq_sqrt (by positivity), div_self (by positivity)]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show g i ^ 2 = 1 ^ 2 by rw [hg1, one_pow]) with h | h
    · left; exact h
    · right; linarith
  set gi : ι → ℤ := fun i => if g i = 1 then 1 else -1
  have hsum_eq : (∑ i ∈ S, g i) = ((∑ i ∈ S, gi i : ℤ) : ℝ) := by
    rw [Int.cast_sum]; apply Finset.sum_congr rfl; intro i hi
    rcases hg_pm i hi with h | h
    · simp [gi, h]
    · simp [gi, h, show ¬((-1 : ℝ) = 1) from by norm_num]
  have hsq : (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ S, g i) ^ 2 * c := by
    have : ∑ i ∈ S, f i = (∑ i ∈ S, g i) * Real.sqrt c := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
      exact (div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr hcr)).symm
    rw [this, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq, hsum_eq]
  set s := (∑ i ∈ S, gi i)
  use s.natAbs
  rw [show (s.natAbs : ℝ) ^ 2 = (s : ℝ) ^ 2 from by
    rw [show (s.natAbs : ℝ) = ((s.natAbs : ℤ) : ℝ) from by simp]
    exact_mod_cast Int.natAbs_sq s]
  ring

lemma trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : ↥(unitaryGroup n ℝ)) (M : Matrix n n ℝ) :
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) U M).trace = M.trace := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [trace_mul_cycle, Unitary.star_mul_self_of_mem U.prop, one_mul]

end chapter44
