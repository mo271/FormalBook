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

Authors: Moritz Firsching, Nick Kuhn
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Lie.OfAssociative

open Finset Subring Polynomial Complex BigOperators Nat
/-!
# Every finite division ring is a field

This is a TODO in `RingTheory.IntegralDomain`.
## TODO
  - statement
    - proof
      - Roots of unity
-/


-- Define cyclotomic polynomials and check their basic properties


-- TODO: find the appropriate lemmas for use in the end of the proof...
example (i j : ℕ) (gj: 0 ≠ j) (h: i ∣ j): i ≤ j:= by
  dsimp [Dvd.dvd] at h
  cases' h with c h₀
  cases' em (c = 0) with hc h
  · by_contra
    rw [hc] at h₀
    simp only [mul_zero] at h₀
    exact gj (Eq.symm h₀)
  · calc
      i ≤ i*c := le_mul_of_le_of_one_le rfl.ge (zero_lt_iff.mpr h)
      _ = j := (Eq.symm h₀)


lemma le_abs_of_dvd {i j : ℤ} (gj: 0 ≠ j) (h: i ∣ j) : |i| ≤ |j| := by
  dsimp [Dvd.dvd] at h
  cases' h with c h₀
  cases' em (c = 0) with hc h
  · by_contra
    rw [hc] at h₀
    simp only [mul_zero] at h₀
    exact gj (Eq.symm h₀)
  · calc
      |i| ≤ (|i|)*|c| := by
          exact le_mul_of_le_of_one_le' rfl.ge (Int.one_le_abs h) (abs_nonneg c) (abs_nonneg i)
        _ = |i*c| := Eq.symm (abs_mul i c)
        _ = |j| := by rw [Eq.symm h₀]


noncomputable
def phi (n : ℕ) : ℤ[X] := cyclotomic n ℤ

lemma phi_dvd (n : ℕ) : phi n ∣ X ^ n - 1 := by
  rw [phi]
  exact cyclotomic.dvd_X_pow_sub_one n ℤ

lemma phi_div_2 (n : ℕ) (k : ℕ) (_ : 1 ≠ k) (h₂ : k ∣ n) (h₃ : k < n) :
  (X ^ k - 1) * (phi n)∣ (X ^ n - 1) := by
  have h_proper_div : k ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨h₂, h₃⟩
  exact X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ h_proper_div


variable {R : Type _}  [DecidableEq R] [DivisionRing R]

-- this is currently not needed, because we use Polynomial.sub_one_lt_natAbs_cyclotomic_eval,
-- TODO: add it later to stay close to the proof in the book.
theorem h_lamb_gt_q_sub_one (q n : ℕ) (lamb : ℂ):
  lamb ∈ (primitiveRoots n ℂ) → ‖(X - (C lamb)).eval (q : ℂ)‖ > (q - 1) := by
  let a := lamb.re
  let b := lamb.im
  intro h
  have h_lamb: lamb ≠ 1 := by sorry
  have h_a_lt_one: ‖a‖ < 1 := by sorry
  have h_ineq :
      ‖((X - C lamb).eval (q : ℂ))‖^2 > ((q : ℝ) - 1)^2  := by
    calc
      _ = ‖q - lamb‖^2 := by
        simp only [eval_sub, eval_X, eval_C, norm_eq_abs]
      _ = ‖(q : ℂ) - a - I*b‖^2 := by sorry
      _ = ‖(q : ℂ) - a‖^2 + ‖b‖^2 := by sorry
      _ = (q : ℝ)^2 - 2*‖a‖*q + ‖a‖^2 + ‖b‖^2 := by sorry
      _ > ((q : ℝ) - 1)^2 := by sorry

  have : 0 ≤ ((q : ℝ) - 1)^2 := by exact sq_nonneg ((q : ℝ) - 1)
  have g := (Real.sqrt_lt_sqrt_iff this).mpr (h_ineq)
  have : Real.sqrt (((q:ℝ) - 1) ^ 2) = ((q : ℝ) - 1) := by sorry
  rw [this] at g
  rw [norm_eq_abs, Real.sqrt_sq] at g
  · exact g
  · aesop

lemma div_of_qpoly_div (k n q : ℕ) (hq : 1 < q) (hk : 0 < k) (hn : 0 < n)
    (H : q ^ k - 1 ∣ q ^ n - 1) : k ∣ n := by
  revert H
  revert hn
  apply Nat.strongInductionOn n
  intro m h hm H
  have hq' := zero_lt_of_lt hq
  by_cases hkeqm : k = m
  · exact Eq.dvd hkeqm

  have hkm : k ≤ m := by
    have : 0 < q ^ m - 1 := by
      have : 1 < q ^ m := by
        calc
          _ < q := hq
          _ = q^1 := (Nat.pow_one q).symm
          _ ≤ q ^ m := (pow_le_pow_iff_right hq).mpr hm
      exact Nat.sub_pos_of_lt this
    have : q ^ k - 1 ≤ q ^ m - 1 := Nat.le_of_dvd this H
    have :  q ^ k ≤ q ^ m  := by
      zify at this
      simp at this
      simpa [Nat.sub_add_cancel <| one_le_pow m q hq'] using this
    exact (pow_le_pow_iff_right hq).mp this

  have : q ^ m - 1 = q^(m - k)*(q ^ k - 1) + (q^(m - k) - 1) := by
    zify
    simp [one_le_pow m q hq', one_le_pow k q hq', one_le_pow (m - k) q hq']
    push_cast
    rw [mul_sub, mul_one]
    ring_nf
    simp only [ge_iff_le, add_right_inj]
    exact (pow_sub_mul_pow (q : ℤ) hkm).symm

  have h1 : q ^ k - 1 ∣ q ^ (m - k) - 1 := by
    refine' (@Nat.dvd_add_iff_right (q ^ k - 1 ) (q ^ (m - k) * (q ^ k - 1)) (q ^ (m - k) - 1) _ ).mpr _
    exact Nat.dvd_mul_left (q ^ k - 1) (q ^ (m - k))
    rw [← this]
    exact H

  have hmk : m - k < m := by
    zify
    rw [cast_sub]
    linarith
    exact hkm
  have h0mk : 0 < m - k := by exact Nat.sub_pos_of_lt <| Nat.lt_of_le_of_ne hkm hkeqm
  convert Nat.dvd_add_self_right.mpr (h (m - k) hmk h0mk h1)
  exact Nat.eq_add_of_sub_eq hkm rfl



def ConjAct_stabilizer_centralizer_eq :
    ∀ x : Rˣ,  Set.centralizer {x} ≃ MulAction.stabilizer (ConjAct Rˣ) x := by
  intro x
  exact {
    toFun:= by
      intro g
      refine' ⟨ (ConjAct.toConjAct (g : Rˣ)), _⟩
      have := g.2
      refine MulAction.mem_stabilizer_iff.mpr ?_
      rw [ConjAct.smul_def]
      simp only [ConjAct.ofConjAct_toConjAct]
      exact (eq_mul_inv_of_mul_eq (this x rfl)).symm
    invFun := by
      intro g
      refine'⟨ (ConjAct.ofConjAct (g : ConjAct Rˣ)), _⟩
      have := g.2
      refine Set.mem_centralizer_iff.mpr ?_
      intro m hm
      apply Eq.symm
      apply eq_mul_of_mul_inv_eq
      rw [← ConjAct.smul_def, hm]
      exact this
    left_inv := congrFun rfl
    right_inv := congrFun rfl}

-- Orbit stabilizer theorem, specialized to conjugacy classes
lemma orbit_stabilizer [Fintype R] (A: ConjClasses Rˣ) [Fintype A.carrier] :
  Fintype.card Rˣ = (Fintype.card A.carrier) *
    (@Fintype.card  (Set.centralizer {ConjClasses.exists_rep A|>.choose}) (
      Fintype.ofFinite (Set.centralizer {ConjClasses.exists_rep A|>.choose}))) := by
  letI := Fintype.ofFinite (Set.centralizer {ConjClasses.exists_rep A|>.choose})
  letI : Fintype ↑(MulAction.orbit (ConjAct Rˣ) (ConjClasses.exists_rep A|>.choose))
      := by refine Set.fintypeRange fun m => m • Exists.choose ?_
  letI : Fintype { x // x ∈ MulAction.stabilizer (ConjAct Rˣ)
        (ConjClasses.exists_rep A|>.choose) } := Fintype.ofFinite _
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct Rˣ)
      (ConjClasses.exists_rep A|>.choose)
  replace this := this.symm
  rw [Fintype.card_congr <| ConjAct_stabilizer_centralizer_eq (ConjClasses.exists_rep A|>.choose)]
  convert this
  rw [ConjAct.orbit_eq_carrier_conjClasses, (ConjClasses.exists_rep A|>.choose_spec)]


section wedderburn

theorem wedderburn (h: Fintype R): IsField R := by
  apply Field.toIsField

end wedderburn
