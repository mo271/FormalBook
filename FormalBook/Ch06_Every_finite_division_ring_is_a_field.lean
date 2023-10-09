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
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Subring.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Complex.Basic

open Finset Subring Polynomial Complex BigOperators Nat
/-!
# Every finite division ring is a field

This is a TODO in `RingTheory.IntegralDomain`.
## TODO
  - statement
    - proof
      - Roots of unity
-/


--Define cyclotomic polynomials and check their basic properties


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

example (n : ℕ): n + 12 > n + 7 := by
  calc
    n + 12 = 12 + n := by sorry
    _ > n + 7 := by sorry

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
      _ = ‖q - lamb‖^2 := by sorry
      _ = ‖(q : ℂ) - a - I*b‖^2 := by sorry
      _ = ‖(q : ℂ) - a‖^2 + ‖b‖^2 := by sorry
      _ = (q : ℝ)^2 - 2*‖a‖*q + ‖a‖^2 + ‖b‖^2 := by sorry
      _ > ((q : ℝ) - 1)^2 := by sorry
      _ = (q - (1 : ℝ))^2 := by sorry
  sorry



section wedderburn

theorem wedderburn (h: Fintype R): IsField R := by
  let Z := center R
  haveI : Fintype R := h

  obtain ⟨n, h_card⟩ := VectorSpace.card_fintype Z R

  have H : (∃ x y : R, x ≠ y) := by exact exists_pair_ne R

  have h_n : n ≠ 0 := by
    by_contra h
    subst h
    simp only [_root_.pow_zero] at h_card
    rcases H with ⟨x, y, H⟩
    absurd H
    exact Fintype.card_le_one_iff.mp (Nat.le_of_eq h_card) x y

  set q := Fintype.card Z

  --conjugacy classes with more than one element
  -- indexed from 1 to t in the book, here we use "S".
  have finclassa: ∀ (A : ConjClasses Rˣ), Fintype ↑(ConjClasses.carrier A) := by
    intro A
    exact ConjClasses.instFintypeElemCarrier
  have : ∀ (A :  ConjClasses Rˣ), Fintype ↑(Set.centralizer {Quotient.out' A}) := by
    intro A
    exact setFintype (Set.centralizer {Quotient.out' A})
  have fintypea : ∀ (A :  ConjClasses Rˣ), Fintype ↑{A |
      have := finclassa A; Fintype.card ↑(ConjClasses.carrier A) > 1} := by
    intro A
    exact
      setFintype
        {A |
          let_fun this := finclassa A;
          Fintype.card ↑(ConjClasses.carrier A) > 1}
  have : Fintype ↑{A |
      have := finclassa A;  Fintype.card ↑(ConjClasses.carrier A) > 1} :=
    setFintype {A |
                  let_fun this := finclassa A;
                  Fintype.card ↑(ConjClasses.carrier A) > 1}
  let S' := {A : ConjClasses Rˣ |  (Fintype.card A.carrier) > 1}
  have : Fintype S' := by exact this
  let S := S'.toFinset
  let n_k :ConjClasses Rˣ → ℕ := fun A => Fintype.card
    (Set.centralizer ({(Quotient.out' (A : ConjClasses Rˣ))} : Set Rˣ))

  have : ((q : ℤ) ^ n - 1) = (q - 1  + ∑ A in S, (q ^ n - 1) / (q ^ (n_k A) - 1)) := by
    sorry
  --class  formula (1)
  have h_n_k_A_dvd: ∀ A : ConjClasses Rˣ, (n_k A ∣ n) := by sorry
  --rest of proof
  have h_phi_dvd_q_sub_one : (phi n).eval (q : ℤ) ∣ (q - 1) := by
    have h₁_dvd : (phi n).eval (q : ℤ) ∣ ((X : ℤ[X])  ^ n - 1).eval (q : ℤ)  := by
      exact eval_dvd <| phi_dvd n
    have h₂_dvd :
     (phi n).eval (q : ℤ) ∣ ∑ A in S, ((q : ℤ)^ n - 1) / ((q : ℤ) ^ (n_k A) - 1) := by
      refine' Finset.dvd_sum _
      intro A
      intro hs
      apply(Int.dvd_div_of_mul_dvd _)
      have h_one_neq: 1 ≠ (n_k A) := by sorry
      have h_k_n_lt_n: n_k A < n := by sorry
      have h_noneval := phi_div_2 n (n_k A) h_one_neq (h_n_k_A_dvd A) h_k_n_lt_n
      have := @eval_dvd ℤ _ _ _ q h_noneval
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, IsUnit.mul_iff] at this
      exact this
    simp only [eval_sub, eval_pow, eval_X, eval_one] at h₁_dvd
    rw [this] at h₁_dvd
    sorry
    --refine (Nat.dvd_add_iff_left h₂_dvd).mpr h₁_dvd
  by_contra


  have g : map (Int.castRingHom ℂ) (phi n) = ∏ lamb in (primitiveRoots n ℂ), (X - C lamb) := by
    dsimp only [phi]
    simp only [map_cyclotomic]
    sorry
  -- what we need is in mathlib as: Polynomial.sub_one_lt_natAbs_cyclotomic_eval
  have h_gt : |(phi n).eval (q : ℤ)| > q - 1 := by sorry
  have h_q_sub_one : 0 ≠ (q : ℤ) - 1 := by sorry
  have h_q : |((q : ℤ) - 1)| = q - 1 := by sorry
  have h_norm := le_abs_of_dvd h_q_sub_one h_phi_dvd_q_sub_one
  rw [h_q] at h_norm
  exact not_le_of_gt h_gt h_norm

end wedderburn
