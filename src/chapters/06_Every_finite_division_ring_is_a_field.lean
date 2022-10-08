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
import tactic
import data.set.basic
import data.fintype.card
import ring_theory.integral_domain
import ring_theory.subring.basic
import ring_theory.polynomial.cyclotomic.basic
import data.polynomial.ring_division
import algebra.group.conj
import linear_algebra.finite_dimensional
import linear_algebra.basis
import data.polynomial.basic
import data.complex.basic

open finset subring polynomial complex
open_locale big_operators nat polynomial
/-!
# Every finite division ring is a field

This is a TODO in `ring_theory.integral_domain`.
## TODO
  - statement
    - proof
      - Roots of unity
-/


--Define cyclotomic polynomials and check their basic properties


-- TODO: find the appropriate lemmas for use in the end of the proof...
example (i j : ℕ) (gj: 0 ≠ j) (h: i ∣ j): i ≤ j:=
begin
  dsimp [has_dvd.dvd] at h,
  cases h with c h₀,
  cases em (c = 0) with hc,
  { by_contradiction,
    rw hc at h₀,
    simp only [mul_zero] at h₀,
    exact gj (eq.symm h₀), },
  { calc
      i ≤ i*c : le_mul_of_le_of_one_le rfl.ge (zero_lt_iff.mpr h)
    ... = j: (eq.symm h₀),},
end

example (i j : ℤ) (gj: 0 ≠ j) (h: i ∣ j): ∥i∥ ≤ ∥j∥ :=
begin
  sorry,
end

noncomputable def phi (n : ℕ) : ℤ[X] := cyclotomic n ℤ

lemma phi_dvd (n : ℕ) : phi n ∣ X ^ n - 1 :=
begin
  rw phi,
  exact cyclotomic.dvd_X_pow_sub_one n ℤ,
end

lemma phi_div_2 (n : ℕ) (k : ℕ) (h₁ : 1 ≠ k) (h₂ : k ∣ n) (h₃ : k < n) :
  (X ^ k - 1) * (phi n)∣ (X ^ n - 1) :=
begin
  have h_proper_div : k ∈ n.proper_divisors := nat.mem_proper_divisors.mpr ⟨h₂, h₃⟩,
  exact X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ h_proper_div,
end


section wedderburn

variables {R : Type*}  [decidable_eq R] [division_ring R]


noncomputable theorem wedderburn (h: fintype R): is_field R :=
begin
  let Z := center R,
  haveI : fintype R := h,



  obtain ⟨n, h_card⟩ := vector_space.card_fintype Z R,
  have h_n : n ≠ 0 := by sorry,

  set q := fintype.card Z,


  --conjugacy classes with more than one element
  -- indexed from 1 to t in the book, here we use "S".
  let S := {A : conj_classes Rˣ | fintype.card A.carrier > 1}.to_finset,
  let n_k :conj_classes Rˣ → ℕ := λ A, fintype.card
    (set.centralizer ({(quotient.out' (A : conj_classes Rˣ))} : set Rˣ)),

  --class  formula (1)
  suffices : (q : ℤ) ^ n - 1 = q - 1  + ∑ A in S, (q ^ n - 1) / (q ^ (n_k A) - 1), by

  { have h_n_k_A_dvd: ∀ A : conj_classes Rˣ, (n_k A ∣ n) := sorry,

  --rest of proof
  have h_phi_dvd_q_sub_one : (phi n).eval q ∣ (q - 1) := by
  { have h₁_dvd : (phi n).eval q ∣ (X ^ n - 1).eval q  := by
    { refine eval_dvd _,
      exact phi_dvd n, },
    have h₂_dvd :
     (phi n).eval(q) ∣ ∑ A in S, (q ^ n - 1) / (q ^ (n_k A) - 1) := by
     { refine finset.dvd_sum _,
      intro A,
      intro hs,
      apply(int.dvd_div_of_mul_dvd _),
      have h_one_neq: 1 ≠ (n_k A) := by sorry,
      have h_k_n_lt_n: n_k A < n := by sorry,
      have h_noneval := phi_div_2 n (n_k A) h_one_neq (h_n_k_A_dvd A) h_k_n_lt_n,
      have := @eval_dvd ℤ _ _ _ q h_noneval,
      simp at this,
      exact this, },
    simp only [eval_sub, eval_pow, eval_X, eval_one] at h₁_dvd,
    rw this at h₁_dvd,
    refine (dvd_add_iff_left h₂_dvd).mpr h₁_dvd, },
  by_contradiction,

  have g : map (int.cast_ring_hom ℂ) (phi n) = ∏ lamb in (primitive_roots n ℂ), (X - C lamb) := by
  { dsimp [phi],
    simp [int_cyclotomic_spec n],
    dsimp [cyclotomic'],
    refl, },
  have h_lamb_gt_q_sub_one : ∀ (lamb : ℂ),
    lamb ∈ (primitive_roots n ℂ) → ∥(X - C lamb).eval q∥ > q - 1 := by
    { intro lamb,
      let a := real_part lamb,
      let b := imaginary_part lamb,
      have h_lamb: lamb ≠ 1 := by sorry,
      have h_a_lt_one: ∥a∥ < 1 := by sorry,
      have h_ineq :=
        calc  ∥(X - C lamb).eval q∥^2 = ∥(q : ℂ) - lamb∥^2 : by simp only [eval_sub, eval_X, eval_C]
        ... = ∥(q : ℂ) - a - I*b∥^2 : by sorry
        ... = ∥(q : ℂ) - a∥^2 + ∥b∥^2 : by sorry
        ... = q^2 - 2*∥a∥*q + ∥a∥^2 + ∥b∥^2 : by sorry
        ... > q^2 - 2*q + 1 : by sorry
        ... = (q - 1)^2 : by sorry,
      sorry, },
  have h_gt: ∥(phi n).eval q∥ > q - 1 := by
  { sorry, },
  have norm_dvd_lemma : ∀ (a b : ℤ), a ∣ b → ∥a∥ ≤ ∥b∥ := by { sorry, },
  have h_q : ∥(q : ℤ) - 1∥ = q - 1 := by { sorry, },
  have h_norm := norm_dvd_lemma ((phi n).eval q) (q - 1) h_phi_dvd_q_sub_one,
  rw h_q at h_norm,
  exact not_le_of_gt h_gt h_norm, },
  { --proof of class  formula
  sorry, },
end

end wedderburn
