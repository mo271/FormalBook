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

open finset subring polynomial
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


noncomputable def phi (d : ℕ) : ℤ[X] := cyclotomic d ℤ

lemma phi_div (n : ℕ) : phi n ∣ X ^ n - 1 :=
begin
  rw phi,
  exact cyclotomic.dvd_X_pow_sub_one n ℤ,
end

lemma phi_div_2 (n : ℕ) (k : ℕ) (h₁ : 1 ≠ k) (h₂ : k ∣ n) (h₃ : k < n) :
  phi n ∣ div_by_monic (X ^ n - 1) (X ^ k - 1) :=
begin
  have h_proper_div : k ∈ n.proper_divisors := nat.mem_proper_divisors.mpr ⟨h₂, h₃⟩,
  have := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ h_proper_div,
  rw phi,
  sorry,
end


section wedderburn

variables {R : Type*}  [decidable_eq R] [division_ring R]


noncomputable theorem wedderburn (h: fintype R): is_field R :=
begin
  let Z := center R,
  haveI : fintype R := h,



  obtain ⟨n, h_card⟩ := vector_space.card_fintype Z R,


  set q := fintype.card Z,


  --conjugacy classes with more than one element
  let S := {A : conj_classes Rˣ | fintype.card A.carrier > 1}.to_finset,
  let n_k : S → ℕ := λ A, fintype.card
    (set.centralizer ({(quotient.out' (A : conj_classes Rˣ))} : set Rˣ)),

  --class  formula
  suffices : q ^ n - 1 = q - 1  + ∑ A in S, (q ^ n - 1) / (q ^ (fintype.card A.carrier) - 1), by

  { have : ∀ A : S, (n_k A ∣ n) := sorry,

  --rest of proof

  sorry,

  },
  --proof of class  formula



  all_goals {sorry},
end

end wedderburn
