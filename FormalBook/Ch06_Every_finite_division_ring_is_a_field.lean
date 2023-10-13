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
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.ClassEquation

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
  simp only [norm_eq_abs, map_nonneg, Real.sqrt_sq] at g
  exact g

section wedderburn

theorem wedderburn (h: Fintype R): IsField R := by
  -- Z is a finite field ...
  let Z := center R

  -- .. and we can view R as a vector space of dimension n over R
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

  -- conjugacy classes with more than one element
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

  let S' := ConjClasses.noncenter Rˣ
  haveI : Fintype S' := Fintype.ofFinite ↑S'
  let S := S'.toFinset
  let n_k : ConjClasses Rˣ → ℕ := fun A => Fintype.card
    (Set.centralizer ({(Quotient.out' (A : ConjClasses Rˣ))} : Set Rˣ))

  have h_R: Fintype.card Rˣ = q ^ n - 1 := by
    have : Fintype.card Rˣ + 1 = Fintype.card R := Fintype.card_eq_card_units_add_one.symm
    rw [← h_card, ← this]
    simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, Fintype.card_ne_zero,
    add_tsub_cancel_right]

  have h_Z : Fintype.card Zˣ = q - 1 := by
    have h : Fintype.card Zˣ + 1 = Fintype.card Z := Fintype.card_eq_card_units_add_one.symm
    have : Fintype.card Z = q := rfl
    rw [← this, ← h]
    simp only [center_toSubsemiring, Subsemiring.center_toSubmonoid, ge_iff_le,
      add_le_iff_nonpos_left, nonpos_iff_eq_zero, Fintype.card_ne_zero, add_tsub_cancel_right]

  --class  formula (1)

  have H1:= (Group.card_center_add_sum_card_noncenter_eq_card Rˣ).symm
  let e := Subgroup.centerUnitsEquivUnitsCenter R
  --Note: This is fishy, it seems like it's just tautological
  let f : { x // x ∈ Submonoid.center R }ˣ ≃ { x // x ∈ Z }ˣ :=
      Equiv.inv { x // x ∈ Submonoid.center R }ˣ
  rw [h_R, Fintype.card_congr (e.toEquiv.trans f), h_Z] at H1

  have h1 : (q ^ n - 1) = q - 1  + ∑ A in S, (q ^ n - 1) / (q ^ (n_k A) - 1) := by
    convert H1
    sorry
  have hq_pow_pos : ∀ m,  1 ≤ q ^ m := by
    intro m
    refine' one_le_pow m q _
    exact Fintype.card_pos

  have h_n_k_A_dvd: ∀ A : ConjClasses Rˣ, (n_k A ∣ n) := by sorry
  --rest of proof
  have h_phi_dvd_q_sub_one : (phi n).eval (q : ℤ) ∣ (((q - (1 : ℕ)) : ℕ ) : ℤ) := by
    have hq : q = (Fintype.card { x // x ∈ center R }) := by rfl
    have h₁_dvd : (phi n).eval (q : ℤ) ∣ ((X : ℤ[X])  ^ n - 1).eval (q : ℤ)  := by
      exact eval_dvd <| phi_dvd n
    have h₂_dvd :
        (phi n).eval (q : ℤ) ∣ ∑ A in S, (((q ^ n - 1) : ℕ):ℤ) / ((q ^ (n_k A) - 1) : ℕ):= by
      refine' Finset.dvd_sum _
      intro A
      intro hs
      apply(Int.dvd_div_of_mul_dvd _)
      have h_one_neq: 1 ≠ n_k A := by
        dsimp only
        sorry
      have h_k_n_lt_n: n_k A < n := by
        dsimp only
        sorry
      have h_noneval := phi_div_2 n (n_k A) h_one_neq (h_n_k_A_dvd A) h_k_n_lt_n
      have := @eval_dvd ℤ _ _ _ q h_noneval
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, IsUnit.mul_iff] at this
      rw [← hq] at *
      convert this
      · simp [hq_pow_pos <| n_k A]
      · simp [hq_pow_pos n]
    simp only [eval_sub, eval_pow, eval_X, eval_one] at h₁_dvd
    have h1' :  (((q:ℤ) ^ n - (1 : ℕ)) : ℤ) =
        ((q - (1 :ℕ) : ℕ):ℤ) + ∑ A in S, (q ^ n - 1) / (q ^ (n_k A) - 1) := by
      have : ((q ^ n - 1 : ℕ) : ℤ ) = (q - 1 + ∑ A in S, (q ^ n - 1) / (q ^ n_k A - 1) : ℕ) :=
        congrArg Nat.cast h1
      rw [cast_add] at this
      rw [← this]
      simp [hq_pow_pos n]
    simp [hq] at h1'
    simp [h1'] at h₁_dvd
    rw [← hq] at h₁_dvd
    exact (Int.dvd_add_left h₂_dvd).mp h₁_dvd

  by_contra

  have g : map (Int.castRingHom ℂ) (phi n) = ∏ lamb in (primitiveRoots n ℂ), (X - C lamb) := by
    dsimp only [phi]
    simp only [map_cyclotomic]
    have := isPrimitiveRoot_exp n h_n
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots this]

  have : 2 ≤ q := by
    refine' Fintype.one_lt_card_iff.mpr _
    exact exists_pair_ne { x // x ∈ Z }
  -- here the book uses h_lamb_gt_q_sub_one from above
  have h_gt : ((cyclotomic n ℤ).eval ↑q).natAbs > q - 1 := by
    have hn : 1 < n := by
      sorry
    have hq : q ≠ 1 := by exact Nat.ne_of_gt this
    exact Polynomial.sub_one_lt_natAbs_cyclotomic_eval hn hq

  have h_q_sub_one : 0 ≠ (q : ℤ) - 1 := by
    have h1 : (q : ℤ) - 1 = (q - 1 : ℕ) := by
      rw [Int.ofNat_sub $ le_of_lt this]
      norm_num
    rw [h1]
    norm_cast
    exact Nat.ne_of_lt <| Nat.sub_pos_of_lt this

  have hq_eq : (q : ℤ) - 1 = (q - 1 : ℕ) := by
    have : 1 ≤ q := Fintype.card_pos
    simp [this]

  rw [← hq_eq] at h_phi_dvd_q_sub_one

  have : 1 ≤ Fintype.card { x // x ∈ center R } := by
    refine' Fintype.card_pos_iff.mpr _
    exact One.nonempty
  have h_q : |((q : ℤ) - 1)| = q - 1 := by
    norm_num
    exact this
  have h_norm := le_abs_of_dvd h_q_sub_one h_phi_dvd_q_sub_one
  rw [h_q] at h_norm

  refine' not_le_of_gt h_gt _
  have : (q - 1 : ℕ) = (q : ℤ) - 1 := by
    exact Int.coe_pred_of_pos this
  rw [← this] at h_norm
  have : Int.natAbs (eval (↑q) (cyclotomic n ℤ)) = |eval (↑q) (phi n)| := by
    simp only [Int.coe_natAbs]
    rfl
  rw [← this] at h_norm
  exact_mod_cast h_norm

end wedderburn
