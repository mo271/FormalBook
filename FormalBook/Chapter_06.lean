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
    exact gj h₀.symm
  · calc
      i ≤ i*c := le_mul_of_le_of_one_le rfl.ge (zero_lt_iff.mpr h)
      _ = j := h₀.symm


lemma le_abs_of_dvd {i j : ℤ} (gj: 0 ≠ j) (h: i ∣ j) : |i| ≤ |j| := by
  dsimp [Dvd.dvd] at h
  cases' h with c h₀
  cases' em (c = 0) with hc h
  · by_contra
    rw [hc] at h₀
    simp only [mul_zero] at h₀
    exact gj h₀.symm
  · calc
      |i| ≤ (|i|)*|c| := by exact le_mul_of_le_of_one_le' rfl.ge (Int.one_le_abs h) (abs_nonneg c) (abs_nonneg i)
        _ = |i*c| := (abs_mul i c).symm
        _ = |j| := by rw [h₀.symm]


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

  have : 0 ≤ ((q : ℝ) - 1)^2 := sq_nonneg ((q : ℝ) - 1)
  have g := (Real.sqrt_lt_sqrt_iff (sq_nonneg ((q : ℝ) - 1))).mpr (h_ineq)
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
    rw [mul_sub, mul_one]
    ring_nf
    simp only [ge_iff_le, add_right_inj]
    exact (pow_sub_mul_pow (q : ℤ) hkm).symm

  have h1 : q ^ k - 1 ∣ q ^ (m - k) - 1 := by
    refine' (@Nat.dvd_add_iff_right (q ^ k - 1 ) (q ^ (m - k) * (q ^ k - 1)) (q ^ (m - k) - 1) _ ).mpr _
    · exact Nat.dvd_mul_left (q ^ k - 1) (q ^ (m - k))
    · exact this ▸ H

  have hmk : m - k < m := by
    zify
    rw [cast_sub]
    linarith
    exact hkm
  have h0mk : 0 < m - k := Nat.sub_pos_of_lt <| Nat.lt_of_le_of_ne hkm hkeqm
  convert Nat.dvd_add_self_right.mpr (h (m - k) hmk h0mk h1)
  exact Nat.eq_add_of_sub_eq hkm rfl

def ConjAct_stabilizer_centralizer_eq :
    ∀ x : Rˣ,  Set.centralizer {x} ≃ MulAction.stabilizer (ConjAct Rˣ) x := by
  intro x
  exact {
    toFun:= by
      refine fun g ↦ ⟨ (ConjAct.toConjAct (g : Rˣ)), MulAction.mem_stabilizer_iff.mpr ?_⟩
      rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
      exact (eq_mul_inv_of_mul_eq (g.2 x rfl)).symm
    invFun := by
      refine fun g ↦ ⟨ (ConjAct.ofConjAct (g : ConjAct Rˣ)), Set.mem_centralizer_iff.mpr
        fun m hm ↦ ((eq_mul_of_mul_inv_eq ?_).symm)⟩
      rw [← ConjAct.smul_def, hm]
      exact g.2
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

  letI fintypea : ∀ (A :  ConjClasses Rˣ), Fintype ↑{A |
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
  --This was wrong: n_k should be the dimension of the centralizer( in `R`), not the cardinality
  let n_k : S' → ℕ := sorry -- fun A => Fintype.card
    --(Set.centralizer ({(Quotient.out' (A : ConjClasses Rˣ))} : Set Rˣ))

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

  -- Orbit stabilizer formula for non-singleton conjugacy classes
  have : ∀ A : S', (Fintype.card <| ConjClasses.carrier (A : ConjClasses Rˣ)) * (q ^ (n_k A) - 1)
      = q ^ n - 1 := by
    sorry

  have h1 : (q ^ n - 1) = q - 1  + ∑ A : S', (q ^ n - 1) / (q ^ (n_k A) - 1) := by
    convert H1
    sorry
  have hZ : Nonempty <| @Subtype R fun x => x ∈ Z := by
      exact Zero.instNonempty
  have hq_pow_pos : ∀ m,  1 ≤ q ^ m := by
    intro m
    refine' one_le_pow m q _

    exact Fintype.card_pos

  have h_n_k_A_dvd: ∀ A : S', (n_k A ∣ n) := by sorry
  --rest of proof
  have h_phi_dvd_q_sub_one : (phi n).eval (q : ℤ) ∣ (((q - (1 : ℕ)) : ℕ ) : ℤ) := by
    have hq : q = (Fintype.card { x // x ∈ center R }) := by rfl
    have h₁_dvd : (phi n).eval (q : ℤ) ∣ ((X : ℤ[X])  ^ n - 1).eval (q : ℤ)  := by
      exact eval_dvd <| phi_dvd n
    have h₂_dvd :
        (phi n).eval (q : ℤ) ∣ ∑ A : S', (((q ^ n - 1) : ℕ):ℤ) / ((q ^ (n_k A) - 1) : ℕ):= by
      refine' Finset.dvd_sum _
      intro A
      intro hs
      apply(Int.dvd_div_of_mul_dvd _)
      have h_one_neq: 1 ≠ n_k A := by
        sorry
      have h_k_n_lt_n: n_k A < n := by
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
        ((q - (1 :ℕ) : ℕ):ℤ) + ∑ A : S', (q ^ n - 1) / (q ^ (n_k A) - 1) := by
      have : ((q ^ n - 1 : ℕ) : ℤ ) = (q - 1 + ∑ A : S', (q ^ n - 1) / (q ^ n_k A - 1) : ℕ) :=
        congrArg Nat.cast h1
      rw [cast_add] at this
      rw [← this]
      simp [hq_pow_pos n]
    --rw [hq] at h1'
    norm_num at h1'
    simp [h1'] at h₁_dvd
    refine (Int.dvd_add_left h₂_dvd).mp ?_
    convert h₁_dvd

  by_contra

  have g : Polynomial.map (Int.castRingHom ℂ) (phi n) = ∏ lamb in (primitiveRoots n ℂ), (X - C lamb) := by
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
    exact ⟨1, Subring.one_mem (center R)⟩
  have h_q : |((q : ℤ) - 1)| = q - 1 := by
    norm_num
    exact this
  have h_norm := le_abs_of_dvd h_q_sub_one h_phi_dvd_q_sub_one
  rw [h_q] at h_norm

  refine' not_le_of_gt h_gt _
  have : (q - 1 : ℕ) = (q : ℤ) - 1 := by
    exact Int.natCast_pred_of_pos this
  rw [← this] at h_norm
  have : Int.natAbs (eval (↑q) (cyclotomic n ℤ)) = |eval (↑q) (phi n)| := by
    simp only [Int.natCast_natAbs]
    rfl
  rw [← this] at h_norm
  exact_mod_cast h_norm

end wedderburn
