/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Niven
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

open Real (exp )--pi crccos)

open Finset (Icc)
open BigOperators
/-!
# Some irrational numbers

## Outline
  - $e$ is irrational
  - $e^2$ is irrational
  - $e^4$ is irrational
  - Lemma
    - (i)
    - (ii)
    - (iii)
    - proof
      - (i)
      - (ii)
      - (iii)
  - Theorem 1.
    - proof
  - Theorem 2.
    - proof
  - Theorem 3.
    - proof

## Implementation notes
The analytic heart of Theorems 1 and 2 is carried out with the integrals
`∫_{-1}^{1} (1 - x²)ⁿ cosh (x θ) dx` (for `exp`) and `∫_{-1}^{1} (1 - x²)ⁿ cos (x θ) dx`
(for `π²`). After the substitution `x ↦ 2x - 1` these are, up to the factor `4ⁿ/2`, the integrals
`∫₀¹ xⁿ(1-x)ⁿ e^{θ(2x-1)} dx` and `∫₀¹ xⁿ(1-x)ⁿ sin (π x) dx` of the book, i.e. they are the
integrals of `n! · f_aux n` against `exp` resp. `sin`. Integrating by parts gives a three–term
recursion, which replaces the book's bookkeeping with the derivatives `F` of `f_aux`.
Theorem 3 is deduced from Niven's theorem (`niven` in Mathlib).

## Changes to the original statements
Three of the original statements were false or vacuous and have been corrected
(each is also flagged in a comment next to the lemma):
  - `lem_aux_i`: the factor `1 / n!` was missing (false e.g. for `n = 2`, `x = π`).
  - `lem_aux_ii`: the hypothesis `x < 0` was a typo for `x < 1`; also `1 ≤ n` is needed.
  - `Theorem_3`: false for `n = 4`; as in the book, `n` must be odd.
-/

namespace book
namespace irrational

/-- A real number is irrational if it is not rational. This is the same definition as in mathlib -/
def Irrational (x : ℝ) := x ∉ Set.range (fun (q : ℚ) => (q : ℝ))

/-- Our definition agrees with the one of mathlib. -/
lemma irrational_of_root {x : ℝ} (h : _root_.Irrational x) : Irrational x := h

/-- This is `irrational_iff_ne_rational` in mathlib. -/
lemma irrational_iff_not_fraction (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, x ≠ (a : ℝ) / b := by
  constructor
  · rintro h a b rfl
    exact h ⟨(a : ℚ) / b, by simp⟩
  · rintro h ⟨q, rfl⟩
    exact h q.num q.den (by simp only []; rw [Rat.cast_def, Int.cast_natCast])


/-- We define abbreviations for Euler's and for Pi-/
noncomputable def e := exp 1
--noncomputable def π := pi

/-- We want to use the series representation of the exponential function-/
theorem exponential_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-!
## Auxiliary integrals for the exponential function

`Jc n θ = ∫_{-1}^{1} (1 - x²)ⁿ cosh (x θ) dx`.
-/

section ExpIntegrals

open intervalIntegral MeasureTheory

/-- The integrals used for the irrationality of `exp`. -/
noncomputable def Jc (n : ℕ) (θ : ℝ) : ℝ := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * Real.cosh (x * θ)

lemma Jc_zero (θ : ℝ) : Jc 0 θ * θ = 2 * Real.sinh θ := by
  have hd : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x => Real.sinh (x * θ)) (Real.cosh (x * θ) * θ) x :=
    fun x _ => HasDerivAt.sinh (hasDerivAt_mul_const θ)
  have := integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [Jc, ← intervalIntegral.integral_mul_const]
  simp only [pow_zero, one_mul]
  rw [this]
  simp [Real.sinh_neg]
  ring

lemma Jc_recursion' (n : ℕ) (θ : ℝ) :
    Jc (n + 1) θ * θ ^ 2 = 4 * (n + 1) * (0 ^ n * Real.cosh θ) -
      2 * (n + 1) * (2 * n + 1) * Jc n θ + 4 * (n + 1) * n * Jc (n - 1) θ := by
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := Real.sinh (x * θ)
  let v₁' (x : ℝ) : ℝ := Real.cosh (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := Real.cosh (x * θ)
  let v₂' (x : ℝ) : ℝ := Real.sinh (x * θ) * θ
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hf (x) : HasDerivAt f (- 2 * x) x :=
    ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv (by push_cast; ring)
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x :=
    ((hf x).pow (n + 1)).congr_deriv (by simp only [u₁', Nat.add_sub_cancel]; push_cast; ring)
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := HasDerivAt.sinh (hasDerivAt_mul_const θ)
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x :=
    ((hasDerivAt_id' x).mul ((hf x).pow n)).congr_deriv (by simp only [u₂', Pi.pow_apply]; ring)
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := HasDerivAt.cosh (hasDerivAt_mul_const θ)
  have e1 := integral_mul_deriv_eq_deriv_mul (a := -1) (b := 1) (fun x _ => hu₁ x)
    (fun x _ => hv₁ x) (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _)
  have e2 := integral_mul_deriv_eq_deriv_mul (a := -1) (b := 1) (fun x _ => hu₂ x)
    (fun x _ => hv₂ x) (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _)
  have b1 : u₁ 1 = 0 := by simp [u₁, f]
  have b2 : u₁ (-1) = 0 := by simp [u₁, f]
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * Real.cosh θ) := by
    simp only [u₂, v₂, f]
    simp only [one_pow, sub_self, neg_one_sq, one_mul, neg_mul, Real.cosh_neg]
    ring
  have hJ1 : Jc (n + 1) θ * θ = ∫ x in (-1)..1, u₁ x * v₁' x := by
    rw [Jc, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [u₁, v₁', f]
    ring
  have hmid : (∫ x in (-1)..1, u₁' x * v₁ x) * θ =
      -(2 * (n + 1)) * ∫ x in (-1)..1, u₂ x * v₂' x := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [u₁', v₁, u₂, v₂']
    ring
  have hlast : ∫ x in (-1)..1, u₂' x * v₂ x =
      (2 * n + 1) * Jc n θ - 2 * n * Jc (n - 1) θ := by
    have hp : ∀ x, u₂' x * v₂ x = (2 * n + 1) * ((1 - x ^ 2) ^ n * Real.cosh (x * θ)) -
        2 * n * ((1 - x ^ 2) ^ (n - 1) * Real.cosh (x * θ)) := by
      intro x
      simp only [u₂', v₂, f]
      rcases n with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        push_cast
        ring
    rw [intervalIntegral.integral_congr (fun x _ => hp x), intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · rfl
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [b1, b2] at e1
  rw [t, hlast] at e2
  have hsq : Jc (n + 1) θ * θ ^ 2 = (Jc (n + 1) θ * θ) * θ := by ring
  rw [hsq, hJ1, e1]
  linear_combination (-1 : ℝ) * hmid + (2 * (n + 1) : ℝ) * e2

lemma Jc_recursion (n : ℕ) (θ : ℝ) :
    Jc (n + 2) θ * θ ^ 2 =
      - 2 * (n + 2) * (2 * n + 3) * Jc (n + 1) θ + 4 * (n + 2) * (n + 1) * Jc n θ := by
  rw [Jc_recursion' (n + 1)]
  simp only [Nat.add_sub_cancel, pow_succ, mul_zero, zero_mul]
  push_cast
  ring

lemma Jc_one (θ : ℝ) : Jc 1 θ * θ ^ 3 = 4 * θ * Real.cosh θ - 4 * Real.sinh θ := by
  have h := Jc_recursion' 0 θ
  simp only [CharP.cast_eq_zero, pow_zero, zero_add] at h
  have h0 := Jc_zero θ
  linear_combination θ * h + (-2 : ℝ) * h0

lemma Jc_pos (n : ℕ) (θ : ℝ) : 0 < Jc n θ := by
  refine intervalIntegral.integral_pos (by norm_num) (by fun_prop) ?_ ⟨0, by simp⟩
  intro x hx
  refine mul_nonneg (pow_nonneg ?_ _) (Real.cosh_pos _).le
  rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
  exact ⟨hx.1.le, hx.2⟩

lemma Jc_le (n : ℕ) (θ : ℝ) : Jc n θ ≤ 2 * Real.cosh θ := by
  rw [← Real.norm_of_nonneg (Jc_pos n θ).le]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.cosh θ) ?_).trans
    (by norm_num [mul_comm])
  intro x hx
  simp only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] at hx
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.cosh_pos _)]
  have h1 : |1 - x ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : Real.cosh (x * θ) ≤ Real.cosh θ := by
    rw [Real.cosh_le_cosh, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2⟩)
  calc |1 - x ^ 2| ^ n * Real.cosh (x * θ) ≤ 1 * Real.cosh θ := by
        gcongr
        exact pow_le_one₀ (abs_nonneg _) h1
    _ = Real.cosh θ := one_mul _

/-- For an integer `θ = k`, `θ^(2n+1) Jc n θ / n!` is an integer combination of
`sinh k` and `cosh k`. -/
lemma Jc_int_comb (k : ℤ) (n : ℕ) : ∃ A B : ℤ,
    (k : ℝ) ^ (2 * n + 1) * Jc n k =
      n.factorial * (A * Real.sinh k + B * Real.cosh k) := by
  set θ : ℝ := (k : ℝ)
  suffices H : ∀ n : ℕ, (∃ A B : ℤ, θ ^ (2 * n + 1) * Jc n θ =
      n.factorial * (A * Real.sinh θ + B * Real.cosh θ)) ∧
      (∃ A B : ℤ, θ ^ (2 * (n + 1) + 1) * Jc (n + 1) θ =
      (n + 1).factorial * (A * Real.sinh θ + B * Real.cosh θ)) from (H n).1
  intro n
  induction n with
  | zero =>
    refine ⟨⟨2, 0, ?_⟩, ⟨-4, 4 * k, ?_⟩⟩
    · have := Jc_zero θ
      simp only [Nat.factorial_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero]
      linear_combination this
    · have := Jc_one θ
      simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_mul]
      linear_combination this
  | succ n ih =>
    obtain ⟨⟨A, B, h0⟩, ⟨A', B', h1⟩⟩ := ih
    refine ⟨⟨A', B', h1⟩, ⟨-2 * (2 * n + 3) * A' + 4 * k ^ 2 * A,
      -2 * (2 * n + 3) * B' + 4 * k ^ 2 * B, ?_⟩⟩
    have hr := Jc_recursion n θ
    rw [show n + 1 + 1 = n + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [Nat.factorial_succ] at h1
    push_cast at h1 ⊢
    linear_combination θ ^ (2 * n + 3) * hr + (-2 * (n + 2) * (2 * n + 3) : ℝ) * h1 +
      (4 * (n + 2) * (n + 1) * θ ^ 2 : ℝ) * h0

/-- `x ^ (2n+1) / n!` tends to zero. -/
lemma tendsto_pow_two_mul_add_one_div_factorial (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => a ^ (2 * n + 1) / n.factorial) Filter.atTop (nhds 0) := by
  rw [← mul_zero a]
  refine ((FloorSemiring.tendsto_pow_div_factorial_atTop (a ^ 2)).const_mul a).congr
    (fun x => ?_)
  rw [← pow_mul, mul_div_assoc', _root_.pow_succ']

/-- The key result: `exp (2 k)` is irrational for every positive natural number `k`. -/
theorem irrational_exp_two_mul (k : ℕ) (hk : 0 < k) : _root_.Irrational (exp (2 * k)) := by
  rintro ⟨q, hq⟩
  set θ : ℝ := ((k : ℤ) : ℝ)
  have hθ : θ = k := by simp [θ]
  have hθpos : 0 < θ := by rw [hθ]; exact_mod_cast hk
  set a : ℤ := q.num
  set b : ℕ := q.den
  have hb : (0 : ℝ) < b := by exact_mod_cast q.pos
  have hexp : exp θ * exp θ = a / b := by
    rw [← Real.exp_add, hθ, ← two_mul, ← hq, Rat.cast_def]
  have hinv : exp θ * exp (-θ) = 1 := by rw [← Real.exp_add]; simp
  set C : ℝ := 2 * b * exp θ * (2 * Real.cosh θ)
  obtain ⟨n, hn⟩ := (((tendsto_pow_two_mul_add_one_div_factorial θ).const_mul C).eventually_lt_const
    (show C * 0 < 1 by simp)).exists
  obtain ⟨A, B, hAB⟩ := Jc_int_comb k n
  replace hAB : θ ^ (2 * n + 1) * Jc n θ =
      n.factorial * (A * Real.sinh θ + B * Real.cosh θ) := hAB
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  set z : ℤ := A * (a - b) + B * (a + b)
  have hz : (z : ℝ) = 2 * b * exp θ * (θ ^ (2 * n + 1) * Jc n θ / n.factorial) := by
    rw [hAB, mul_div_cancel_left₀ _ hfac.ne', Real.sinh_eq, Real.cosh_eq]
    have hb' : (b : ℝ) ≠ 0 := hb.ne'
    have hexp' : (b : ℝ) * (exp θ * exp θ) = a := by rw [hexp]; field_simp
    simp only [z]
    push_cast
    linear_combination (-(A : ℝ) - B) * hexp' + ((A : ℝ) - B) * b * hinv
  have hJ := Jc_pos n θ
  have hJle := Jc_le n θ
  have h0 : (0 : ℝ) < z := by rw [hz]; positivity
  have h1 : (z : ℝ) < 1 := by
    rw [hz]
    refine lt_of_le_of_lt ?_ hn
    simp only [C]
    have : 0 ≤ θ ^ (2 * n + 1) / n.factorial := by positivity
    have : 0 ≤ 2 * (b : ℝ) * exp θ := by positivity
    calc 2 * b * exp θ * (θ ^ (2 * n + 1) * Jc n θ / n.factorial)
        = 2 * b * exp θ * (Jc n θ * (θ ^ (2 * n + 1) / n.factorial)) := by ring
      _ ≤ 2 * b * exp θ * (2 * Real.cosh θ * (θ ^ (2 * n + 1) / n.factorial)) := by gcongr
      _ = _ := by ring
  have h0' : (0 : ℤ) < z := by exact_mod_cast h0
  have h1' : z < 1 := by exact_mod_cast h1
  omega

end ExpIntegrals

/-!
## Some Proofs of irrationality
-/


theorem e_irrational : Irrational e := by
  apply irrational_of_root
  apply _root_.Irrational.of_pow 2
  have h := irrational_exp_two_mul 1 one_pos
  rwa [Nat.cast_one, mul_one, show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul] at h

theorem e_pow_2_irrational : Irrational (e ^ 2) := by
  apply irrational_of_root
  have h := irrational_exp_two_mul 1 one_pos
  rwa [Nat.cast_one, mul_one, show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul] at h

/-- Binary digit sums: they are positive, and equal to `1` exactly for powers of two. -/
lemma digits_two_sum (n : ℕ) (hn : n ≠ 0) :
    1 ≤ (Nat.digits 2 n).sum ∧ ((Nat.digits 2 n).sum = 1 ↔ ∃ m : ℕ, n = 2 ^ m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact ⟨by norm_num, ⟨fun _ => ⟨0, rfl⟩, fun _ => by norm_num⟩⟩
  · have h2 : n / 2 ≠ 0 := by omega
    have hlt : n / 2 < n := by omega
    obtain ⟨ih1, ih2⟩ := ih (n / 2) hlt h2
    rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
    refine ⟨by omega, ⟨fun hs => ?_, ?_⟩⟩
    · have hm : n % 2 = 0 := by omega
      obtain ⟨m, hm'⟩ := ih2.mp (by omega)
      exact ⟨m + 1, by rw [pow_succ]; omega⟩
    · rintro ⟨m, rfl⟩
      rcases m with _ | m
      · simp at h
      · have e1 : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; simp
        have e2 : 2 ^ (m + 1) % 2 = 0 := by rw [pow_succ]; simp
        rw [e1] at ih2
        have := ih2.mpr ⟨m, rfl⟩
        rw [e1]
        omega

/--
"For any `n ≥ 1` the integer `n!` contains the prime factor `2` at most `n − 1` times —
with equality if (and only if) `n` is a power of two, `n = 2 ^ m`."
-/
lemma little_lemma (n : ℕ) (h_n : n ≠ 0) :
  ¬ (2 ^ n ∣ n.factorial) ∧ (2 ^ (n - 1) ∣ n.factorial ↔ ∃ m : ℕ, n = 2 ^ m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := sub_one_mul_padicValNat_factorial (p := 2) n
  have hd : ∀ k, 2 ^ k ∣ n.factorial ↔ k ≤ padicValNat 2 n.factorial := fun k =>
    padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)
  have hle := Nat.digit_sum_le 2 n
  obtain ⟨hpos, hiff⟩ := digits_two_sum n h_n
  simp only [one_mul, show (2 : ℕ) - 1 = 1 from rfl] at hv
  rw [hd, hd, ← hiff]
  refine ⟨by omega, ⟨fun h => by omega, fun h => by omega⟩⟩

theorem e_pow_4_irrational : Irrational (e ^ 4) := by
  apply irrational_of_root
  have h := irrational_exp_two_mul 2 two_pos
  rwa [show (2 : ℝ) * (2 : ℕ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul] at h

/-!  ### Proofs of the main theorems-/

/-!
####  Auxiliary Lemma
We first prove the following lemma (see `lem_aux_i` to `lem_aux_iii` below):
Let `n : ℕ`, `n ≥ 1` be fixed, and consider `f_aux n x = x ^ n * (1 - x) ^ n / n.factorial`. Then
(i) `f_aux n` is equal, as a function in `x`, to a polynomial of the form
  `(sum (i : Icc n (2 * n)), (c i) x ^i) / n.factorial`, where `c i : ℤ`.
(ii) For `0 < x < 1` we have `0 < f_aux n x < 1 / n.factorial` .
(iii) The `k`-th derivatives `iterated_deriv k (f_aux n)` take integer values at `x = 0` and `x = 1`
   for all `k ≥ 0`.
-/

/-- The auxiliary function `xⁿ * (1 - x)ⁿ / n!` used in the irrationality proofs. -/
@[nolint defsWithUnderscore]
noncomputable def f_aux (n : ℕ) (x : ℝ) :=  x ^ n * (1 - x) ^ n / n.factorial

/-- Note: the original statement omitted the factor `1 / n!`, which made it false
(e.g. for `n = 2` and `x = π`). -/
lemma lem_aux_i (n : ℕ) (x : ℝ) :
    ∃ c : ℕ → ℤ, f_aux n x = (∑ i ∈ Icc n (2 * n), (c i) * x ^ i) / n.factorial := by
  refine ⟨fun i => (-1) ^ (i - n) * (n.choose (i - n) : ℤ), ?_⟩
  unfold f_aux
  congr 1
  have hI : Icc n (2 * n) = Finset.Ico n (n + (n + 1)) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show n + (n + 1) - n = n + 1 by omega,
    show (1 - x) = -x + 1 by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Nat.add_sub_cancel_left, one_pow, mul_one, neg_pow x, pow_add]
  push_cast
  ring

/-- Note: the original statement had the typo `x < 0` (instead of `x < 1`), which made it
vacuous. We also need `n ≥ 1`, as in the book (for `n = 0` we have `f_aux 0 x = 1 = 1 / 0!`). -/
lemma lem_aux_ii (n : ℕ) (x : ℝ) (h_1 : 0 < x) (h_2 : x < 1) (h_n : 1 ≤ n) :
  (0 < f_aux n x) ∧ (f_aux n x < (1 : ℝ) / n.factorial) := by
  have h3 : 0 < 1 - x := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold f_aux
  constructor
  · exact div_pos (mul_pos (pow_pos h_1 n) (pow_pos h3 n)) hfac
  · rw [div_lt_div_iff_of_pos_right hfac, ← mul_pow]
    exact pow_lt_one₀ (by positivity) (by nlinarith) (by omega)

/-- Iterated derivatives of a polynomial function. -/
lemma iteratedDeriv_poly_eval (p : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) =
      fun x => (Polynomial.derivative^[k] p).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-!
WARNING: There might be a better way to state this, not sure what the best API for derivatives of
smooth (polynomial) functions is
-/
lemma lem_aux_iii (n : ℕ) (k : ℕ):
    iteratedDeriv k (f_aux n) 0 ∈ Set.range (fun (q : ℚ) ↦ (q : ℝ)) ∧
    iteratedDeriv k (f_aux n) 1 ∈ Set.range (fun (q : ℚ) ↦ (q : ℝ))  := by
  let P : Polynomial ℚ :=
    Polynomial.C (1 / (n.factorial : ℚ)) * Polynomial.X ^ n * (1 - Polynomial.X) ^ n
  have hf : f_aux n = fun x => (P.map (algebraMap ℚ ℝ)).eval x := by
    funext x
    simp only [f_aux, P, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_C]
    simp only [one_div, map_inv₀, map_natCast]
    ring
  have key : ∀ y : ℚ, iteratedDeriv k (f_aux n) (y : ℝ) =
      ((Polynomial.derivative^[k] P).eval y : ℚ) := by
    intro y
    rw [hf, iteratedDeriv_poly_eval, Polynomial.iterate_derivative_map]
    beta_reduce
    rw [Polynomial.eval_map, show ((y : ℝ)) = algebraMap ℚ ℝ y from rfl,
      Polynomial.eval₂_at_apply]
    rfl
  refine ⟨⟨(Polynomial.derivative^[k] P).eval 0, ?_⟩, ⟨(Polynomial.derivative^[k] P).eval 1, ?_⟩⟩
  · have := key 0
    simp only [Rat.cast_zero] at this
    exact this.symm
  · have := key 1
    simp only [Rat.cast_one] at this
    exact this.symm


/-!### Theorems 1 to 3-/

/--For any non-zero rational number `r`, the exponential `e ^ r` is irrational.-/
theorem Theorem_1 (r : ℚ) (h_r : r ≠ 0) : Irrational (exp r) := by
  have : ∀ k : ℤ, k > 0 → Irrational (exp k) := by
    intro k hk
    apply irrational_of_root
    apply _root_.Irrational.of_pow 2
    have h := irrational_exp_two_mul k.toNat (by omega)
    rwa [show ((k.toNat : ℕ) : ℝ) = (k : ℝ) by exact_mod_cast Int.toNat_of_nonneg hk.le,
      mul_comm, Real.exp_mul, Real.rpow_two] at h
  -- write `r = p / d`; then `exp r ^ (2 d) = exp (2 p)`.
  apply irrational_of_root
  apply _root_.Irrational.of_pow (2 * r.den)
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hpow : exp r ^ (2 * r.den) = exp (2 * r.num) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Rat.cast_def]
    push_cast
    field_simp
  rw [hpow]
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr h_r
  rcases lt_or_gt_of_ne hnum with hneg | hpos
  · have h := this (-(2 * r.num)) (by omega)
    apply _root_.Irrational.of_inv
    rw [← Real.exp_neg]
    push_cast at h
    exact h
  · have h := this (2 * r.num) (by omega)
    push_cast at h
    exact h

open Real

/-!
## Auxiliary integrals for `π`

`Ic n θ = ∫_{-1}^{1} (1 - x²)ⁿ cos (x θ) dx`, as in mathlib's proof of `irrational_pi`.
-/

section PiIntegrals

open intervalIntegral MeasureTheory

/-- The integrals used for the irrationality of `π²`. -/
noncomputable def Ic (n : ℕ) (θ : ℝ) : ℝ := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

lemma Ic_zero (θ : ℝ) : Ic 0 θ * θ = 2 * sin θ := by
  have hd : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x => sin (x * θ)) (cos (x * θ) * θ) x :=
    fun x _ => HasDerivAt.sin (hasDerivAt_mul_const θ)
  have := integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [Ic, ← intervalIntegral.integral_mul_const]
  simp only [pow_zero, one_mul]
  rw [this]
  simp [sin_neg]
  ring

lemma Ic_recursion' (n : ℕ) (θ : ℝ) :
    Ic (n + 1) θ * θ ^ 2 = - (4 * (n + 1) * (0 ^ n * cos θ)) +
      2 * (n + 1) * (2 * n + 1) * Ic n θ - 4 * (n + 1) * n * Ic (n - 1) θ := by
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := sin (x * θ)
  let v₁' (x : ℝ) : ℝ := cos (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := cos (x * θ)
  let v₂' (x : ℝ) : ℝ := -sin (x * θ) * θ
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hf (x) : HasDerivAt f (- 2 * x) x :=
    ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv (by push_cast; ring)
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x :=
    ((hf x).pow (n + 1)).congr_deriv (by simp only [u₁', Nat.add_sub_cancel]; push_cast; ring)
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := HasDerivAt.sin (hasDerivAt_mul_const θ)
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x :=
    ((hasDerivAt_id' x).mul ((hf x).pow n)).congr_deriv (by simp only [u₂', Pi.pow_apply]; ring)
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := HasDerivAt.cos (hasDerivAt_mul_const θ)
  have e1 := integral_mul_deriv_eq_deriv_mul (a := -1) (b := 1) (fun x _ => hu₁ x)
    (fun x _ => hv₁ x) (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _)
  have e2 := integral_mul_deriv_eq_deriv_mul (a := -1) (b := 1) (fun x _ => hu₂ x)
    (fun x _ => hv₂ x) (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _)
  have b1 : u₁ 1 = 0 := by simp [u₁, f]
  have b2 : u₁ (-1) = 0 := by simp [u₁, f]
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by
    simp only [u₂, v₂, f]
    simp only [one_pow, sub_self, neg_one_sq, one_mul, neg_mul, cos_neg]
    ring
  have hJ1 : Ic (n + 1) θ * θ = ∫ x in (-1)..1, u₁ x * v₁' x := by
    rw [Ic, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [u₁, v₁', f]
    ring
  have hmid : (∫ x in (-1)..1, u₁' x * v₁ x) * θ =
      (2 * (n + 1)) * ∫ x in (-1)..1, u₂ x * v₂' x := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [u₁', v₁, u₂, v₂']
    ring
  have hlast : ∫ x in (-1)..1, u₂' x * v₂ x =
      (2 * n + 1) * Ic n θ - 2 * n * Ic (n - 1) θ := by
    have hp : ∀ x, u₂' x * v₂ x = (2 * n + 1) * ((1 - x ^ 2) ^ n * cos (x * θ)) -
        2 * n * ((1 - x ^ 2) ^ (n - 1) * cos (x * θ)) := by
      intro x
      simp only [u₂', v₂, f]
      rcases n with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        push_cast
        ring
    rw [intervalIntegral.integral_congr (fun x _ => hp x), intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · rfl
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [b1, b2] at e1
  rw [t, hlast] at e2
  have hsq : Ic (n + 1) θ * θ ^ 2 = (Ic (n + 1) θ * θ) * θ := by ring
  rw [hsq, hJ1, e1]
  linear_combination (-1 : ℝ) * hmid + (-2 * (n + 1) : ℝ) * e2

lemma Ic_recursion (n : ℕ) (θ : ℝ) :
    Ic (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * Ic (n + 1) θ - 4 * (n + 2) * (n + 1) * Ic n θ := by
  rw [Ic_recursion' (n + 1)]
  simp only [Nat.add_sub_cancel, pow_succ, mul_zero, zero_mul]
  push_cast
  ring

lemma Ic_one (θ : ℝ) : Ic 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  have h := Ic_recursion' 0 θ
  simp only [CharP.cast_eq_zero, pow_zero, zero_add] at h
  have h0 := Ic_zero θ
  linear_combination θ * h + (2 : ℝ) * h0

lemma Ic_pos (n : ℕ) : 0 < Ic n (π / 2) := by
  refine intervalIntegral.integral_pos (by norm_num) (by fun_prop) ?_ ⟨0, by simp⟩
  intro x hx
  refine mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

lemma Ic_le (n : ℕ) : Ic n (π / 2) ≤ 2 := by
  rw [← Real.norm_of_nonneg (Ic_pos n).le]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) ?_).trans (by norm_num)
  intro x hx
  simp only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] at hx
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |1 - x ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |1 - x ^ 2| ^ n * |cos (x * (π / 2))| ≤ 1 * 1 := by
        gcongr
        · exact pow_le_one₀ (abs_nonneg _) h1
        · exact abs_cos_le_one _
    _ = 1 := one_mul _

/-- If `c θ² = a` with `θ = π / 2` and integers `a, c`, then `cⁿ θ^(2n+1) Ic n θ / n!`
is an integer. -/
lemma Ic_int (a c : ℤ) (hca : (c : ℝ) * (π / 2) ^ 2 = a) (n : ℕ) : ∃ z : ℤ,
    (c : ℝ) ^ n * (π / 2) ^ (2 * n + 1) * Ic n (π / 2) = n.factorial * z := by
  set θ : ℝ := π / 2
  suffices H : ∀ n : ℕ, (∃ z : ℤ, (c : ℝ) ^ n * θ ^ (2 * n + 1) * Ic n θ = n.factorial * z) ∧
      (∃ z : ℤ, (c : ℝ) ^ (n + 1) * θ ^ (2 * (n + 1) + 1) * Ic (n + 1) θ =
        (n + 1).factorial * z) from (H n).1
  have hs : sin θ = 1 := sin_pi_div_two
  have hc : cos θ = 0 := cos_pi_div_two
  intro n
  induction n with
  | zero =>
    refine ⟨⟨2, ?_⟩, ⟨4 * c, ?_⟩⟩
    · have := Ic_zero θ
      rw [hs] at this
      simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, Int.cast_ofNat]
      linear_combination this
    · have := Ic_one θ
      rw [hs, hc] at this
      simp only [Int.cast_mul, Int.cast_ofNat]
      linear_combination (c : ℝ) * this
  | succ n ih =>
    obtain ⟨⟨z, h0⟩, ⟨z', h1⟩⟩ := ih
    refine ⟨⟨z', h1⟩, ⟨2 * (2 * n + 3) * c * z' - 4 * c * a * z, ?_⟩⟩
    have hr := Ic_recursion n θ
    rw [show n + 1 + 1 = n + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [Nat.factorial_succ] at h1
    push_cast at h1 ⊢
    linear_combination ((c : ℝ) ^ (n + 2) * θ ^ (2 * n + 3)) * hr +
      (2 * (n + 2) * (2 * n + 3) * c : ℝ) * h1 +
      (-4 * (n + 2) * (n + 1) * c * ((c : ℝ) ^ n * θ ^ (2 * n + 1) * Ic n θ)) * hca +
      (-4 * (n + 2) * (n + 1) * c * a : ℝ) * h0

end PiIntegrals

/-- Note: the hypotheses `r` and `h_r` are not needed. -/
@[nolint unusedArguments]
theorem Theorem_2 (r : ℚ) (h_r : r ≠ 0) : Irrational (π ^ 2) := by
  rintro ⟨q, hq⟩
  beta_reduce at hq
  set θ : ℝ := π / 2
  have hθ : 0 < θ := by positivity
  have hq0 : (0 : ℝ) < q := by rw [hq]; positivity
  set a : ℤ := q.num
  set c : ℤ := 4 * q.den
  have ha : (0 : ℝ) < a := by exact_mod_cast Rat.num_pos.mpr (by exact_mod_cast hq0)
  have hca : (c : ℝ) * θ ^ 2 = a := by
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [θ, c, a, div_pow, ← hq]
    rw [Rat.cast_def]
    push_cast
    field_simp
    ring
  obtain ⟨n, hn⟩ := (((FloorSemiring.tendsto_pow_div_factorial_atTop (a : ℝ)).mul_const
    (θ * 2)).eventually_lt_const (show (0 : ℝ) * (θ * 2) < 1 by simp)).exists
  obtain ⟨z, hz⟩ := Ic_int a c hca n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpow : (c : ℝ) ^ n * θ ^ (2 * n + 1) = (a : ℝ) ^ n * θ := by
    rw [← hca, mul_pow, pow_succ, pow_mul]
    ring
  have hz' : (z : ℝ) = (a : ℝ) ^ n / n.factorial * (θ * Ic n θ) := by
    rw [hpow] at hz
    field_simp
    linear_combination -hz
  have hI := Ic_pos n
  have hIle := Ic_le n
  have h0 : (0 : ℝ) < z := by rw [hz']; positivity
  have h1 : (z : ℝ) < 1 := by
    rw [hz']
    refine lt_of_le_of_lt ?_ hn
    have : 0 ≤ (a : ℝ) ^ n / n.factorial := by positivity
    gcongr
  have h0' : (0 : ℤ) < z := by exact_mod_cast h0
  have h1' : z < 1 := by exact_mod_cast h1
  omega

/-- Note: the original statement was for all `n ≥ 3`, but it is false for `n = 4`
(`arccos (1 / 2) / π = 1 / 3`). As in the book, we require `n` to be odd. -/
theorem Theorem_3 (n : ℕ) (h_n : n ≥ 3) (h_odd : Odd n) :
    Irrational ( arccos (1 / (n : ℝ).sqrt) / π) := by
  rintro ⟨q, hq⟩
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast h_n
  have hsqrt : 0 < (n : ℝ).sqrt := Real.sqrt_pos.mpr (by linarith)
  set θ := arccos (1 / (n : ℝ).sqrt)
  have hθ : θ = q * π := by
    simp only at hq
    rw [hq]; field_simp [pi_ne_zero]
  have hcos : cos θ = 1 / (n : ℝ).sqrt := by
    apply cos_arccos
    · have : 0 < 1 / (n : ℝ).sqrt := by positivity
      linarith
    · rw [div_le_one hsqrt, Real.one_le_sqrt]
      linarith
  have hcos2 : cos (2 * θ) = 2 / n - 1 := by
    rw [cos_two_mul, hcos, div_pow, Real.sq_sqrt (by linarith)]
    ring
  have hN := niven (θ := 2 * θ) ⟨2 * q, by rw [hθ]; push_cast; ring⟩
    ⟨2 / n - 1, by rw [hcos2]; push_cast; ring⟩
  rw [hcos2] at hN
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  obtain ⟨m, rfl⟩ := h_odd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
  rcases hN with h | h | h | h | h <;> field_simp at h
  all_goals
    first
    | (have h' : ((2 * m + 1 : ℕ) : ℝ) = 4 := by push_cast at h ⊢; linarith
       norm_cast at h'; omega)
    | (push_cast at h hn; nlinarith)
