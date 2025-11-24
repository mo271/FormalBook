/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse


open Real (exp )--pi crccos)

open Finset (Icc)
open BigOperators
/-!
# Some irrational numbers

## TODO : All proofs,
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
-/

namespace book
namespace irrational

/-- A real number is irrational if it is not rational. This is the same definition as in mathlib -/
def Irrational (x : ℝ) := x ∉ Set.range (fun (q : ℚ) => (q : ℝ))

/-- This is `irrational_iff_ne_rational` in mathlib. -/
lemma irrational_iff_not_fraction (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, x ≠ (a : ℝ) / b := by
  sorry


/-- We define abbreviations for Euler's and for Pi-/
noncomputable def e := exp 1
--noncomputable def π := pi

/-- We want to use the series representation of the exponential function-/
theorem exponential_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial)) (Real.exp x) := by
  sorry

/-!
## Some Proofs of irrationality
-/


theorem e_irrational : Irrational e := by
  sorry

theorem e_pow_2_irrational : Irrational (e ^ 2) := by
  sorry

/--
"For any `n ≥ 1` the integer `n!` contains the prime factor `2` at most `n − 1` times —
with equality if (and only if) `n` is a power of two, `n = 2 ^ m`."
-/
lemma little_lemma (n : ℕ) (h_n : n ≠ 0) :
  ¬ (2 ^ n ∣ n.factorial) ∧ (2 ^ (n - 1) ∣ n.factorial ↔ ∃ m : ℕ, n = 2 ^ m) := by
  sorry

theorem e_pow_4_irrational : Irrational (e ^ 4) := by
  sorry

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
noncomputable def f_aux (n : ℕ) (x : ℝ) :=  x ^ n * (1 - x) ^ n / n.factorial

lemma lem_aux_i (n : ℕ) (x : ℝ) : ∃ c : ℕ → ℤ, f_aux n x = ∑ i ∈ Icc n (2 * n), (c i) * x ^ i := by
  sorry

lemma lem_aux_ii (n : ℕ) (x : ℝ) (h_1 : 0 < x) (h_2 : x < 0) :
  (0 < f_aux n x) ∧ (f_aux n x < (1 : ℝ) / n.factorial) := by
  constructor <;> linarith

/-!
WARNING: There might be a better way to state this, not sure what the best API for derivatives of
smooth (polynomial) functions is
-/
lemma lem_aux_iii (n : ℕ) (k : ℕ): iteratedDeriv k (f_aux n) 0 ∈  Set.range (fun (q : ℚ) ↦ (q : ℝ)) ∧
  iteratedDeriv k (f_aux n) 1 ∈ Set.range (fun (q : ℚ) ↦ (q : ℝ))  := by
  sorry


/-!### Theorems 1 to 3-/

/--For any non-zero rational number `r`, the exponential `e ^ r` is irrational.-/
theorem Theorem_1 (r : ℚ) (h_r : r ≠ 0) : Irrational (exp r) := by
  have : ∀ k : ℤ, k > 0 → Irrational (exp k) := by
    sorry
  sorry

open Real

theorem Theorem_2 (r : ℚ) (h_r : r ≠ 0) : Irrational (π ^ 2) := by
  sorry

theorem Theorem_3 (n : ℕ) (h_n : n ≥ 3) : Irrational ( arccos (1 / (n : ℝ).sqrt) / π) := by
  sorry


end irrational
end book
