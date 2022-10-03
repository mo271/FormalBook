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

Authors: Moritz Firsching
-/
import tactic
import data.real.basic
import data.complex.exponential
import analysis.calculus.iterated_deriv
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.trigonometric.inverse

open real (exp pi arccos)

open finset (Icc)
open_locale big_operators
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
def irrational (x : ℝ) := x ∉ set.range (coe : ℚ → ℝ)

/-- This is `irrational_iff_ne_rational` in mathlib. -/
lemma irrational_iff_not_fraction (x : ℝ) : irrational x ↔ ∀ a b : ℤ, x ≠ (a : ℝ) / b :=
begin
  sorry,
end


/-- We define abbreviations for Euler's and for Pi-/
noncomputable def e := exp 1
noncomputable def π := pi

/-- We want to use the series representation of the exponential function-/
theorem exponential_series (x : ℝ) : has_sum (λ n : ℕ, x ^ n / (n.factorial)) (real.exp x) :=
begin
  sorry,
end

/-!
## Some Proofs of irrationality
-/


theorem e_irrational : irrational e :=
begin
  sorry,
end

theorem e_pow_2_irrational : irrational (e ^ 2) :=
begin
  sorry,
end

/--
"For any `n ≥ 1` the integer `n!` contains the prime factor `2` at most `n − 1` times — with equality if
(and only if) `n` is a power of two, `n = 2 ^ m`."
-/
lemma little_lemma (n : ℕ) (h_n : n ≠ 0) :
  ¬ (2 ^ n ∣ n.factorial) ∧ (2 ^ (n - 1) ∣ n.factorial ↔ ∃ m : ℕ, n = 2 ^ m) :=
begin
  sorry,
end

theorem e_pow_4_irrational : irrational (e ^ 4) :=
begin
  sorry,
end

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

noncomputable def f_aux (n : ℕ) (x : ℝ) :=  x ^ n * (1 - x) ^ n / n.factorial

lemma lem_aux_i (n : ℕ) (x : ℝ) : ∃ c : ℕ → ℤ, f_aux n x = ∑ i in Icc n (2 * n), (c i) * x ^ i :=
begin
  sorry,
end

lemma lem_aux_ii (n : ℕ) (x : ℝ) (h_1 : 0 < x) (h_2 x < 0) :
  (0 < f_aux n x) ∧ (f_aux n x < (1 : ℝ) / n.factorial) :=
begin
  sorry,
end

/--
WARNING: There might be a better way to state this, not sure what the best API for derivatives of
smooth (polynomial) functions is
-/
lemma lem_aux_iii (n : ℕ) (k : ℕ): iterated_deriv k (f_aux n) 0 ∈  set.range (coe : ℚ → ℝ) ∧
  iterated_deriv k (f_aux n) 1 ∈ set.range (coe : ℚ → ℝ) :=
begin
  sorry,
end

/-! ### Theorems 1 to 3-/

/--For any non-zero rational number `r`, the exponential `e ^ r` is irrational.-/
theorem Theorem_1 (r : ℚ) (h_r : r ≠ 0) : irrational (exp r) :=
begin
  suffices : ∀ k : ℤ, k > 0 → irrational (exp k), by
  begin
    sorry,
  end,
  sorry,
end

theorem Theorem_2 (r : ℚ) (h_r : r ≠ 0) : irrational (π ^ 2) :=
begin
  sorry,
end

theorem Theorem_3 (n : ℕ) (h_n : n ≥ 3) : irrational ( arccos (1 / (n : ℝ).sqrt) / π) :=
begin
  sorry,
end


end irrational
end book
