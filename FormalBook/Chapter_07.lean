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
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!
# The spectral theorem and Hadamard's determinant problem

## TODO
  - statement Theorem 1.
    - proof
      - Lemma
        - (A)
        - (B)
        - (C)
  - The Hadamard determinant problem
  - Hadamard matreices esixt for all $n = 2^m$
  - Theorem 2.
-/

namespace chapter7

open Matrix

theorem Theorem₁ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : IsHermitian A) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
    Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
    ∃ (d : (Fin n) → ℝ), diagonal d = (Q.conjTranspose * A * Q) := by
  sorry


theorem Theorem₂ (n : ℕ) : ∃ (M : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, M i j = -1 ∨ M i j = 1) ∧
    M.det > Real.sqrt n.factorial := by
  sorry

end chapter7
