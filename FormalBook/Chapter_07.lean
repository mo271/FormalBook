/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
