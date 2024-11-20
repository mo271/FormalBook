/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Matrix.DoublyStochastic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
/-!
# Van der Waerden's permanent conjecture

## TODO
  - statement
    - proof
  - Gurvits' Proposition
  - proof
    - Claim 1
    - Claim 2
  - Lemma 1
    - proof
  - Lemma 2
    - proof
  - Proof of Gurvits' Proposition
    - Case 1
    - Case 2
    - Claim
  - Farkas Lemma
-/


open Equiv
namespace Matrix

variable {n : ℕ}


theorem permanent_conjecture (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ doublyStochastic ℝ (Fin n) → permanent M ≥ (n.factorial)/(n ^ n) := sorry
