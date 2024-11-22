/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.Polynomial
open Complex Polynomial

/-!
# The fundamental theorem of algebra

## TODO
  - compare analysis.complex.polynomial
  - statment
    - proof
      - (A)
      - (B)
      - (C)
    - Lemma
      - proof
-/

def Polynomial.constant (f : Polynomial ℂ) : Prop := (0 < degree f)

theorem fundamental_theorem_of_algebra (f : Polynomial ℂ) (h : ¬ Polynomial.constant f) :
  ∃ z : ℂ, IsRoot f z := by
  rw [Polynomial.constant] at h
  sorry
