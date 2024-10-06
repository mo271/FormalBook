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
