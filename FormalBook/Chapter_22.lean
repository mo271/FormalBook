/-
Copyright 2024 the Amsterdam Lean seminar

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching,
Maris Ozols,
Jan Hendriks,
Casper,
Pjotr Buys,
Giacomo Grevink,
Dion Leijnse,
Thijs Maessen,
Thomas Koopman,
Jonas van der Schaaf,
Lenny Taelman,
Dhyan Aranha.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Valuation.Basic
open BigOperators

/-!
# One square and an odd number of triangles
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- First we define the inductive type Rainbow, which will be the the target type of the painter
-- function. The painter function will take a point in ℝ² and return a color from Rainbow (eg. Red
-- Blue or Green).

inductive Rainbow
| Red
| Green
| Blue

--Now we define the painter function as appears in the Book.

def painter (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀) :
ℝ² → Rainbow
| X => if v (X 0) < v (1) ∧ v (X 1) < v 1 then Rainbow.Red
  else if v (X 0) < v (X 1) ∧ v (X 1) ≥ v 1 then Rainbow.Green
  else Rainbow.Blue

-- The next two lemmas below basically unravel the definition of the painter function which will
-- be of use in the proof of the lemma on the boundedness of the determinant.

lemma painted_green (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
 (X : ℝ²) : painter Γ₀ locg v X = Rainbow.Green → v (X 1) ≥  v (1) := by
  intro h
  simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
  -- I want to get rid of this simp with an unfold but if I do this then split_ifs stops working.
  split_ifs at h with h1 h2
  rcases h2 with ⟨p,  q⟩
  rw [v.map_one]
  exact q

-- the next lemma should be a cousin? of push_neg but I couldn't get what was in mathlib to work so
-- I just did it by hand.

lemma dist_negation_over_and (P Q : Prop): ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ


lemma painted_blue (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X : ℝ²) : painter Γ₀ locg v X = Rainbow.Blue → v (X 0) ≥ v (1) := by
intro h
simp only [painter, Fin.isValue, map_one, ge_iff_le] at h
--again here we want to get rid of the simp with an unfold but then split_ifs stops working.
split_ifs at h with h1 h2
rw [dist_negation_over_and] at h1
rw [dist_negation_over_and] at h2
cases' h1 with p q
rw [not_lt] at p
rw [v.map_one]
apply p
cases' h2 with m n
·  rw [not_lt] at m
   rw [not_lt, ← v.map_one] at q
   exact le_trans q m

·  rw [not_lt] at q
   contradiction


-- Now we come the first main lemma of the chapter.


lemma bounded_det (Γ₀ : Type) (locg : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation ℝ Γ₀)
(X Y Z : ℝ²) (hb: painter Γ₀ locg v X = Rainbow.Blue )(hg: painter Γ₀ locg v Y = Rainbow.Green)
(hr: painter Γ₀ locg v Z = Rainbow.Red) :
v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) ≥ 1 := by

have h₁1 : v (X 0) ≥ v 1 := painted_blue Γ₀ locg v X hb
have h₁2 : v (Y 1) ≥ v 1 := painted_green Γ₀ locg v Y hg
have h₁3: v (X 0 * Y 1) = v (X 0) * v (Y 1) := by rw [v.map_mul]
have h₁4: v (X 0 * Y 1) ≥ v 1 * v 1 := by
  rw [h₁3]
  apply mul_le_mul' h₁1 h₁2
simp at h₁4

sorry








/-## TODO
  - Monsky's Theorem
    - proof
inducrtive
      - Lemma 1
        - proof
      - Corollary
        - proof
      - Lemma 2
        - proof
          - (A)
          - (B)
  - Appendix: Extending valuations
    - definition
    - Theorem
      - proof
    - Lemma
      - proof
    - Claim
    - Zorn's Lemma
-/
