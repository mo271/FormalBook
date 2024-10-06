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
/-!
# Pigeon-hole and double counting

## TODO
  - statement
  - 1. Numbers
    - Claim
    - Claim
  - 2. Sequences
    - Claim
      - proof
  - 3. Sums
    - Claim
  - Double Counting
  - 4. Numbers again
  - 5. Graphs
    - Theorem
      - proof
    - Claim
  - 6. Sperner's Lemma
    - proof
    - Proof of Brouwer's fixed point theorem (for $n = 2$)
-/

theorem pigeon_hole_principle (n r : ℕ) (h : r < n) (object_to_boxes : Fin n → Fin r) :
  ∃ box : Fin r, ∃ object₁ object₂ : Fin n,
  object₁ ≠ object₂ ∧
  object_to_boxes object₁ = box ∧
  object_to_boxes object₂ = box := by
  have ⟨object₁, object₂, h_object⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt object_to_boxes (by convert h <;> simp)
  use object_to_boxes object₁
  use object₁
  use object₂
  tauto
