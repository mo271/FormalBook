/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import FormalBook.Mathlib.EdgeFinset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

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

namespace chapter28

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



variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v

lemma handshaking : ∑ v, d(v) = 2 * #E := by
  calc  ∑ v, d(v)
    _ = ∑ v, #I(v)             := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v, #{e ∈ E | v ∈ e}  := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ E, #{v | v ∈ e}  := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ e ∈ E, 2             := Finset.sum_congr rfl (λ e he ↦ (G.card_filter_mem_of_mem_edgeFinset e he))
    _ = 2 * ∑ e ∈ E, 1         := (Finset.mul_sum E (λ _ ↦ 1) 2).symm
    _ = 2 * #E                 := by rw [Finset.card_eq_sum_ones E]

end chapter28
