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
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import FormalBook.Mathlib.EdgeFinset

/-!
# Buffon's needle problem

## TODO
  - statement
    - proof
-/

section HandshakingLemma

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

lemma handshaking : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  calc  ∑ v, G.degree v
    _ = ∑ v, (G.incidenceFinset v).card              := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v, {e ∈ G.edgeFinset | v ∈ e}.card         := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ G.edgeFinset, Finset.card {v | v ∈ e}  := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ e ∈ G.edgeFinset, 2                        := Finset.sum_congr rfl (λ e he ↦ (G.card_filter_mem_of_mem_edgeFinset e he))
    _ = 2 * ∑ e ∈ G.edgeFinset, 1                    := (Finset.mul_sum G.edgeFinset (λ _ ↦ 1) 2).symm
    _ = 2 * G.edgeFinset.card                        := by rw [Finset.card_eq_sum_ones G.edgeFinset]

end HandshakingLemma
