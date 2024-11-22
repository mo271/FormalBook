/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
/-!
# Of friends and politicians

We are adapting the proof of from archive/100-theorems-list/83_friendship_graphs to follow the book
more closely
## TODO
  - proof
    - (1) The C₄ condition
    - (2) everyting after the eigenvalues
  - Kotzig's Conjecture
-/
namespace chapter44

open scoped Classical BigOperators

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R] variable [Fintype V]

variable (G : SimpleGraph V)



theorem friendship_theorem [Nonempty V]
    (h : ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  -- Suppose the assertion is false, and `G` is a counterexample.
  by_contra no_politician
  -- We proceed in two steps
  -- (1) We claim that G is a regular graph
  have lemma₁ :  ∃ k : ℕ, G.IsRegularOfDegree k := by
    sorry

  have ⟨k, hregular⟩ := lemma₁
  let n := Fintype.card V
  have eq₁ : n = k^2 - k  + 1 := by
    have : k + (n - 1) = k * k := by
      sorry
    rw [pow_two, this.symm]
    simp only [add_tsub_cancel_left]
    exact Nat.eq_add_of_sub_eq Fintype.card_pos rfl

  -- (2) The rest of the proof is a beautiful application of some stadard results of linear algebra.

  -- Note first that k must be greater than 2
  have : 2 < k := by
    by_contra hk
    rw [not_lt] at hk
    interval_cases k
    -- In case k = 0 or k = 1, we have G = K₁.
    repeat
      · simp at eq₁
        have v := Classical.arbitrary V
        simp at no_politician
        have ⟨x, hx⟩ := no_politician v
        have := hx.left
        have : 1 < Fintype.card V := by
          refine' Fintype.one_lt_card_iff.mpr _
          use v
          use x
        rw [(show Fintype.card V = n by rfl), eq₁] at this
        tauto
    -- In case k = 2, we have G = K₃
    · norm_num at eq₁
      have v := Classical.arbitrary V
      simp only [ne_eq, not_exists, not_forall, exists_prop] at no_politician
      have ⟨x, ⟨hx_left, hx_right⟩⟩ := no_politician v
      refine' hx_right _
      simp only [IsRegularOfDegree, degree] at hregular
      rw [← mem_neighborFinset]
      have := hregular v
      have : G.neighborFinset v = Finset.univ.erase v := by
        apply eq_of_subset_of_card_le
        · rw [Finset.subset_iff]
          intro x
          rw [mem_neighborFinset, Finset.mem_erase]
          exact fun h => ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
        convert_to 2 ≤ _
        · convert_to _ = Fintype.card V - 1
          · rw [(show Fintype.card V = n by rfl), eq₁]
          · exact Finset.card_erase_of_mem (Finset.mem_univ _)
        · rw [hregular]
      rw [this]
      -- x is a neighbor of v since they are distinct and there are only 3 vertices
      simp only [Finset.mem_erase, Finset.mem_univ]
      tauto


  -- Consider the adjacency matrix
  let A := G.adjMatrix ℝ
  have : (A ^ 2) = (k - 1) • (1 : Matrix V V ℝ) + of (fun _ _ => 1) := by sorry

  sorry
