import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

-- https://github.com/leanprover-community/mathlib4/pull/17587


section Mathlib.Data.Sym.Sym2

namespace Sym2

variable {α : Type*}

theorem exists_eq (z : Sym2 α) : ∃ x y, z = s(x, y) :=
  z.ind fun x y => ⟨x, y, rfl⟩

@[simp] theorem setOf_mem_eq {z : Sym2 α} : {v | v ∈ z} = z := rfl

@[simp] theorem coe_mk_eq {x y : α} : (s(x, y) : Set α) = {x, y} := by
  ext; simp

theorem isDiag_iff_exists {z : Sym2 α} : z.IsDiag ↔ ∃ x, z = s(x, x) := by
  induction z; rw [mk_isDiag_iff]; simp [eq_comm]

theorem not_isDiag_iff_exists {z : Sym2 α} : ¬ z.IsDiag ↔ ∃ x y, x ≠ y ∧ z = s(x, y) := by
  induction z with | _ x y =>
  rw [mk_isDiag_iff, not_iff_comm]
  push_neg
  constructor
  · intro h; simpa using h x y
  · aesop

@[coe]
protected def toMultiset (z : Sym2 α) : Multiset α :=
  Sym2.lift ⟨fun x y => {x, y}, Multiset.pair_comm⟩ z

instance : Coe (Sym2 α) (Multiset α) := ⟨Sym2.toMultiset⟩

@[simp] lemma toMultiset_mk {x y : α} : (s(x, y) : Multiset α) = {x, y} := rfl

variable [DecidableEq α]

@[coe]
protected def toFinset (z : Sym2 α) : Finset α := Multiset.toFinset z

instance : Coe (Sym2 α) (Finset α) := ⟨Sym2.toFinset⟩

@[simp] lemma toFinset_mk {x y : α} : (s(x, y) : Finset α) = {x, y} := by
  ext; rw [Sym2.toFinset, Sym2.toMultiset]; simp

@[simp] lemma toFinset_toMultiset {s : Sym2 α} : (s : Multiset α).toFinset = (s : Finset α) := rfl

@[simp] lemma mem_toFinset {z : Sym2 α} {x : α} : x ∈ (z : Finset α) ↔ x ∈ z := by
  induction z; simp

@[simp] lemma coe_toFinset {z : Sym2 α} : ((z : Finset α) : Set α) = z := by
  ext; simp

lemma toFinset_eq [Fintype α] {e : Sym2 α} : (e : Finset α) = {v | v ∈ e}.toFinset := by
  ext; simp

lemma card_toFinset_of_isDiag {z : Sym2 α} (h : z.IsDiag) : (z : Finset α).card = 1 := by
  obtain ⟨x, rfl⟩ := isDiag_iff_exists.mp h
  simp [Finset.card_eq_one]

lemma card_toFinset_mk_of_ne {x y : α} (h : x ≠ y) : s(x, y).toFinset.card = 2 := by
  rw [Finset.card_eq_two]
  use x, y, h
  simp

lemma card_toFinset_of_not_isDiag {z : Sym2 α} (h : ¬z.IsDiag) : z.toFinset.card = 2 := by
  induction z with | _ x y => exact card_toFinset_mk_of_ne h

lemma one_le_card_toFinset {z : Sym2 α} : 1 ≤ z.toFinset.card := by
  induction z; simp

lemma card_toFinset_le_two {z : Sym2 α} : z.toFinset.card ≤ 2 := by
  by_cases z.IsDiag <;> simp [*, card_toFinset_of_isDiag, card_toFinset_of_not_isDiag]

end Sym2

end Mathlib.Data.Sym.Sym2



section Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [DecidableEq α]

lemma card_toFinset_of_mem_edgeSet (e : Sym2 α) (he : e ∈ G.edgeSet) :
    (e : Finset α).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag (not_isDiag_of_mem_edgeSet _ he)

lemma card_filter_mem_of_mem_edgeSet [Fintype α] (e : Sym2 α) (he : e ∈ G.edgeSet) :
    Finset.card {v | v ∈ e} = 2 := by
  rw [← SimpleGraph.card_toFinset_of_mem_edgeSet _ he]
  congr; ext; simp

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Basic



section Mathlib.Combinatorics.SimpleGraph.Finite

namespace SimpleGraph

variable {α : Type*} [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj] [DecidableEq α]

lemma card_toFinset_of_mem_edgeFinset (e : Sym2 α) (he : e ∈ G.edgeFinset) :
    (e : Finset α).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag (not_isDiag_of_mem_edgeSet _ (mem_edgeFinset.mp he))

lemma card_filter_mem_of_mem_edgeFinset (e : Sym2 α) (he : e ∈ G.edgeFinset) :
    Finset.card {v | v ∈ e} = 2 := by
  rw [← SimpleGraph.card_toFinset_of_mem_edgeFinset _ he]
  congr; ext; simp

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Finite
