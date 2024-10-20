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
import FormalBook.Widgets.Windmill

/-!
# Representing numbers as sums of two squares

## TODO
  - Lemma 1
    - statement
    - proof
  - Lemma 2
    - statement
    - proof
  Proposition
    - statement
    - first proof
    - second proof
      - 1.
      - 2.
      - 3.
    - third proof
  Theorem
    - statement
    - proof
      - (1)
      - (2)
      - (3)
      - (4)
      - (5)
-/


namespace ch04

open Nat

lemma lemma₁ {p : ℕ} [h : Fact p.Prime] :
    let num_solutions := Finset.card { s : ZMod p | s ^ 2 = - 1 }
    (∃ m, p = 4 * m + 1 → num_solutions = 2) ∧
    (p = 2 → num_solutions = 1) ∧
    (∃ m, p = 4 * m + 1 → num_solutions = 0) := by
  constructor
  · sorry
  · constructor
    · intro hp
      -- TODO: figure out how to easily write `use 1` here to follow more closely the book
      aesop
    · sorry

-- TODO: golf, and perhaps make it even close to book proof
lemma lemma₂ (n m : ℕ) (hn : n = 4 * m + 3) :
  ¬ ∃ a b, n = a ^2 + b ^2 := by
  push_neg
  intro a b
  by_contra h
  have : (n : ZMod 4) =  a ^ 2 + b ^ 2 := by
    rw [h]
    simp only [Nat.cast_add, Nat.cast_pow]
  rw [hn] at this
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
  rw [mul_eq_zero_of_left (by rfl) (m : ZMod 4), zero_add] at this
  have hx : ∀ (x : ZMod 4),  x ^2 ∈ ({0, 1} : Finset (ZMod 4)) := by
    intro x
    fin_cases x <;> simp
    · left
      rfl
    · right
      rfl
  have ha := hx <| a
  have hb := hx  <| b
  generalize hA: (a : ZMod 4) ^ 2 = A
  generalize hB: (b : ZMod 4) ^ 2 = B
  rw [hA, hB] at this
  rw [hA] at ha
  rw [hB] at hb
  fin_cases A <;> fin_cases B <;> norm_num at this <;> tauto

-- We follow a similar path taken by Jeremy Tan and Thomas Browning in
-- mathlib4/Archive/ZagierTwoSquares.lean.

theorem theorem₁  {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  sorry

section Sets

open Set

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- We study the set S -/
def S : Set (ℤ × ℤ × ℤ) := {((x, y, z) : ℤ × ℤ × ℤ) | 4 * x * y + z ^ 2 = 4 * k + 1 ∧ x > 0 ∧ y > 0}

noncomputable instance : Fintype (S k) := by
  sorry

end Sets

section Involutions

open Function

variable (k : ℕ)

/- 1. -/

/-- The linear involution `(x, y, z) ↦ (y, x, -z)`. -/
def linearInvo : Function.End (S k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨y, x, -z⟩, by
  simp only [S, Set.mem_setOf_eq] at h ⊢
  exact ⟨by linarith [h], h.2.2, h.2.1⟩ ⟩

theorem linearInvo_sq : linearInvo k ^2  = (1 : Function.End (S k)) := by
  change linearInvo k ∘ linearInvo k = id
  funext x
  simp only [linearInvo, comp_apply, neg_neg, Prod.mk.eta, Subtype.coe_eta]
  rfl

theorem linearInvo_no_fixedPoints : IsEmpty (fixedPoints (linearInvo k)) := by
  simp
  intro x y z h
  intro hfixed
  simp only [IsFixedPt, linearInvo, Subtype.mk.injEq, Prod.mk.injEq] at hfixed
  have : z = 0 := by linarith
  obtain ⟨h, _, _⟩ := h
  simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  apply_fun (· % 4) at h
  simp [mul_assoc, Int.add_emod] at h

def T : Set (ℤ × ℤ × ℤ) := {((x, y, z) : ℤ × ℤ × ℤ) | (x,y,z) ∈ S k ∧ z > 0}

noncomputable instance : Fintype <| T k := by
  sorry

def U : Set (ℤ × ℤ × ℤ) := {((x, y, z) : ℤ × ℤ × ℤ) | (x,y,z) ∈ S k ∧ (x - y) + z > 0}

noncomputable instance : Fintype <| U k := by
  sorry

theorem sameCard : Fintype.card (U k) = Fintype.card (T k) := by
  sorry

/- 2. -/

def secondInvo_fun := fun ((x,y,z) : ℤ × ℤ × ℤ) ↦ (x - y + z, y, 2 * y - z)

/-- The second involution that we study is an involution on the set U. -/
def secondInvo : Function.End (U k) := fun ⟨⟨x, y, z⟩, h⟩ =>
  ⟨secondInvo_fun (x, y, z), by
  obtain ⟨hS, h⟩ := h
  simp [U]
  simp [S, secondInvo_fun] at *
  constructor
  · constructor
    · rw [← hS.1]
      ring_nf
    constructor
    · exact h
    · exact hS.2.2
  linarith⟩

/-- `complexInvo k` is indeed an involution. -/
theorem secondInvo_sq : secondInvo k ^ 2 = 1 := by
  change secondInvo k ∘ secondInvo k = id
  funext ⟨⟨x, y, z⟩, h⟩
  rw [comp_apply]
  simp only [secondInvo, secondInvo_fun, sub_sub_cancel, id_eq, Subtype.mk.injEq, Prod.mk.injEq,
    and_true]
  ring

variable [hk : Fact (4 * k + 1).Prime]
theorem k_pos : 0 < k := by
  by_contra h
  simp at h
  rw [h] at hk
  simp at hk
  tauto



/-- The singleton containing `(1, 1, k)`. -/
def singletonFixedPoint : Finset (U k) :=
  {⟨(k, 1, 1), ⟨by
    simp [S]
    exact k_pos k,
    by
    simp
    exact k_pos k⟩⟩}

/-- Any fixed point of `complexInvo k` must be `(1, 1, k)`. -/
theorem eq_of_mem_fixedPoints : fixedPoints (secondInvo k) = singletonFixedPoint k := by
  simp only [fixedPoints, IsFixedPt, secondInvo, secondInvo_fun,
    singletonFixedPoint, Prod.mk_one_one, Finset.coe_singleton]
  ext t
  constructor
  · intro ht
    simp at ht
    sorry
  · aesop

/-- `complexInvo k` has exactly one fixed point. -/
theorem card_fixedPoints_eq_one : Fintype.card (fixedPoints (secondInvo k)) = 1 := by
  simp only [eq_of_mem_fixedPoints, singletonFixedPoint]
  rfl

theorem card_T_odd : Odd <| Fintype.card <| T k := by
  sorry

/- 3. -/
/- The third, trivial, involution `(x, y, z) ↦ (x, z, y)`. -/
def trivialInvo : Function.End (T k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨y, x, z⟩, by
  simp [T, S] at *
  obtain ⟨⟨h, hx, hy⟩, hz⟩ := h
  exact ⟨⟨by
    rw [← h]
    ring, hy, hx⟩, hz⟩
  ⟩

/-- If `trivialInvo k` has a fixed point, a representation of `4 * k + 1` as a sum of two squares
can be extracted from it. -/
theorem sq_add_sq_of_nonempty_fixedPoints (hn : (fixedPoints (trivialInvo k)).Nonempty) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  simp only [sq]
  obtain ⟨⟨⟨x, y, z⟩, he⟩, hf⟩ := hn
  have := mem_fixedPoints_iff.mp hf
  simp only [trivialInvo, Subtype.mk.injEq, Prod.mk.injEq, true_and] at this
  simp only [T, S, Set.mem_setOf_eq] at he
  simp [IsFixedPt, trivialInvo] at hf
  use (2 * y), z
  rw [show 2 * y * (2 * y) = 4 * y * y by linarith, ← he.1.1]
  rw [hf.2]
  ring

theorem trivialInvo_fixedPoints : (fixedPoints (trivialInvo k)).Nonempty := by sorry

end Involutions

theorem theorem₂ {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rw [← div_add_mod p 4, hp] at h ⊢
  let k := p / 4
  have ⟨a, b, h⟩ := sq_add_sq_of_nonempty_fixedPoints k <| trivialInvo_fixedPoints k
  use a.natAbs
  use b.natAbs
  unfold k at h
  zify
  simpa only [sq_abs] using h



-- The windged sqaure of area 4xy + z^2 = 73 that corresponds to (x,y,z) = (3,4,5)

def xyz := ((4, 3, 5) : ℤ × ℤ × ℤ)

def toTriple := fun (xyz : ℤ × ℤ × ℤ) ↦
    (some <|  {x := xyz.1.natAbs, y := xyz.2.1.natAbs, z := xyz.2.2.natAbs} : Option WindmillTriple)

#widget WindmillWidget with ({ triple? :=toTriple xyz, mirror := true} : WindmillWidgetProps )

-- ... and its winged shape

#widget WindmillWidget with ({ triple? := (toTriple xyz), colors? := greyColors, mirror := true} : WindmillWidgetProps)

-- The second winged derived from the windeg shape of are 73 using `secondInvo`:

#eval secondInvo_fun xyz

#widget WindmillWidget with ({triple? := (toTriple <| secondInvo_fun xyz)} : WindmillWidgetProps)
