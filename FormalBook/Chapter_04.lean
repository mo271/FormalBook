/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
    · exact Or.inl rfl
    · exact Or.inr rfl
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

omit hk in
lemma S_lower_bound {x y z : ℤ} (h : ⟨x, y, z⟩ ∈ S k) : 0 < x ∧ 0 < y  := ⟨h.2.1, h.2.2⟩

omit hk in
lemma S_upper_bound {x y z : ℤ} (h : ⟨x, y, z⟩ ∈ S k) :
    x ≤ k ∧ y ≤ k := by
  obtain ⟨_, _⟩ := S_lower_bound k h
  simp [S, mem_setOf_eq] at h
  refine ⟨?_, ?_⟩
  all_goals try nlinarith

-- todo use Fin 2 instead of ({(0 : ℤ), 1})
/-- Embedding of the set `S k` into a finite product of finite sets for `Fintype` instance. -/
def embed_S : S k → Ioc (0 : ℤ) k ×ˢ Ioc (0 : ℤ) k ×ˢ ({(0 : ℤ), 1}) :=
  fun  (⟨⟨x, y, z⟩, h⟩ : S k) ↦ by
  have lb := S_lower_bound k h
  have ub := S_upper_bound k h
  exact ⟨⟨x, y, if 0 ≤ z then 1 else 0⟩, ⟨⟨lb.1, ub.1⟩, ⟨lb.2, ub.2⟩, by
    simp; exact
    Int.lt_or_le z 0 ⟩⟩

omit hk in
lemma embed_S_injective : Function.Injective (embed_S k):= by
  intro s1 s2 hS
  simp [embed_S] at hS
  ext
  · exact hS.1
  · exact hS.2.1
  · have := hS.2.2
    have ⟨⟨x1, y1, z1⟩, ⟨h1, _, _⟩⟩ := s1
    have ⟨⟨x2, y2, z2⟩, ⟨h2, _, _⟩⟩ := s2
    have hz_eq_z: z1 ^ 2 = z2 ^ 2 := by
      nlinarith
    simp at this
    by_cases hz1 : 0 ≤ z1
    · simp [hz1] at this
      by_cases hz2 : 0 ≤ z2
      · nlinarith
      · simp [hz2] at this
    · by_cases hz2 : 0 ≤ z2
      · simp [hz2] at this
        tauto
      · nlinarith

noncomputable instance : Fintype (S k) := by
  refine' Fintype.ofInjective (embed_S k) (embed_S_injective k)

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
  simp [linearInvo]

theorem linearInvo_no_fixedPoints : IsEmpty (fixedPoints (linearInvo k)) := by
  simp only [isEmpty_subtype, mem_fixedPoints, Subtype.forall, Prod.forall]
  intro x y z h hfixed
  simp only [IsFixedPt, linearInvo, Subtype.mk.injEq, Prod.mk.injEq] at hfixed
  have : z = 0 := by linarith
  obtain ⟨h, _, _⟩ := h
  simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  apply_fun (· % 4) at h
  simp [mul_assoc, Int.add_emod] at h

/-- The subset of `S k` where `z` is positive. -/
def T : Set (S k) := {⟨(_, _, z), _⟩ : S k |  z > 0}

noncomputable instance : Fintype <| T k := by
  exact Fintype.ofFinite ↑(T k)

/-- The subset of `S k` where `x - y + z > 0`. -/
def U : Set (S k) := {⟨(x, y, z), _⟩ | (x - y) + z > 0}

noncomputable instance : Fintype <| U k := Fintype.ofFinite ↑(U k)

theorem sameCard : Fintype.card (U k) = Fintype.card (T k) := by
  sorry

/- 2. -/

/-- The function underlying the second involution. -/
def secondInvo_fun := fun ((x,y,z) : ℤ × ℤ × ℤ) ↦ (x - y + z, y, 2 * y - z)

/-- The second involution that we study is an involution on the set U. -/
def secondInvo : Function.End (U k) := fun ⟨⟨⟨x, y, z⟩, hS⟩, h⟩ =>
  ⟨⟨secondInvo_fun ⟨x, y, z⟩, by
  simp [S, secondInvo_fun] at *
  constructor
  · rw [← hS.1]; ring
  refine ⟨h, hS.2.2⟩
  ⟩, by
    simp only [U, gt_iff_lt, secondInvo_fun, Set.mem_setOf_eq]
    ring_nf
    exact hS.2.1⟩


/-- `secondInvo k` is indeed an involution. -/
theorem secondInvo_sq : secondInvo k ^ 2 = 1 := by
  change secondInvo k ∘ secondInvo k = id
  funext ⟨⟨x, y, z⟩, h⟩
  rw [comp_apply]
  simp only [secondInvo, secondInvo_fun, sub_sub_cancel, id_eq, Subtype.mk.injEq, Prod.mk.injEq,
    and_true]
  ring_nf

variable [hk : Fact (4 * k + 1).Prime]
theorem k_pos : 0 < k := by
  by_contra h
  simp at h
  rw [h] at hk
  simp at hk
  tauto


/-- The singleton containing `(k, 1, 1)`. -/
def singletonFixedPoint : Finset (U k) :=
  {⟨⟨(k, 1, 1), by
  simp [S]
  exact k_pos k ⟩, by
  simp [U]
  exact k_pos k⟩}

/-- Any fixed point of `secondInvo k` must be `(k, 1, 1)`. -/
theorem eq_of_mem_fixedPoints : fixedPoints (secondInvo k) = singletonFixedPoint k := by
  simp only [fixedPoints, IsFixedPt, secondInvo, secondInvo_fun,
    singletonFixedPoint, Prod.mk_one_one, Finset.coe_singleton]
  ext t
  constructor
  · intro ht
    simp at ht
    sorry
  · aesop

/-- `secondInvo k` has exactly one fixed point. -/
theorem card_fixedPoints_eq_one : Fintype.card (fixedPoints (secondInvo k)) = 1 := by
  simp only [eq_of_mem_fixedPoints, singletonFixedPoint]
  rfl

theorem card_T_odd : Odd <| Fintype.card <| T k := by
  sorry

/- 3. -/
/-- The third, trivial, involution `(x, y, z) ↦ (y, x, z)`. -/
def trivialInvo : Function.End (T k) := fun ⟨⟨⟨x, y, z⟩, ⟨h, hx, hy⟩⟩, hz⟩ => ⟨⟨⟨y, x, z⟩, by
  exact ⟨by rw [← h,Int.mul_assoc, Int.mul_comm y x, Int.mul_assoc], hy, hx⟩⟩, hz⟩

omit hk in
theorem trivialInvo_apply (x y z : ℤ) (hS : ⟨x, y, z⟩ ∈ S k) (hT : ⟨⟨x, y, z⟩ , hS⟩ ∈ T k)
  (hS' : ⟨y, x, z⟩ ∈ S k) (hT' : ⟨⟨y, x, z⟩ , hS'⟩ ∈ T k) :
  trivialInvo k ⟨⟨⟨x, y, z⟩, hS⟩, hT⟩ = ⟨⟨⟨y,x,z⟩, hS'⟩, hT'⟩ := by
    simp [trivialInvo]
    aesop

omit hk in
/-- If `trivialInvo k` has a fixed point, a representation of `4 * k + 1` as a sum of two squares
can be extracted from it. -/
theorem sq_add_sq_of_nonempty_fixedPoints (hn : (fixedPoints (trivialInvo k)).Nonempty) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  simp only [sq]
  obtain ⟨⟨⟨⟨x, y, z⟩, hS⟩, hT⟩, hf⟩ := hn
  have hf := mem_fixedPoints_iff.mp hf
  simp only [ Subtype.mk.injEq, Prod.mk.injEq, true_and] at hf
  have : (trivialInvo k ⟨⟨(x, y, z), hS⟩, hT⟩).1.1 = (⟨⟨(x, y, z), hS⟩, hT⟩ : T k).1.1 := by
    rw [hf]
  simp at this
  rw [trivialInvo_apply] at this
  · simp at this
    use (2 * y), z
    rw [show 2 * y * (2 * y) = 4 * y * y by linarith, ← hS.1]
    congr
    · exact this.1
    · ring
  --TODO: avoid repeating from the definition of trivialInvo here!
  · exact ⟨by rw [← hS.1,Int.mul_assoc, Int.mul_comm y x, Int.mul_assoc], hS.2.2, hS.2.1⟩
  · exact hT



theorem trivialInvo_fixedPoints : (fixedPoints (trivialInvo k)).Nonempty := by sorry

end Involutions

theorem theorem₂ {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rw [← div_add_mod p 4, hp] at h ⊢
  let k := p / 4
  have ⟨a, b, h⟩ := sq_add_sq_of_nonempty_fixedPoints k <| trivialInvo_fixedPoints k
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  zify
  simpa only [sq_abs] using h


-- The windged square of area 4xy + z^2 = 73 that corresponds to (x,y,z) = (3,4,5)

/-- An example triple in `S k` for `k = 18` (so `4 * k + 1 = 73`). -/
def xyz := ((3, 5, 4) : ℤ × ℤ × ℤ)

/-- Convert a triple of integers to a `WindmillTriple` for visualization. -/
def toTriple := fun (xyz : ℤ × ℤ × ℤ) ↦
    (some <|  {x := xyz.1.natAbs, y := xyz.2.1.natAbs, z := xyz.2.2.natAbs} : Option WindmillTriple)

#widget WindmillWidget with ({ triple? :=toTriple xyz, mirror := true} : WindmillWidgetProps)

-- ... and its winged shape

#widget WindmillWidget with ({ triple? := (toTriple xyz),
                               colors? := greyColors,
                               mirror := true} : WindmillWidgetProps)

-- The second winged derived from the windeg shape of are 73 using `secondInvo`:

#eval secondInvo_fun xyz

#widget WindmillWidget with ({triple? := (toTriple <| secondInvo_fun xyz)} : WindmillWidgetProps)
