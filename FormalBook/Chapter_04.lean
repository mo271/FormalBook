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
  ¬ ∃ a b, n = a ^ 2 + b ^ 2 := by
  intro ⟨a, b, h⟩
  have : (n : ZMod 4) = a ^ 2 + b ^ 2 := by
    rw [h]
    simp only [Nat.cast_add, Nat.cast_pow]
  rw [hn] at this
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
  rw [mul_eq_zero_of_left (by rfl) (m : ZMod 4), zero_add] at this
  have h_mod : ∀ (x y : ZMod 4), (3 : ZMod 4) ≠ x ^ 2 + y ^ 2 := by decide
  exact h_mod a b this

-- We follow a similar path taken by Jeremy Tan and Thomas Browning in
-- mathlib4/Archive/ZagierTwoSquares.lean.

theorem theorem₁ {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  sorry

section Sets

open Set

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- We study the set S -/
def S : Set (ℤ × ℤ × ℤ) := {((x, y, z) : ℤ × ℤ × ℤ) | 4 * x * y + z ^ 2 = 4 * k + 1 ∧ x > 0 ∧ y > 0}

omit hk in
lemma S_lower_bound {x y z : ℤ} (h : ⟨x, y, z⟩ ∈ S k) : 0 < x ∧ 0 < y := ⟨h.2.1, h.2.2⟩

omit hk in
lemma S_upper_bound {x y z : ℤ} (h : ⟨x, y, z⟩ ∈ S k) :
    x ≤ k ∧ y ≤ k := by
  obtain ⟨_, _⟩ := S_lower_bound k h
  simp [S] at h
  refine ⟨?_, ?_⟩
  all_goals try nlinarith

-- todo use Fin 2 instead of ({(0 : ℤ), 1})
/-- Embedding of the set `S k` into a finite product of finite sets for `Fintype` instance. -/
@[nolint defsWithUnderscore]
def embed_S : S k → Ioc (0 : ℤ) k ×ˢ Ioc (0 : ℤ) k ×ˢ ({(0 : ℤ), 1}) :=
  fun (⟨⟨x, y, z⟩, h⟩ : S k) ↦ by
  have lb := S_lower_bound k h
  have ub := S_upper_bound k h
  exact ⟨⟨x, y, if 0 ≤ z then 1 else 0⟩, ⟨⟨lb.1, ub.1⟩, ⟨lb.2, ub.2⟩, by
    simp; exact
    Int.lt_or_le z 0 ⟩⟩

omit hk in
lemma embed_S_injective : Function.Injective (embed_S k) := by
  intro ⟨⟨x1, y1, z1⟩, h1⟩ ⟨⟨x2, y2, z2⟩, h2⟩ hS
  have h_val := congr_arg Subtype.val hS
  simp only [embed_S, Prod.mk.injEq] at h_val
  obtain ⟨rfl, rfl, hz⟩ := h_val
  have hz_sq : z1 ^ 2 = z2 ^ 2 := by
    have h1_eq := h1.1
    have h2_eq := h2.1
    linarith
  have hz_eq : z1 = z2 := by
    split_ifs at hz with hz1 hz2
    · nlinarith
    · linarith
    · linarith
    · nlinarith
  subst hz_eq
  rfl

noncomputable instance : Fintype (S k) := by
  refine' Fintype.ofInjective (embed_S k) (embed_S_injective k)

end Sets

section Involutions

open Function

variable (k : ℕ)

/- 1. -/

/-- The linear involution `(x, y, z) ↦ (y, x, -z)`. -/
def linearInvo : Function.End (S k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨y, x, -z⟩, by
  simp only [S, Set.mem_ofPred_eq] at h ⊢
  exact ⟨by linarith [h], h.2.2, h.2.1⟩ ⟩

theorem linearInvo_sq : linearInvo k ^ 2 = (1 : Function.End (S k)) := by
  change linearInvo k ∘ linearInvo k = id
  funext ⟨⟨x, y, z⟩, h⟩
  rw [show (linearInvo k ∘ linearInvo k) ⟨(x, y, z), h⟩ =
      linearInvo k (linearInvo k ⟨(x, y, z), h⟩) from rfl]
  apply Subtype.ext
  dsimp [linearInvo]
  ext <;> simp

theorem linearInvo_no_fixedPoints : IsEmpty (fixedPoints (linearInvo k)) := by
  simp only [isEmpty_subtype, Subtype.forall, Prod.forall]
  intro x y z h hfixed
  have hfixed' : (linearInvo k ⟨⟨x, y, z⟩, h⟩).1.2.2 = z := by rw [hfixed]
  have : -z = z := hfixed'
  have : z = 0 := by linarith
  obtain ⟨h, _, _⟩ := h
  simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  apply_fun (· % 4) at h
  simp [mul_assoc, Int.add_emod] at h

/-- The subset of `S k` where `z` is positive. -/
def T : Set (S k) := {⟨(_, _, z), _⟩ : S k | z > 0}

noncomputable instance : Fintype <| T k := by
  exact Fintype.ofFinite ↑(T k)

/-- The subset of `S k` where `x - y + z > 0`. -/
def U : Set (S k) := {⟨(x, y, z), _⟩ | (x - y) + z > 0}

noncomputable instance : Fintype <| U k := Fintype.ofFinite ↑(U k)
noncomputable instance (s : Set (U k)) : Fintype s := Fintype.ofFinite s

theorem sameCard : Fintype.card (U k) = Fintype.card (T k) := by
  sorry

/- 2. -/

/-- The function underlying the second involution. -/
@[nolint defsWithUnderscore]
def secondInvo_fun := fun ((x,y,z) : ℤ × ℤ × ℤ) ↦ (x - y + z, y, 2 * y - z)

/-- The second involution that we study is an involution on the set U. -/
def secondInvo : Function.End (U k) := fun ⟨⟨⟨x, y, z⟩, hS⟩, h⟩ =>
  ⟨⟨secondInvo_fun ⟨x, y, z⟩, by
  simp [S, secondInvo_fun] at *
  constructor
  · rw [← hS.1]; ring
  refine ⟨h, hS.2.2⟩
  ⟩, by
    simp only [U, gt_iff_lt, secondInvo_fun, Set.mem_ofPred_eq]
    ring_nf
    exact hS.2.1⟩


/-- `secondInvo k` is indeed an involution. -/
theorem secondInvo_sq : secondInvo k ^ 2 = 1 := by
  change secondInvo k ∘ secondInvo k = id
  funext ⟨⟨⟨x, y, z⟩, hS⟩, h⟩
  rw [show (secondInvo k ∘ secondInvo k) ⟨⟨(x, y, z), hS⟩, h⟩ =
      secondInvo k (secondInvo k ⟨⟨(x, y, z), hS⟩, h⟩) from rfl]
  apply Subtype.ext
  apply Subtype.ext
  dsimp [secondInvo, secondInvo_fun]
  ext
  · ring
  · rfl
  · ring

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
  have : fixedPoints (secondInvo k) = (singletonFixedPoint k : Set (U k)) := eq_of_mem_fixedPoints k
  rw [this]
  simp [singletonFixedPoint]

theorem card_T_odd : Odd <| Fintype.card <| T k := by
  sorry

/- 3. -/
/-- The third, trivial, involution `(x, y, z) ↦ (y, x, z)`. -/
def trivialInvo : Function.End (T k) := fun ⟨⟨⟨x, y, z⟩, hS⟩, hz⟩ => ⟨⟨⟨y, x, z⟩, by
  obtain ⟨h, hx, hy⟩ := hS
  exact ⟨by rw [← h, Int.mul_assoc, Int.mul_comm y x, Int.mul_assoc], hy, hx⟩⟩, hz⟩

omit hk in
theorem trivialInvo_apply (x y z : ℤ) (hS : ⟨x, y, z⟩ ∈ S k) (hT : ⟨⟨x, y, z⟩ , hS⟩ ∈ T k)
  (hS' : ⟨y, x, z⟩ ∈ S k) (hT' : ⟨⟨y, x, z⟩ , hS'⟩ ∈ T k) :
  trivialInvo k ⟨⟨⟨x, y, z⟩, hS⟩, hT⟩ = ⟨⟨⟨y,x,z⟩, hS'⟩, hT'⟩ := rfl

omit hk in
/-- If `trivialInvo k` has a fixed point, a representation of `4 * k + 1` as a sum of two squares
can be extracted from it. -/
theorem sq_add_sq_of_nonempty_fixedPoints (hn : (fixedPoints (trivialInvo k)).Nonempty) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  obtain ⟨⟨⟨⟨x, y, z⟩, hS⟩, hT⟩, hf⟩ := hn
  have hf' : (trivialInvo k ⟨⟨⟨x, y, z⟩, hS⟩, hT⟩).1.1.1 = (⟨⟨⟨x, y, z⟩, hS⟩, hT⟩ : T k).1.1.1 := by
    rw [hf]
  have h_eq : y = x := hf'
  use 2 * y, z
  have hS1 := hS.1
  subst h_eq
  linear_combination hS1

theorem trivialInvo_fixedPoints : (fixedPoints (trivialInvo k)).Nonempty := by sorry

end Involutions

theorem theorem₂ {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have hk : Fact (4 * (p / 4) + 1).Prime := ⟨by
    have : 4 * (p / 4) + 1 = p := by omega
    rw [this]
    exact h.out⟩
  have ⟨a, b, h_sq⟩ := sq_add_sq_of_nonempty_fixedPoints (p / 4) (trivialInvo_fixedPoints (p / 4))
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  have hp_eq : p = 4 * (p / 4) + 1 := by omega
  rw [hp_eq]
  zify
  simp only [sq_abs]
  exact h_sq


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

-- #eval secondInvo_fun xyz

#widget WindmillWidget with ({triple? := (toTriple <| secondInvo_fun xyz)} : WindmillWidgetProps)
