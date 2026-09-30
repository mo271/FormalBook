/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SumTwoSquares

public meta import FormalBook.Widgets.Windmill
import FormalBook.Widgets.Windmill

@[expose] public section

/-!
# Representing numbers as sums of two squares

This file formalizes Chapter 4 of *Proofs from THE BOOK*:

* `ch04.lemma₁` / `ch04.lemma₁_faithful` : Lemma 1 (solutions of `s ^ 2 = -1` in `ZMod p`);
* `ch04.lemma₂` : Lemma 2 (no number `4 * m + 3` is a sum of two squares);
* `ch04.theorem₁`, `ch04.theorem₂` : the Proposition (every prime `p ≡ 1 (mod 4)` is a sum of
  two squares); `theorem₂` follows Heath-Brown's / Zagier's proof with three involutions;
* `ch04.theorem₃` : the Theorem (characterization of the numbers that are sums of two squares).
-/


namespace ch04

open Nat

/-- In `ZMod 2`, the equation `s ^ 2 = -1` has exactly one solution. -/
lemma card_sq_eq_neg_one_zmod_two : Finset.card { s : ZMod 2 | s ^ 2 = - 1 } = 1 := by
  decide

/-- Lemma 1, *as originally stated in this file*.

Note: because of the placement of the existential quantifiers, the first and third conjuncts
are trivially true (take `m` with `p ≠ 4 * m + 1`). A faithful version of Lemma 1 is
`lemma₁_faithful` below. -/
lemma lemma₁ {p : ℕ} [h : Fact p.Prime] :
    let num_solutions := Finset.card { s : ZMod p | s ^ 2 = - 1 }
    (∃ m, p = 4 * m + 1 → num_solutions = 2) ∧
    (p = 2 → num_solutions = 1) ∧
    (∃ m, p = 4 * m + 1 → num_solutions = 0) := by
  refine ⟨⟨p, fun hp => by omega⟩, ?_, ⟨p, fun hp => by omega⟩⟩
  intro hp
  subst hp
  convert card_sq_eq_neg_one_zmod_two

/-- Lemma 1 (faithful version). For primes `p = 4 * m + 1` the equation `s ^ 2 = -1` has two
solutions in `ZMod p`, for `p = 2` it has one solution, and for primes `p = 4 * m + 3` it has
no solution. -/
lemma lemma₁_faithful {p : ℕ} [h : Fact p.Prime] :
    let num_solutions := Finset.card { s : ZMod p | s ^ 2 = - 1 }
    (p % 4 = 1 → num_solutions = 2) ∧
    (p = 2 → num_solutions = 1) ∧
    (p % 4 = 3 → num_solutions = 0) := by
  intro num_solutions
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨s, hs⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (show p % 4 ≠ 3 by omega)
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h2
      have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
      have := Nat.le_of_dvd (by norm_num) hd
      have := h.out.two_le
      omega
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    have hne : s ≠ -s := by
      intro hss
      apply hs0
      have : (2 : ZMod p) * s = 0 := by linear_combination hss
      exact (mul_eq_zero.mp this).resolve_left h2
    have hset : ({ t : ZMod p | t ^ 2 = - 1 } : Finset (ZMod p)) = {s, -s} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [hs, ← sq, sq_eq_sq_iff_eq_or_eq_neg]
    show Finset.card _ = 2
    rw [hset, Finset.card_pair hne]
  · subst hp
    show Finset.card _ = 1
    convert card_sq_eq_neg_one_zmod_two
  · have hns : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]; omega
    show Finset.card _ = 0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact hns ⟨t, by rw [← ht, sq]⟩

-- TODO: golf, and perhaps make it even close to book proof
/-- Lemma 2. No number `n = 4 * m + 3` is a sum of two squares. -/
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

/-- The Proposition: every prime of the form `4 * m + 1` is a sum of two squares.
Here we simply appeal to Mathlib; the book's involution proof is `theorem₂` below. -/
theorem theorem₁ {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq (by omega)

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
  obtain ⟨h, _, _⟩ := h
  refine ⟨?_, ?_⟩
  all_goals nlinarith

-- todo use Fin 2 instead of ({(0 : ℤ), 1})
/-- Embedding of the set `S k` into a finite product of finite sets for `Fintype` instance. -/
@[nolint defsWithUnderscore]
def embed_S : S k → Ioc (0 : ℤ) k ×ˢ Ioc (0 : ℤ) k ×ˢ ({(0 : ℤ), 1}) :=
  fun (⟨⟨x, y, z⟩, h⟩ : S k) ↦ by
  have lb := S_lower_bound k h
  have ub := S_upper_bound k h
  exact ⟨⟨x, y, if 0 ≤ z then 1 else 0⟩, ⟨⟨lb.1, ub.1⟩, ⟨lb.2, ub.2⟩, by
    split_ifs <;> simp⟩⟩

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
    · simp at hz
    · simp at hz
    · nlinarith
  subst hz_eq
  rfl

noncomputable instance : Fintype (S k) :=
  Fintype.ofInjective (embed_S k) (embed_S_injective k)

end Sets

section Involutions

open Function

variable (k : ℕ)

/- 1. -/

/-- The linear involution `(x, y, z) ↦ (y, x, -z)`. -/
def linearInvo : Function.End (S k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨y, x, -z⟩, by
  obtain ⟨h, hx, hy⟩ := h
  exact ⟨by rw [← h]; ring, hy, hx⟩ ⟩

theorem linearInvo_sq : linearInvo k ^ 2 = (1 : Function.End (S k)) := by
  change linearInvo k ∘ linearInvo k = id
  funext ⟨⟨x, y, z⟩, h⟩
  apply Subtype.ext
  change ((x, y, - -z) : ℤ × ℤ × ℤ) = (x, y, z)
  rw [neg_neg]

/-- There is no point of `S k` with `z = 0`. -/
lemma S_z_ne_zero {x y z : ℤ} (h : ⟨x, y, z⟩ ∈ S k) : z ≠ 0 := by
  rintro rfl
  obtain ⟨h, _, _⟩ := h
  have h' : 4 * (x * y) = 4 * k + 1 := by rw [← h]; ring
  omega

theorem linearInvo_no_fixedPoints : IsEmpty (fixedPoints (linearInvo k)) := by
  simp only [isEmpty_subtype, Subtype.forall, Prod.forall]
  intro x y z h hfixed
  have hfixed' : (linearInvo k ⟨⟨x, y, z⟩, h⟩).1.2.2 = z := by rw [hfixed]
  have : -z = z := hfixed'
  exact S_z_ne_zero k h (by linarith)

/-- The subset of `S k` where `z` is positive. -/
def T : Set (S k) := {⟨(_, _, z), _⟩ : S k | z > 0}

noncomputable instance : Fintype <| T k := by
  exact Fintype.ofFinite ↑(T k)

noncomputable instance (s : Set (T k)) : Fintype s := Fintype.ofFinite s

/-- The subset of `S k` where `x - y + z > 0`. -/
def U : Set (S k) := {⟨(x, y, z), _⟩ | (x - y) + z > 0}

noncomputable instance : Fintype <| U k := Fintype.ofFinite ↑(U k)
noncomputable instance (s : Set (U k)) : Fintype s := Fintype.ofFinite s

/-- If an involution `f` maps a set `P` exactly onto its complement, then `P` contains
exactly half of the elements. -/
lemma two_mul_card_of_involutive_compl {α : Type*} [Fintype α] (f : α → α)
    (hf : Involutive f) (P : Set α) (hP : ∀ x, x ∈ P ↔ f x ∉ P) :
    2 * Nat.card P = Fintype.card α := by
  classical
  rw [Nat.card_eq_card_toFinset]
  have h1 : P.toFinset.card = (Finset.univ.filter (· ∉ P)).card := by
    apply Finset.card_bij (fun a _ => f a)
    · intro a ha
      simp only [Set.mem_toFinset] at ha
      simpa using (hP a).1 ha
    · intro a _ b _ h
      exact hf.injective h
    · intro b hb
      refine ⟨f b, ?_, hf b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simpa [hP (f b), hf b] using hb
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ P)
  have h3 : P.toFinset = Finset.univ.filter (· ∈ P) := by ext; simp
  rw [Finset.card_univ, ← h3] at h2
  omega

lemma linearInvo_involutive : Involutive (linearInvo k) := fun x => by
  have := congrFun (linearInvo_sq k) x
  exact this

/- Original statement of `sameCard`, commented out because it is **false** as stated:
it lacks the hypothesis that `4 * k + 1` is prime. For `k = 2` (so `4 * k + 1 = 9`) we have
`S 2 = {(1, 2, ±1), (2, 1, ±1)}`, hence `T 2 = {(1, 2, 1), (2, 1, 1)}` has two elements while
`U 2 = {(2, 1, 1)}` has only one (the triples `(1, 2, 1)` and `(2, 1, -1)` satisfy
`x - y + z = 0`). This is proved in `not_sameCard_two` below. The corrected statement
`sameCard` adds the primality hypothesis. The original statement read:

  theorem sameCard : Fintype.card (U k) = Fintype.card (T k)
-/

/-- The original, hypothesis-free statement of `sameCard` fails for `k = 2`. -/
theorem not_sameCard_two : ¬ (Fintype.card (U 2) = Fintype.card (T 2)) := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have hU : Nat.card (U 2) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨(2, 1, 1), by refine ⟨by norm_num, by norm_num, by norm_num⟩⟩,
      by change (0 : ℤ) < 2 - 1 + 1; norm_num⟩, ?_⟩
    rintro ⟨⟨⟨x, y, z⟩, hS⟩, hU⟩
    have ub := S_upper_bound 2 hS
    obtain ⟨h, hx, hy⟩ := hS
    change 0 < x - y + z at hU
    have hx2 : x ≤ 2 := by exact_mod_cast ub.1
    have hy2 : y ≤ 2 := by exact_mod_cast ub.2
    push_cast at h
    have hz : z ≤ 3 := by nlinarith
    have hz' : -3 ≤ z := by nlinarith
    have : x = 2 ∧ y = 1 ∧ z = 1 := by
      interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all
    obtain ⟨rfl, rfl, rfl⟩ := this
    rfl
  have hT : 1 < Nat.card (T 2) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨⟨(1, 2, 1), by refine ⟨by norm_num, by norm_num, by norm_num⟩⟩,
      by change (0 : ℤ) < 1; norm_num⟩,
      ⟨⟨(2, 1, 1), by refine ⟨by norm_num, by norm_num, by norm_num⟩⟩,
      by change (0 : ℤ) < 1; norm_num⟩, ?_⟩⟩
    intro h
    have := congrArg (fun t => t.1.1.1) h
    simp at this
  omega

/-- `T` and `U` have the same cardinality (needs `4 * k + 1` to be prime, see above). -/
theorem sameCard [hk : Fact (4 * k + 1).Prime] :
    Fintype.card (U k) = Fintype.card (T k) := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  have hT :=
    two_mul_card_of_involutive_compl (linearInvo k) (linearInvo_involutive k) (T k)
    (by
      rintro ⟨⟨x, y, z⟩, h⟩
      have := S_z_ne_zero k h
      simp only [T, linearInvo, Set.mem_ofPred_eq]
      omega)
  have hU :=
    two_mul_card_of_involutive_compl (linearInvo k) (linearInvo_involutive k) (U k)
    (by
      rintro ⟨⟨x, y, z⟩, h⟩
      have hne : x - y + z ≠ 0 := by
        intro h0
        obtain ⟨h, hx, hy⟩ := h
        have hz : z = y - x := by linarith
        subst hz
        have hsq : ((x + y).toNat * (x + y).toNat : ℕ) = 4 * k + 1 := by
          have : (((x + y).toNat : ℕ) : ℤ) = x + y := Int.toNat_of_nonneg (by linarith)
          have : ((((x + y).toNat * (x + y).toNat : ℕ)) : ℤ) = 4 * k + 1 := by
            push_cast; rw [this, ← h]; ring
          exact_mod_cast this
        have hp := hk.out
        rw [← hsq] at hp
        have h2 : 2 ≤ (x + y).toNat := by omega
        exact Nat.not_prime_mul (by omega) (by omega) hp
      simp only [U, linearInvo, Set.mem_ofPred_eq]
      omega)
  omega

/- 2. -/

/-- The function underlying the second involution. -/
@[nolint defsWithUnderscore]
def secondInvo_fun := fun ((x,y,z) : ℤ × ℤ × ℤ) ↦ (x - y + z, y, 2 * y - z)

/-- The second involution that we study is an involution on the set U. -/
def secondInvo : Function.End (U k) := fun ⟨⟨⟨x, y, z⟩, hS⟩, h⟩ =>
  ⟨⟨secondInvo_fun ⟨x, y, z⟩, by
    obtain ⟨hS, _, hy⟩ := hS
    refine ⟨?_, h, hy⟩
    rw [← hS]; ring⟩, by
    obtain ⟨_, hx, _⟩ := hS
    change 0 < (x - y + z) - y + (2 * y - z)
    linarith⟩

/-- `secondInvo k` is indeed an involution. -/
theorem secondInvo_sq : secondInvo k ^ 2 = 1 := by
  change secondInvo k ∘ secondInvo k = id
  funext ⟨⟨⟨x, y, z⟩, hS⟩, h⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((x - y + z - y + (2 * y - z), y, 2 * y - (2 * y - z)) : ℤ × ℤ × ℤ) = (x, y, z)
  ext <;> dsimp only <;> ring

variable [hk : Fact (4 * k + 1).Prime]
theorem k_pos : 0 < k := by
  by_contra h
  simp at h
  rw [h] at hk
  simp at hk
  exact Nat.not_prime_one hk.out

/-- The singleton containing `(k, 1, 1)`. -/
def singletonFixedPoint : Finset (U k) :=
  {⟨⟨(k, 1, 1), by
  refine ⟨by ring, ?_, by norm_num⟩
  exact_mod_cast k_pos k⟩, by
  change (0 : ℤ) < k - 1 + 1
  have := k_pos k
  omega⟩}

/-- Any fixed point of `secondInvo k` must be `(k, 1, 1)`. -/
theorem eq_of_mem_fixedPoints : fixedPoints (secondInvo k) = singletonFixedPoint k := by
  ext ⟨⟨⟨x, y, z⟩, hS⟩, hU⟩
  have key : (⟨⟨(x, y, z), hS⟩, hU⟩ : U k) ∈ fixedPoints (secondInvo k) ↔
      x = k ∧ y = 1 ∧ z = 1 := by
    constructor
    · intro hfix
      have hfix' : secondInvo k ⟨⟨(x, y, z), hS⟩, hU⟩ = ⟨⟨(x, y, z), hS⟩, hU⟩ :=
        hfix
      have hv : secondInvo_fun (x, y, z) = (x, y, z) :=
        congrArg (fun t : U k => t.1.1) hfix'
      have hz : 2 * y - z = z := congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hv
      have hyz : y = z := by linarith
      subst y
      obtain ⟨hS, hx, hy⟩ := hS
      have hmul : z * (4 * x + z) = 4 * k + 1 := by rw [← hS]; ring
      have hdvd : z.toNat ∣ 4 * k + 1 := by
        refine ⟨(4 * x + z).toNat, ?_⟩
        have : (((z.toNat * (4 * x + z).toNat : ℕ)) : ℤ) = 4 * k + 1 := by
          push_cast
          rw [Int.toNat_of_nonneg (by linarith), Int.toNat_of_nonneg (by linarith), hmul]
        exact_mod_cast this.symm
      rcases hk.out.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · have hz1 : z = 1 := by omega
        subst hz1
        have h4 : 4 * x = 4 * (k : ℤ) := by linear_combination hS
        exact ⟨by linarith, rfl, rfl⟩
      · have hz1 : z = 4 * k + 1 := by omega
        exfalso
        subst hz1
        nlinarith [mul_pos (show (0 : ℤ) < 4 * k + 1 by positivity) hx, sq_nonneg (k : ℤ),
          (Nat.cast_nonneg k : (0 : ℤ) ≤ k)]
    · rintro ⟨rfl, rfl, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change ((k : ℤ) - 1 + 1, (1 : ℤ), 2 * (1 : ℤ) - 1) =
        ((k : ℤ), (1 : ℤ), (1 : ℤ))
      ext <;> dsimp only <;> ring
  rw [key, singletonFixedPoint, Finset.coe_singleton, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    rfl
  · intro h
    have hv := congrArg (fun t : U k => t.1.1) h
    simp only [Prod.mk.injEq] at hv
    exact hv

/-- `secondInvo k` has exactly one fixed point. -/
theorem card_fixedPoints_eq_one : Fintype.card (fixedPoints (secondInvo k)) = 1 := by
  have : fixedPoints (secondInvo k) = (singletonFixedPoint k : Set (U k)) :=
    eq_of_mem_fixedPoints k
  rw [Fintype.card_eq_nat_card, this]
  simp [singletonFixedPoint]

theorem card_T_odd : Odd <| Fintype.card <| T k := by
  rw [← sameCard k]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (f := secondInvo k)
    (by simpa using secondInvo_sq k)
  have h1 := card_fixedPoints_eq_one k
  simp only [Fintype.card_eq_nat_card] at hmod h1 ⊢
  rw [h1] at hmod
  rw [Nat.odd_iff]
  exact hmod

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
/-- `trivialInvo k` is an involution. -/
theorem trivialInvo_sq : trivialInvo k ^ 2 = 1 := by
  change trivialInvo k ∘ trivialInvo k = id
  funext ⟨⟨⟨x, y, z⟩, hS⟩, h⟩
  rfl

omit hk in
/-- If `trivialInvo k` has a fixed point, a representation of `4 * k + 1` as a sum of two squares
can be extracted from it. -/
theorem sq_add_sq_of_nonempty_fixedPoints (hn : (fixedPoints (trivialInvo k)).Nonempty) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  obtain ⟨⟨⟨⟨x, y, z⟩, hS⟩, hT⟩, hf⟩ := hn
  have hf' : (trivialInvo k ⟨⟨⟨x, y, z⟩, hS⟩, hT⟩).1.1.1 =
      (⟨⟨⟨x, y, z⟩, hS⟩, hT⟩ : T k).1.1.1 := by
    rw [hf]
  have h_eq : y = x := hf'
  use 2 * y, z
  have hS1 := hS.1
  subst h_eq
  linear_combination hS1

theorem trivialInvo_fixedPoints : (fixedPoints (trivialInvo k)).Nonempty := by
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (f := trivialInvo k)
    (by simpa using trivialInvo_sq k)
  have hodd := card_T_odd k
  simp only [Fintype.card_eq_nat_card] at hmod hodd
  rw [Nat.odd_iff] at hodd
  rw [Nat.ModEq, hodd] at hmod
  have hpos : 0 < Nat.card (fixedPoints (trivialInvo k)) := by omega
  rw [Nat.card_pos_iff] at hpos
  exact Set.nonempty_coe_sort.mp hpos.1

end Involutions

/-- The Proposition, via Heath-Brown's / Zagier's involution proof:
every prime `p` with `p % 4 = 1` is a sum of two squares. -/
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

/-- The Theorem of the chapter: a natural number `n` is a sum of two squares if and only if
every prime factor `q` of the form `4 * m + 3` appears with an even exponent in the prime
decomposition of `n`. -/
theorem theorem₃ (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (padicValNat q n) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro H q hq h3
    by_cases hqn : q ∈ n.primeFactors
    · exact H q hqn h3
    · have : ¬ (q ∣ n ∧ n ≠ 0) := by
        intro hc
        exact hqn (Nat.mem_primeFactors.mpr ⟨hq, hc.1, hc.2⟩)
      by_cases hn : n = 0
      · simp [hn]
      · have hnd : ¬ q ∣ n := fun hd => this ⟨hd, hn⟩
        simp [padicValNat.eq_zero_of_not_dvd hnd]
  · intro H q hq h3
    exact H q (Nat.prime_of_mem_primeFactors hq) h3

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

end ch04
