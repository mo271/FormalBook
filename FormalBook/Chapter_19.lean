/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib

/-!
# Sets, functions, and the continuum hypothesis — complete formalization in one file

This single file contains the entire formalization of Chapter 19, organised in the sections
1. Theorem 1 and the Calkin–Wilf enumeration,
2. Hyperbinary representations,
3. Theorems 2 and 3 (real numbers, intervals, the plane),
4. Theorem 4 (Cantor–Bernstein) and the continuum hypothesis,
5. Appendix: cardinal and ordinal numbers (Propositions 1–6),
6. Analytic ingredients for Theorem 5,
7. Theorem 5 (Erdős).
All declarations live in the namespace `Chapter19`.
-/

@[expose] public section


/-! ======================================================================
## Part: CalkinWilf
====================================================================== -/

/-!
# Theorem 1: the rationals are countable — the Calkin–Wilf enumeration

We formalize Theorem 1 of the chapter together with all four properties `(1)`–`(4)` of the
Calkin–Wilf tree, Stern's diatomic sequence, Newman's successor formula and the binary
description of the `n`-th fraction.

## Conventions

* `stern` is Stern's diatomic sequence in its standard indexing
  `s 0 = 0, s 1 = 1, s (2n) = s n, s (2n+1) = s n + s (n+1)`.
  The book's sequence `b(n)` (with `b 0 = 1`) is `diatomic n = stern (n + 1)`.
* The nodes of the Calkin–Wilf tree are indexed in *heap order*: the root `1/1` has index `1`,
  and the left/right sons of the node with index `m` have indices `2m` and `2m+1`.
  Heap order is exactly the level-by-level, left-to-right listing used in the book, so the
  `n`-th fraction of the Calkin–Wilf list (`n ≥ 0`) is the node with index `n + 1`.
  Index `0` carries the extra fraction `0/1` of the "larger tree without root".
* Fractions are represented as pairs `(numerator, denominator)` of natural numbers.
-/


namespace Chapter19

section CalkinWilf

/-! ### Stern's diatomic sequence -/

/-- Stern's diatomic sequence in its standard indexing:
`s 0 = 0`, `s 1 = 1`, `s (2n) = s n`, `s (2n+1) = s n + s (n+1)`. -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2)
    else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
  decreasing_by all_goals omega

theorem stern_zero : stern 0 = 0 := by simp [stern]

theorem stern_one : stern 1 = 1 := by simp [stern]

theorem stern_two_mul (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, stern, ite_cond_eq_true _ _ (eq_true (by omega)),
      show (2 * n + 2) / 2 = n + 1 by omega]

theorem stern_two_mul_add_one (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, stern, ite_cond_eq_false _ _ (eq_false (by omega)),
      show (2 * n + 1 + 2) / 2 = n + 1 by omega]

theorem stern_pos {m : ℕ} (hm : 1 ≤ m) : 0 < stern m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [stern_two_mul]; exact ih k (by omega) (by omega)
    · rw [stern_two_mul_add_one]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [stern_one]
      · have := ih (k + 1) (by omega) (by omega); omega

theorem stern_two_mul_add_two (n : ℕ) : stern (2 * n + 2) = stern (n + 1) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by ring, stern_two_mul]

theorem stern_two : stern 2 = 1 := by simpa [stern_one] using stern_two_mul 1

/-- The book's version `b(n)` of Stern's diatomic series, `b = (1, 1, 2, 1, 3, 2, 3, 1, …)`. -/
def diatomic (n : ℕ) : ℕ := stern (n + 1)

/-- The recursion `(1)` of the book: `b 0 = 1`, `b (2n+1) = b n`, `b (2n+2) = b n + b (n+1)`.
These equations determine `b` completely. -/
theorem diatomic_recursion :
    diatomic 0 = 1 ∧ (∀ n, diatomic (2 * n + 1) = diatomic n) ∧
      (∀ n, diatomic (2 * n + 2) = diatomic n + diatomic (n + 1)) := by
  refine ⟨stern_one, fun n => ?_, fun n => ?_⟩
  · simp only [diatomic, show 2 * n + 1 + 1 = 2 * n + 2 by ring, stern_two_mul_add_two]
  · simp only [diatomic, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, stern_two_mul_add_one]

/-! ### The Calkin–Wilf tree -/

/-- The Calkin–Wilf tree, with nodes indexed in heap order. The root (index `1`) is `1/1`; the
left son of `i/j` is `i/(i+j)` and its right son is `(i+j)/j`. Index `0` carries `0/1`, whose
right son is the root `1/1`. -/
def cwNode : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | (m + 1) =>
    if (m + 1) % 2 = 0 then ((cwNode ((m + 1) / 2)).1, (cwNode ((m + 1) / 2)).1 + (cwNode ((m + 1) / 2)).2)
    else ((cwNode ((m + 1) / 2)).1 + (cwNode ((m + 1) / 2)).2, (cwNode ((m + 1) / 2)).2)
  decreasing_by all_goals omega

/-- The top of the tree is `1/1`. -/
theorem cwNode_one : cwNode 1 = (1, 1) := by
  simp [cwNode]

/-- The left son of `i/j` is `i/(i+j)`. -/
theorem cwNode_left {m : ℕ} (hm : 1 ≤ m) :
    cwNode (2 * m) = ((cwNode m).1, (cwNode m).1 + (cwNode m).2) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, cwNode, ite_cond_eq_true _ _ (eq_true (by omega)),
    show (2 * j + 1 + 1) / 2 = j + 1 by omega]

/-- The right son of `i/j` is `(i+j)/j`. -/
theorem cwNode_right (m : ℕ) :
    cwNode (2 * m + 1) = ((cwNode m).1 + (cwNode m).2, (cwNode m).2) := by
  rw [cwNode, ite_cond_eq_false _ _ (eq_false (by omega)), show (2 * m + 1) / 2 = m by omega]

/-- The node with index `m` is `stern m / stern (m+1)`. -/
theorem cwNode_eq_stern (m : ℕ) : cwNode m = (stern m, stern (m + 1)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [cwNode, stern_zero, stern_one]
      · rw [cwNode_left hk, ih k (by omega), stern_two_mul, stern_two_mul_add_one]
    · rw [cwNode_right, ih k (by omega), stern_two_mul_add_one, stern_two_mul_add_two]

theorem stern_coprime (m : ℕ) : Nat.Coprime (stern m) (stern (m + 1)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [stern_zero, stern_one]
      · rw [stern_two_mul, stern_two_mul_add_one, add_comm, Nat.coprime_add_self_right]
        exact ih k (by omega)
    · rw [stern_two_mul_add_one, stern_two_mul_add_two, Nat.coprime_add_self_left]
      exact ih k (by omega)

theorem stern_surjective_aux (N : ℕ) : ∀ r s, r + s ≤ N → 0 < r → 0 < s → Nat.Coprime r s →
    ∃ m, 1 ≤ m ∧ stern m = r ∧ stern (m + 1) = s := by
  induction N with
  | zero => intro r s h hr hs _; omega
  | succ N ih =>
    intro r s h hr hs hrs
    rcases lt_trichotomy r s with hlt | heq | hgt
    · obtain ⟨k, hk, h1, h2⟩ := ih r (s - r) (by omega) hr (by omega)
        (by
          have : s = (s - r) + r := by omega
          rw [this, Nat.coprime_add_self_right] at hrs; exact hrs)
      refine ⟨2 * k, by omega, ?_, ?_⟩
      · rw [stern_two_mul, h1]
      · rw [stern_two_mul_add_one, h1, h2]; omega
    · subst heq
      have : r = 1 := (Nat.coprime_self r).mp hrs
      subst this
      exact ⟨1, le_rfl, stern_one, by simpa [stern_one] using stern_two_mul 1⟩
    · obtain ⟨k, hk, h1, h2⟩ := ih (r - s) s (by omega) (by omega) hs
        (by
          have : r = (r - s) + s := by omega
          rw [this, Nat.coprime_add_self_left] at hrs; exact hrs)
      refine ⟨2 * k + 1, by omega, ?_, ?_⟩
      · rw [stern_two_mul_add_one, h1, h2]; omega
      · rw [stern_two_mul_add_two, h2]

theorem stern_even_lt {k : ℕ} (hk : 1 ≤ k) : stern (2 * k) < stern (2 * k + 1) := by
  rw [stern_two_mul, stern_two_mul_add_one]
  have := stern_pos (m := k + 1) (by omega); omega

theorem stern_odd_gt {k : ℕ} (hk : 1 ≤ k) : stern (2 * k + 2) < stern (2 * k + 1) := by
  rw [stern_two_mul_add_two, stern_two_mul_add_one]
  have := stern_pos hk; omega

theorem index_cases {m : ℕ} (hm : 1 ≤ m) :
    m = 1 ∨ (∃ k, 1 ≤ k ∧ m = 2 * k) ∨ (∃ k, 1 ≤ k ∧ m = 2 * k + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact Or.inr (Or.inl ⟨k, by omega, rfl⟩)
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)

theorem stern_injective_aux (m : ℕ) : ∀ m', 1 ≤ m → 1 ≤ m' → stern m = stern m' →
    stern (m + 1) = stern (m' + 1) → m = m' := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro m' hm hm' h1 h2
    have s2 : stern 2 = 1 := by simpa [stern_one] using stern_two_mul 1
    rcases index_cases hm with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases index_cases hm' with rfl | ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩ <;>
    try simp only [show ∀ j : ℕ, 2 * j + 1 + 1 = 2 * j + 2 from fun j => rfl] at h1 h2
    · rfl
    · have := stern_even_lt hk'; rw [stern_one] at h1; rw [s2] at h2; omega
    · have := stern_odd_gt hk'; rw [stern_one] at h1; rw [s2] at h2; omega
    · have := stern_even_lt hk; rw [stern_one] at h1; rw [s2] at h2; omega
    · rw [stern_two_mul, stern_two_mul] at h1
      rw [stern_two_mul_add_one, stern_two_mul_add_one] at h2
      have := ih k (by omega) k' hk hk' h1 (by omega); omega
    · have := stern_even_lt hk; have := stern_odd_gt hk'; omega
    · have := stern_odd_gt hk; rw [stern_one] at h1; rw [s2] at h2; omega
    · have := stern_even_lt hk'; have := stern_odd_gt hk; omega
    · rw [stern_two_mul_add_two, stern_two_mul_add_two] at h2
      rw [stern_two_mul_add_one, stern_two_mul_add_one] at h1
      have := ih k (by omega) k' hk hk' (by omega) h2; omega

/-- Property `(1)`: all fractions in the tree are reduced. -/
theorem cwNode_coprime (m : ℕ) : Nat.Coprime (cwNode m).1 (cwNode m).2 := by
  rw [cwNode_eq_stern]; exact stern_coprime m

/-- Property `(2)`: every reduced fraction `r/s > 0` appears in the tree. -/
theorem cwNode_surjective {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s) :
    ∃ m, 1 ≤ m ∧ cwNode m = (r, s) := by
  obtain ⟨m, hm, h1, h2⟩ := stern_surjective_aux (r + s) r s le_rfl hr hs hrs
  exact ⟨m, hm, by rw [cwNode_eq_stern, h1, h2]⟩

/-- Property `(3)`: every reduced fraction appears exactly once. -/
theorem cwNode_injective {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (h : cwNode m = cwNode m') :
    m = m' := by
  rw [cwNode_eq_stern, cwNode_eq_stern, Prod.mk.injEq] at h
  exact stern_injective_aux m m' hm hm' h.1 h.2

/-- Property `(4)`: the denominator of the `n`-th fraction in the list equals the numerator of
the `(n+1)`-st. (The `n`-th fraction, `n ≥ 0`, is the node with heap index `n + 1`.) -/
theorem cwNode_denominator_eq_next_numerator (n : ℕ) :
    (cwNode (n + 1)).2 = (cwNode (n + 2)).1 := by
  simp [cwNode_eq_stern]

/-- The `n`-th fraction of the Calkin–Wilf list is `b(n)/b(n+1)`. -/
theorem cwNode_eq_diatomic (n : ℕ) : cwNode (n + 1) = (diatomic n, diatomic (n + 1)) := by
  rw [cwNode_eq_stern]; rfl

/-! ### The Calkin–Wilf sequence and Theorem 1 -/

/-- The Calkin–Wilf sequence `1/1, 1/2, 2/1, 1/3, 3/2, 2/3, 3/1, 1/4, …`, i.e. `b(n)/b(n+1)`. -/
def calkinWilfSeq (n : ℕ) : ℚ := (diatomic n : ℚ) / diatomic (n + 1)

theorem calkinWilfSeq_pos (n : ℕ) : 0 < calkinWilfSeq n := by
  unfold calkinWilfSeq diatomic
  have h1 := stern_pos (m := n + 1) (by omega)
  have h2 := stern_pos (m := n + 1 + 1) (by omega)
  positivity

/-- The Calkin–Wilf sequence lists every positive rational exactly once. -/
theorem calkinWilfSeq_bijective :
    Function.Bijective (fun n : ℕ => (⟨calkinWilfSeq n, calkinWilfSeq_pos n⟩ : {q : ℚ // 0 < q})) := by
  have key : ∀ k, ((diatomic k : ℚ) / diatomic (k + 1)).num = diatomic k ∧
      ((diatomic k : ℚ) / diatomic (k + 1)).den = diatomic (k + 1) := by
    intro k
    have hpos : (0 : ℤ) < (diatomic (k + 1) : ℤ) := by
      unfold diatomic; exact_mod_cast stern_pos (by omega)
    have hcop : (diatomic k : ℤ).natAbs.Coprime (diatomic (k + 1) : ℤ).natAbs := by
      simpa [diatomic] using stern_coprime (k + 1)
    have e : ((diatomic k : ℚ) / diatomic (k + 1)) =
        ((diatomic k : ℤ) : ℚ) / ((diatomic (k + 1) : ℤ) : ℚ) := by push_cast; rfl
    rw [e]
    exact ⟨Rat.num_div_eq_of_coprime hpos hcop, by exact_mod_cast Rat.den_div_eq_of_coprime hpos hcop⟩
  constructor
  · intro n n' h
    simp only [Subtype.mk.injEq, calkinWilfSeq] at h
    have h1 := (key n).1; have h2 := (key n).2; have h3 := (key n').1; have h4 := (key n').2
    rw [h] at h1 h2
    have e1 : diatomic n = diatomic n' := by exact_mod_cast h1.symm.trans h3
    have e2 : diatomic (n + 1) = diatomic (n' + 1) := h2.symm.trans h4
    have := cwNode_injective (m := n + 1) (m' := n' + 1) (by omega) (by omega)
      (by rw [cwNode_eq_diatomic, cwNode_eq_diatomic, e1, e2])
    omega
  · rintro ⟨q, hq⟩
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    obtain ⟨m, hm, hmq⟩ := cwNode_surjective (r := q.num.natAbs) (s := q.den)
      (Int.natAbs_pos.mpr hnum.ne') q.den_pos q.reduced
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [cwNode_eq_diatomic, Prod.mk.injEq] at hmq
    refine ⟨n, Subtype.ext ?_⟩
    simp only [calkinWilfSeq, hmq.1, hmq.2]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
    exact Rat.num_div_den q

/-- **Theorem 1.** The set `ℚ` of rational numbers is countable. We list `0` first and `-q`
right after `q` for every `q` of the Calkin–Wilf list. -/
theorem rat_countable : Countable ℚ := by
  let g : Option (ℕ ⊕ ℕ) → ℚ := fun o => match o with
    | none => 0
    | some (Sum.inl n) => calkinWilfSeq n
    | some (Sum.inr n) => -calkinWilfSeq n
  have hg : Function.Surjective g := by
    intro q
    rcases lt_trichotomy q 0 with h | rfl | h
    · obtain ⟨n, hn⟩ := calkinWilfSeq_bijective.2 ⟨-q, by linarith⟩
      refine ⟨some (Sum.inr n), ?_⟩
      have := congrArg Subtype.val hn
      simp only at this
      simp [g, this]
    · exact ⟨none, rfl⟩
    · obtain ⟨n, hn⟩ := calkinWilfSeq_bijective.2 ⟨q, h⟩
      exact ⟨some (Sum.inl n), congrArg Subtype.val hn⟩
  exact hg.countable

/-- An explicit bijection between `ℕ` and `ℚ` exists. -/
theorem rat_equiv_nat : Nonempty (ℚ ≃ ℕ) := by
  have := rat_countable
  obtain ⟨d⟩ := nonempty_denumerable ℚ
  exact ⟨Denumerable.eqv ℚ⟩

/-- The set `ℤ` of integers is countable: `ℤ = {0, 1, -1, 2, -2, …}`. -/
theorem int_countable : Countable ℤ := by
  let g : ℕ ⊕ ℕ → ℤ := fun o => match o with
    | Sum.inl n => n
    | Sum.inr n => -n
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
    · exact ⟨Sum.inl n, rfl⟩
    · exact ⟨Sum.inr n, rfl⟩
  exact hg.countable

/-- The union of countably many countable sets is again countable. -/
theorem countable_iUnion_of_countable {α : Type*} (M : ℕ → Set α) (hM : ∀ n, (M n).Countable) :
    (⋃ n, M n).Countable := by
  exact Set.countable_iUnion hM

/-! ### Newman's formula -/

/-- The right son `x ↦ x + 1` in the Calkin–Wilf tree, written for rationals `x = r/s`. -/
def rightSon (x : ℚ) : ℚ := x + 1

/-- The left son `x ↦ x / (1 + x)` in the Calkin–Wilf tree, written for rationals `x = r/s`. -/
def leftSon (x : ℚ) : ℚ := x / (1 + x)

/-- The sons of `r/s` are `r/(r+s)` and `(r+s)/s`. -/
theorem sons_of_fraction {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    leftSon ((r : ℚ) / s) = (r : ℚ) / (r + s) ∧ rightSon ((r : ℚ) / s) = ((r : ℚ) + s) / s := by
  have hs' : (s : ℚ) ≠ 0 := by positivity
  have hrs : (r : ℚ) + s ≠ 0 := by positivity
  unfold leftSon rightSon
  constructor <;> field_simp; ring

/-- The `k`-fold right son of `x` is `x + k`. -/
theorem rightSon_iterate (k : ℕ) (x : ℚ) : rightSon^[k] x = x + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rightSon]; push_cast; ring

/-- The `k`-fold left son of `x ≥ 0` is `x / (1 + k x)`. -/
theorem leftSon_iterate (k : ℕ) {x : ℚ} (hx : 0 ≤ x) : leftSon^[k] x = x / (1 + k * x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 : 0 < 1 + (k : ℚ) * x := by positivity
    have h2 : 0 < 1 + ((k : ℚ) + 1) * x := by positivity
    unfold leftSon
    push_cast
    field_simp
    ring

/-- Newman's successor function `f(x) = 1 / (⌊x⌋ + 1 - {x})`. -/
def newman (x : ℚ) : ℚ := 1 / (⌊x⌋ + 1 - Int.fract x)

/-- The key computation behind Newman's formula: if `x` is the `k`-fold right son of the left
son of `y ≥ 0`, then `f(x)` is the `k`-fold left son of the right son of `y`. -/
theorem newman_rightSon_leftSon (k : ℕ) {y : ℚ} (hy : 0 ≤ y) :
    newman (rightSon^[k] (leftSon y)) = leftSon^[k] (rightSon y) := by
  have hy1 : 0 < 1 + y := by linarith
  have h0 : 0 ≤ y / (1 + y) := by positivity
  have h1 : y / (1 + y) < 1 := by rw [div_lt_one hy1]; linarith
  rw [rightSon_iterate, leftSon_iterate k (by unfold rightSon; linarith)]
  unfold newman leftSon rightSon
  rw [Int.floor_add_natCast, Int.fract_add_natCast, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩,
    Int.fract_eq_self.mpr ⟨h0, h1⟩]
  have h2 : 0 < 1 + (k : ℚ) * (y + 1) := by positivity
  simp only [zero_add, Int.cast_natCast]
  rw [show (k : ℚ) + 1 - y / (1 + y) = (1 + k * (y + 1)) / (1 + y) by field_simp; ring,
    one_div_div, add_comm y 1]

/-- The arithmetic identity behind Newman's formula:
`s (m+2) = s m + s (m+1) - 2 (s m mod s (m+1))`. -/
theorem stern_newman (m : ℕ) : (stern (m + 2) : ℤ) =
    stern m + stern (m + 1) - 2 * ((stern m % stern (m + 1) : ℕ) : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [stern_two_mul_add_two, stern_two_mul, stern_two_mul_add_one,
        Nat.mod_eq_of_lt (by have := stern_pos (m := k + 1) (by omega); omega)]
      push_cast; ring
    · rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, show 2 * k + 1 + 1 = 2 * k + 2 by ring,
        stern_two_mul_add_one, stern_two_mul_add_one, stern_two_mul_add_two, Nat.add_mod_right]
      have := ih k (by omega)
      simp only [show k + 1 + 1 = k + 2 from rfl] at *
      push_cast at this ⊢; linarith

/-- **Newman's formula.** `x ↦ 1 / (⌊x⌋ + 1 - {x})` generates the Calkin–Wilf sequence. -/
theorem newman_calkinWilfSeq (n : ℕ) : newman (calkinWilfSeq n) = calkinWilfSeq (n + 1) := by
  have key := stern_newman (n + 1)
  unfold calkinWilfSeq diatomic
  simp only [show n + 1 + 2 = n + 1 + 1 + 1 from rfl] at key
  set a := stern (n + 1)
  set b := stern (n + 1 + 1)
  set c := stern (n + 1 + 1 + 1)
  have hb : 0 < b := stern_pos (by omega)
  have hc : 0 < c := stern_pos (by omega)
  have hab : (a : ℚ) = b * ((a / b : ℕ) : ℚ) + ((a % b : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod a b).symm
  have hr : a % b < b := Nat.mod_lt _ hb
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hrq : ((a % b : ℕ) : ℚ) < b := by exact_mod_cast hr
  have hcq : (c : ℚ) = a + b - 2 * ((a % b : ℕ) : ℚ) := by exact_mod_cast key
  have hx : (a : ℚ) / b = ((a % b : ℕ) : ℚ) / b + ((a / b : ℕ) : ℚ) := by
    rw [hab]; field_simp; ring
  have h0 : 0 ≤ ((a % b : ℕ) : ℚ) / b := by positivity
  have h1 : ((a % b : ℕ) : ℚ) / b < 1 := by rw [div_lt_one hbq]; exact hrq
  rw [hx]
  unfold newman
  rw [Int.floor_add_natCast, Int.fract_add_natCast, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩,
    Int.fract_eq_self.mpr ⟨h0, h1⟩, hcq, hab]
  have hden : (b : ℚ) * ((a / b : ℕ) : ℚ) + b - ((a % b : ℕ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) ≤ ((a / b : ℕ) : ℚ) := by positivity
    nlinarith
  simp only [zero_add, Int.cast_natCast]
  rw [show ((a / b : ℕ) : ℚ) + 1 - ((a % b : ℕ) : ℚ) / b =
      (b * ((a / b : ℕ) : ℚ) + b - ((a % b : ℕ) : ℚ)) / b by field_simp,
    one_div_div]
  congr 1
  ring

/-- Starting from the extra fraction `0/1`, Newman's map produces `1/1`, the start of the list. -/
theorem newman_zero : newman 0 = calkinWilfSeq 0 := by
  simp [newman, calkinWilfSeq, diatomic, stern_one, stern_two]

/-! ### The `n`-th fraction from the binary expansion of `n` -/

/-- One step along a path of the tree: digit `1` means "take the right son" (add the
denominator to the numerator), digit `0` means "take the left son" (add the numerator to
the denominator). -/
def cwStep (p : ℕ × ℕ) (d : ℕ) : ℕ × ℕ :=
  if d = 1 then (p.1 + p.2, p.2) else (p.1, p.1 + p.2)

/-- Follow the path determined by the binary digits of `n` (most significant digit first),
starting at `0/1`. -/
def cwPath (n : ℕ) : ℕ × ℕ := (Nat.digits 2 n).reverse.foldl cwStep (0, 1)

/-- The path given by the binary digits of `n` ends at the `n`-th fraction of the
Calkin–Wilf sequence (counting `0/1` as the `0`-th one). -/
theorem cwPath_eq (n : ℕ) : cwPath n = cwNode n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cwPath, cwNode]
    · have hd : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) := Nat.digits_def' (by norm_num) hn
      have hstep : cwPath n = cwStep (cwPath (n / 2)) (n % 2) := by
        simp only [cwPath, hd, List.reverse_cons, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      rw [hstep, ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [h]
        have e : n = 2 * (n / 2) := by omega
        conv_rhs => rw [e]
        rw [cwNode_left (by omega)]
        simp [cwStep]
      · rw [h]
        have e : n = 2 * (n / 2) + 1 := by omega
        conv_rhs => rw [e]
        rw [cwNode_right]
        simp [cwStep]

/-- The book's example: `25 = (11001)₂`, and the 25th number of the sequence is `7/5`. -/
theorem cwPath_25 : cwPath 25 = (7, 5) := by
  rw [cwPath_eq, cwNode_eq_stern]
  simp [stern]

end CalkinWilf

end Chapter19


/-! ======================================================================
## Part: Hyperbinary
====================================================================== -/

/-!
# Hyperbinary representations and Stern's diatomic series

A *hyperbinary representation* of `n` is a representation of `n` as a sum of powers of `2`
in which every power `2^k` appears at most twice. We encode such a representation as the
multiset of exponents `k`. The book observes that the number `h(n)` of hyperbinary
representations obeys the same recursion `(1)` as `b(n)`, hence `b(n) = h(n)`.
-/


namespace Chapter19

section Hyperbinary

/-- The hyperbinary representations of `n`, encoded as multisets of exponents in which every
exponent occurs at most twice and `∑ 2^k = n`. -/
def hyperbinaryReps (n : ℕ) : Set (Multiset ℕ) :=
  {s | (∀ k, s.count k ≤ 2) ∧ (s.map (2 ^ ·)).sum = n}

theorem mem_hyperbinaryReps {n : ℕ} {s : Multiset ℕ} :
    s ∈ hyperbinaryReps n ↔ (∀ k, s.count k ≤ 2) ∧ (s.map (2 ^ ·)).sum = n := Iff.rfl

/-- The number `h(n)` of hyperbinary representations of `n`. -/
noncomputable def hyperbinary (n : ℕ) : ℕ := (hyperbinaryReps n).ncard

/-- Prepend `c` copies of the exponent `0` to a representation in which all exponents
are shifted up by one. -/
def hbLift (c : ℕ) (t : Multiset ℕ) : Multiset ℕ := Multiset.replicate c 0 + t.map (· + 1)

theorem hbLift_injective (c : ℕ) : Function.Injective (hbLift c) := by
  intro t t' h
  unfold hbLift at h
  exact Multiset.map_injective (fun a b h => by simpa using h) (add_left_cancel h)

theorem count_zero_hbLift (c : ℕ) (t : Multiset ℕ) : (hbLift c t).count 0 = c := by
  unfold hbLift
  rw [Multiset.count_add, Multiset.count_replicate_self, Multiset.count_eq_zero.mpr]
  · simp
  · simp

theorem count_succ_hbLift (c : ℕ) (t : Multiset ℕ) (k : ℕ) :
    (hbLift c t).count (k + 1) = t.count k := by
  unfold hbLift
  rw [Multiset.count_add, Multiset.count_map_eq_count' _ _ (add_left_injective 1)]
  simp [Multiset.count_replicate]

theorem sum_hbLift (c : ℕ) (t : Multiset ℕ) :
    ((hbLift c t).map (2 ^ ·)).sum = c + 2 * (t.map (2 ^ ·)).sum := by
  unfold hbLift
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
    Multiset.map_map]
  simp only [Function.comp_def, pow_succ', Multiset.sum_map_mul_left, smul_eq_mul, pow_zero,
    mul_one]

theorem hbLift_mem_iff {c m : ℕ} (hc : c ≤ 2) (t : Multiset ℕ) :
    hbLift c t ∈ hyperbinaryReps (c + 2 * m) ↔ t ∈ hyperbinaryReps m := by
  simp only [mem_hyperbinaryReps, sum_hbLift]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k => by rw [← count_succ_hbLift c t k]; exact h1 _, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, by omega⟩
    rcases k with _ | k
    · rw [count_zero_hbLift]; exact hc
    · rw [count_succ_hbLift]; exact h1 k

/-- Every multiset of exponents decomposes according to the multiplicity of the exponent `0`. -/
theorem eq_hbLift (s : Multiset ℕ) :
    s = hbLift (s.count 0) ((s.filter (· ≠ 0)).map (· - 1)) := by
  unfold hbLift
  conv_lhs => rw [← Multiset.filter_add_not (· = 0) s]
  congr 1
  · rw [Multiset.filter_eq' s 0]
  · rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id (Multiset.filter _ s)]
    apply Multiset.map_congr rfl
    intro x hx
    simp only [Multiset.mem_filter] at hx
    simp only [id, Function.comp_apply]
    omega

theorem decompose_hyperbinary {N : ℕ} {s : Multiset ℕ} (hs : s ∈ hyperbinaryReps N) :
    ∃ m, N = s.count 0 + 2 * m ∧ s.count 0 ≤ 2 ∧
      (s.filter (· ≠ 0)).map (· - 1) ∈ hyperbinaryReps m ∧
      s = hbLift (s.count 0) ((s.filter (· ≠ 0)).map (· - 1)) := by
  have hdec := eq_hbLift s
  set t := (s.filter (· ≠ 0)).map (· - 1)
  have h2 : (s.map (2 ^ ·)).sum = s.count 0 + 2 * (t.map (2 ^ ·)).sum := by
    conv_lhs => rw [hdec]
    exact sum_hbLift _ _
  have hN : N = s.count 0 + 2 * (t.map (2 ^ ·)).sum := hs.2 ▸ h2
  refine ⟨(t.map (2 ^ ·)).sum, hN, hs.1 0, ?_, hdec⟩
  rw [← hbLift_mem_iff (hs.1 0), ← hdec, ← hN]
  exact hs

theorem hyperbinaryReps_zero : hyperbinaryReps 0 = {0} := by
  ext s
  simp only [mem_hyperbinaryReps, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    rw [Multiset.sum_eq_zero_iff] at h
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    exact absurd (h (2 ^ x) (Multiset.mem_map_of_mem _ hx)) (by positivity)
  · rintro rfl; simp

theorem hyperbinaryReps_odd (n : ℕ) :
    hyperbinaryReps (2 * n + 1) = hbLift 1 '' hyperbinaryReps n := by
  ext s
  constructor
  · intro hs
    obtain ⟨m, hN, hc, ht, hdec⟩ := decompose_hyperbinary hs
    have h1 : s.count 0 = 1 := by omega
    have h2 : m = n := by omega
    rw [h1] at hdec; rw [h2] at ht
    exact ⟨_, ht, hdec.symm⟩
  · rintro ⟨t, ht, rfl⟩
    rw [show 2 * n + 1 = 1 + 2 * n by ring]
    exact (hbLift_mem_iff (by norm_num) t).2 ht

theorem hyperbinaryReps_even (n : ℕ) :
    hyperbinaryReps (2 * n + 2) =
      hbLift 0 '' hyperbinaryReps (n + 1) ∪ hbLift 2 '' hyperbinaryReps n := by
  ext s
  constructor
  · intro hs
    obtain ⟨m, hN, hc, ht, hdec⟩ := decompose_hyperbinary hs
    rcases (show (s.count 0 = 0 ∧ m = n + 1) ∨ (s.count 0 = 2 ∧ m = n) by omega) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hdec; rw [h2] at ht
      exact Or.inl ⟨_, ht, hdec.symm⟩
    · rw [h1] at hdec; rw [h2] at ht
      exact Or.inr ⟨_, ht, hdec.symm⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [show 2 * n + 2 = 0 + 2 * (n + 1) by ring]
      exact (hbLift_mem_iff (by norm_num) t).2 ht
    · rw [show 2 * n + 2 = 2 + 2 * n by ring]
      exact (hbLift_mem_iff (by norm_num) t).2 ht

theorem encard_hyperbinaryReps (n : ℕ) :
    (hyperbinaryReps n).encard = (diatomic n : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨_, rec1, rec2⟩ := diatomic_recursion
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases k with _ | k
      · rw [hyperbinaryReps_zero, Set.encard_singleton]
        simp [diatomic, stern_one]
      · rw [show 2 * (k + 1) = 2 * k + 2 by ring, hyperbinaryReps_even, Set.encard_union_eq,
          (hbLift_injective 0).encard_image, (hbLift_injective 2).encard_image,
          ih (k + 1) (by omega), ih k (by omega), rec2]
        · push_cast; ring
        · rw [Set.disjoint_left]
          rintro _ ⟨t, -, rfl⟩ ⟨t', -, h⟩
          have := congrArg (Multiset.count 0) h
          rw [count_zero_hbLift, count_zero_hbLift] at this
          omega
    · rw [hyperbinaryReps_odd, (hbLift_injective 1).encard_image, ih k (by omega), rec1]

/-- There are only finitely many hyperbinary representations of `n`. -/
theorem hyperbinaryReps_finite (n : ℕ) : (hyperbinaryReps n).Finite := by
  apply Set.finite_of_encard_eq_coe (k := diatomic n)
  exact encard_hyperbinaryReps n

/-- `b(n) = h(n)`: Stern's diatomic series counts hyperbinary representations. -/
theorem hyperbinary_eq_diatomic (n : ℕ) : hyperbinary n = diatomic n := by
  simp [hyperbinary, Set.ncard_def, encard_hyperbinaryReps]

/-- The number of hyperbinary representations satisfies the recursion `(1)`. -/
theorem hyperbinary_recursion :
    hyperbinary 0 = 1 ∧ (∀ n, hyperbinary (2 * n + 1) = hyperbinary n) ∧
      (∀ n, hyperbinary (2 * n + 2) = hyperbinary n + hyperbinary (n + 1)) := by
  obtain ⟨h0, h1, h2⟩ := diatomic_recursion
  simp only [hyperbinary_eq_diatomic]
  exact ⟨h0, h1, h2⟩

/-- The book's example: `h(6) = 3`, from `6 = 4 + 2 = 4 + 1 + 1 = 2 + 2 + 1 + 1`. -/
theorem hyperbinary_six : hyperbinary 6 = 3 := by
  rw [hyperbinary_eq_diatomic]
  simp [diatomic, stern]

/-- The "surprising fact": for every reduced fraction `r/s > 0` there is exactly one `n`
with `r = h(n)` and `s = h(n+1)`. -/
theorem existsUnique_hyperbinary {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s) :
    ∃! n, hyperbinary n = r ∧ hyperbinary (n + 1) = s := by
  simp only [hyperbinary_eq_diatomic]
  obtain ⟨m, hm, hmrs⟩ := cwNode_surjective hr hs hrs
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [cwNode_eq_diatomic, Prod.mk.injEq] at hmrs
  refine ⟨n, hmrs, ?_⟩
  rintro n' ⟨h1, h2⟩
  have := cwNode_injective (m := n' + 1) (m' := n + 1) (by omega) (by omega)
    (by rw [cwNode_eq_diatomic, cwNode_eq_diatomic, h1, h2, hmrs.1, hmrs.2])
  omega

end Hyperbinary

end Chapter19


/-! ======================================================================
## Part: Reals
====================================================================== -/

/-!
# Theorems 2 and 3: the real numbers, intervals and the plane

* Theorem 2 (Cantor's diagonal argument): `ℝ` is not countable.
* All intervals of positive length have the same size `𝔠`, including an explicit bijection
  `(0,1] → (0,1)`.
* Theorem 3: `ℝ²` has the same size as `ℝ` (and so do `ℂ` and `ℝⁿ`).
* `𝒫(ℕ)` has cardinality `𝔠`.

## Decimal digits

For a real `x` we use the `(i+1)`-st decimal digit `⌊x · 10^(i+1)⌋ mod 10`. For the numbers
produced in the diagonal argument (all of whose digits are `1` or `2`) this agrees with every
decimal expansion, so the subtlety about expansions ending in `000…` versus `999…` never
arises.
-/



namespace Chapter19

section Reals

open Cardinal Set

/-! ### Decimal digits -/

/-- The `(i+1)`-st decimal digit of `x`, i.e. `⌊x · 10^(i+1)⌋ mod 10`. -/
noncomputable def decDigit (x : ℝ) (i : ℕ) : ℤ := ⌊x * 10 ^ (i + 1)⌋ % 10

/-- The real number `0.d₀ d₁ d₂ …` with prescribed decimal digits. -/
noncomputable def decimal (d : ℕ → ℕ) : ℝ := ∑' i, (d i : ℝ) / 10 ^ (i + 1)

theorem decimal_term_le {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) (i : ℕ) :
    (d i : ℝ) / 10 ^ (i + 1) ≤ 8 / 10 * (1 / 10) ^ i := by
  have h8 : (d i : ℝ) ≤ 8 := by exact_mod_cast hd i
  rw [div_le_iff₀ (by positivity), one_div_pow, pow_succ]
  field_simp
  linarith

theorem summable_decimal_bound : Summable (fun i : ℕ => (8 / 10 : ℝ) * (1 / 10) ^ i) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

theorem summable_decimal {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) :
    Summable (fun i => (d i : ℝ) / 10 ^ (i + 1)) := by
  exact Summable.of_nonneg_of_le (fun i => by positivity) (decimal_term_le hd)
    summable_decimal_bound

theorem decimal_nonneg (d : ℕ → ℕ) : 0 ≤ decimal d := by
  exact tsum_nonneg (fun i => by positivity)

theorem decimal_lt_one {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) : decimal d < 1 := by
  calc decimal d ≤ ∑' i : ℕ, (8 / 10 : ℝ) * (1 / 10) ^ i :=
        Summable.tsum_le_tsum (decimal_term_le hd) (summable_decimal hd) summable_decimal_bound
    _ = 8 / 9 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ < 1 := by norm_num

theorem decimal_pos {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) (i : ℕ) (hi : 0 < d i) : 0 < decimal d := by
  exact (summable_decimal hd).tsum_pos (fun i => by positivity) i (by
    have : (0 : ℝ) < d i := by exact_mod_cast hi
    positivity)

/-- Shifting the digits: `10 · 0.d₀d₁d₂… = d₀ + 0.d₁d₂…`. -/
theorem ten_mul_decimal {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) :
    10 * decimal d = d 0 + decimal (fun i => d (i + 1)) := by
  unfold decimal
  rw [(summable_decimal hd).tsum_eq_zero_add, mul_add, ← tsum_mul_left]
  congr 1
  · field_simp; ring
  · congr 1; ext i; rw [pow_succ]; field_simp

theorem decimal_mul_pow {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) (k : ℕ) :
    ∃ N : ℤ, decimal d * 10 ^ k = N + decimal (fun i => d (i + k)) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    have h := ten_mul_decimal (d := fun i => d (i + k)) (fun i => hd _)
    refine ⟨10 * N + d k, ?_⟩
    have e : (fun i => d (i + 1 + k)) = (fun i => d (i + (k + 1))) := by
      ext i; congr 1; omega
    simp only [zero_add, e] at h
    rw [pow_succ, ← mul_assoc, hN]
    push_cast
    linarith

/-- The digits of `0.d₀d₁d₂…` (with all `dᵢ ≤ 8`) are the `dᵢ`. -/
theorem decDigit_decimal {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 8) (k : ℕ) :
    decDigit (decimal d) k = d k := by
  obtain ⟨N, hN⟩ := decimal_mul_pow hd k
  have h := ten_mul_decimal (d := fun i => d (i + k)) (fun i => hd _)
  have e : (fun i => d (i + 1 + k)) = (fun i => d (i + (k + 1))) := by
    ext i; congr 1; omega
  simp only [zero_add, e] at h
  have h0 := decimal_nonneg (fun i => d (i + (k + 1)))
  have h1 := decimal_lt_one (d := fun i => d (i + (k + 1))) (fun i => hd _)
  have hfl : ⌊decimal d * 10 ^ (k + 1)⌋ = 10 * N + d k := by
    rw [Int.floor_eq_iff]
    rw [pow_succ, ← mul_assoc, hN]
    push_cast
    constructor <;> linarith
  unfold decDigit
  rw [hfl]
  have := hd k
  omega

/-! ### Theorem 2 -/

/-- Any subset of a countable set is at most countable. -/
theorem countable_of_subset {α : Type*} {M N : Set α} (hM : M.Countable) (hNM : N ⊆ M) :
    N.Countable :=
  hM.mono hNM

/-- **Cantor's diagonal argument.** For every listing `r₁, r₂, r₃, …` of real numbers there is a
number `b ∈ (0,1]` which is not in the list: its `n`-th digit is the least element of `{1,2}`
different from the `n`-th digit of `rₙ`. -/
theorem cantor_diagonal (r : ℕ → ℝ) : ∃ b ∈ Ioc (0 : ℝ) 1, ∀ k, b ≠ r k := by
  classical
  let d : ℕ → ℕ := fun n => if decDigit (r n) n = 1 then 2 else 1
  have hd : ∀ i, d i ≤ 8 := fun i => by simp only [d]; split_ifs <;> norm_num
  have hpos : 0 < d 0 := by simp only [d]; split_ifs <;> norm_num
  refine ⟨decimal d, ⟨decimal_pos hd 0 hpos, (decimal_lt_one hd).le⟩, fun k hk => ?_⟩
  have h1 := decDigit_decimal hd k
  rw [hk] at h1
  simp only [d] at h1
  split_ifs at h1 with h <;> push_cast at h1 <;> omega

/-- The interval `(0,1]` is not countable. -/
theorem Ioc_not_countable : ¬ (Ioc (0 : ℝ) 1).Countable := by
  intro hc
  obtain ⟨f, hf⟩ := hc.exists_eq_range ⟨1, by norm_num, le_rfl⟩
  obtain ⟨b, hb, hbk⟩ := cantor_diagonal f
  rw [hf] at hb
  obtain ⟨k, rfl⟩ := hb
  exact hbk k rfl

/-- **Theorem 2.** The set `ℝ` of real numbers is not countable. -/
theorem real_not_countable : ¬ Countable ℝ := by
  intro h
  exact Ioc_not_countable (Set.to_countable _)

/-! ### Intervals -/

/-- The index `k` with `1/2^(k+1) < x ≤ 1/2^k`, for `x ∈ (0,1]`. -/
noncomputable def halvingIndex (x : ℝ) : ℕ :=
  open Classical in
  if h : 0 < x then Nat.find (show ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < x from
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one h (by norm_num : (1 / 2 : ℝ) < 1)
    ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn⟩)
  else 0

/-- The book's map `(0,1] → (0,1)`: `y = 3/2 - x` for `1/2 < x ≤ 1`, `y = 3/4 - x` for
`1/4 < x ≤ 1/2`, `y = 3/8 - x` for `1/8 < x ≤ 1/4`, and so on. -/
noncomputable def halvingMap (x : ℝ) : ℝ := 3 * (1 / 2 : ℝ) ^ (halvingIndex x + 1) - x

theorem half_pow_succ (k : ℕ) : (1 / 2 : ℝ) ^ k = 2 * (1 / 2) ^ (k + 1) := by
  rw [pow_succ]; ring

theorem halvingIndex_spec {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    (1 / 2 : ℝ) ^ (halvingIndex x + 1) < x ∧ x ≤ (1 / 2 : ℝ) ^ halvingIndex x := by
  classical
  have hex : ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx.1 (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn⟩
  have hidx : halvingIndex x = Nat.find hex := by
    unfold halvingIndex
    rw [dite_cond_eq_true (eq_true hx.1)]
  rw [hidx]
  refine ⟨Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simpa using hx.2
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    rw [hj]
    exact not_lt.mp this

theorem index_unique_Ioc {x : ℝ} {k k' : ℕ} (h1 : (1 / 2 : ℝ) ^ (k + 1) < x)
    (h2 : x ≤ (1 / 2 : ℝ) ^ k) (h1' : (1 / 2 : ℝ) ^ (k' + 1) < x) (h2' : x ≤ (1 / 2 : ℝ) ^ k') :
    k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k + 1 ≤ k' by omega)
    linarith
  · exact h
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k' + 1 ≤ k by omega)
    linarith

theorem index_unique_Ico {x : ℝ} {k k' : ℕ} (h1 : (1 / 2 : ℝ) ^ (k + 1) ≤ x)
    (h2 : x < (1 / 2 : ℝ) ^ k) (h1' : (1 / 2 : ℝ) ^ (k' + 1) ≤ x) (h2' : x < (1 / 2 : ℝ) ^ k') :
    k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k + 1 ≤ k' by omega)
    linarith
  · exact h
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k' + 1 ≤ k by omega)
    linarith

theorem exists_index_Ico {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) ≤ y ∧ y < (1 / 2 : ℝ) ^ j := by
  classical
  have hex : ∃ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) ≤ y := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hy.1 (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, le_of_lt (lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simpa using hy.2
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    rw [hj]
    exact not_le.mp this

theorem halvingMap_mem {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : halvingMap x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := halvingIndex_spec hx
  have hp := half_pow_succ (halvingIndex x)
  unfold halvingMap
  have h3 : (1 / 2 : ℝ) ^ halvingIndex x ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> linarith

/-- The map `(0,1] → (0,1)` from the book is a bijection. -/
theorem halvingMap_bijective :
    Function.Bijective (fun x : Ioc (0 : ℝ) 1 => (⟨halvingMap x, halvingMap_mem x.2⟩ : Ioo (0 : ℝ) 1)) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    simp only [Subtype.mk.injEq, halvingMap] at h
    obtain ⟨h1, h2⟩ := halvingIndex_spec hx
    obtain ⟨h1', h2'⟩ := halvingIndex_spec hx'
    have hp := half_pow_succ (halvingIndex x)
    have hp' := half_pow_succ (halvingIndex x')
    have hk : halvingIndex x = halvingIndex x' := by
      apply index_unique_Ico (x := 3 * (1 / 2 : ℝ) ^ (halvingIndex x + 1) - x)
      · linarith
      · linarith
      · rw [h]; linarith
      · rw [h]; linarith
    rw [hk] at h
    exact Subtype.ext (by linarith)
  · rintro ⟨y, hy⟩
    obtain ⟨j, hj1, hj2⟩ := exists_index_Ico hy
    have hj3 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < (1 / 2) ^ (j + 1) := by positivity
    have hp := half_pow_succ j
    have hx1 : (1 / 2 : ℝ) ^ (j + 1) < 3 * (1 / 2 : ℝ) ^ (j + 1) - y := by linarith
    have hx2 : 3 * (1 / 2 : ℝ) ^ (j + 1) - y ≤ (1 / 2 : ℝ) ^ j := by linarith
    have hx : 3 * (1 / 2 : ℝ) ^ (j + 1) - y ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
    obtain ⟨h1, h2⟩ := halvingIndex_spec hx
    have hk : halvingIndex (3 * (1 / 2 : ℝ) ^ (j + 1) - y) = j := index_unique_Ioc h1 h2 hx1 hx2
    simp only [halvingMap, hk]
    ring

/-- Every interval of positive length (open, half-open, closed, finite or infinite) has the same
size `𝔠` as the whole real line. -/
theorem intervals_card {a b : ℝ} (hab : a < b) :
    #(Ioo a b) = 𝔠 ∧ #(Ico a b) = 𝔠 ∧ #(Ioc a b) = 𝔠 ∧ #(Icc a b) = 𝔠 ∧
      #(Ioi a) = 𝔠 ∧ #(Ici a) = 𝔠 ∧ #(Iio a) = 𝔠 ∧ #(Iic a) = 𝔠 ∧ #ℝ = 𝔠 := by
  exact ⟨mk_Ioo_real hab, mk_Ico_real hab, mk_Ioc_real hab, mk_Icc_real hab, mk_Ioi_real a,
    mk_Ici_real a, mk_Iio_real a, mk_Iic_real a, mk_real⟩

/-- Any two intervals of positive length have the same size. -/
theorem Ioo_equiv_Ioo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Nonempty (Ioo a b ≃ Ioo c d) := by
  exact Cardinal.eq.mp ((mk_Ioo_real hab).trans (mk_Ioo_real hcd).symm)

/-- Every open interval has the same size as `ℝ`. -/
theorem Ioo_equiv_real {a b : ℝ} (hab : a < b) : Nonempty (Ioo a b ≃ ℝ) := by
  exact Cardinal.eq.mp ((mk_Ioo_real hab).trans mk_real.symm)

/-! ### Theorem 3 -/

/-- **Theorem 3.** The plane `ℝ²` has the same size as `ℝ`. -/
theorem card_real_prod : #(ℝ × ℝ) = #ℝ := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, mk_real, Cardinal.mul_eq_self aleph0_le_continuum]

/-- **Theorem 3**, as a bijection. -/
theorem real_prod_equiv_real : Nonempty (ℝ × ℝ ≃ ℝ) := by
  exact Cardinal.eq.mp card_real_prod

/-- `|ℂ| = |ℝ| = 𝔠`, via the bijection `(x, y) ↦ x + iy`. -/
theorem card_complex : #ℂ = #ℝ ∧ #ℂ = 𝔠 := by
  exact ⟨mk_complex.trans mk_real.symm, mk_complex⟩

/-- More generally `ℝⁿ` has the same size as `ℝ` for every `n ≥ 1`. -/
theorem card_real_pi {n : ℕ} (hn : 1 ≤ n) : #(Fin n → ℝ) = #ℝ := by
  rw [Cardinal.mk_arrow, mk_fin, Cardinal.lift_id, Cardinal.lift_natCast, mk_real,
    Cardinal.power_natCast, power_nat_eq aleph0_le_continuum hn]

/-! ### `𝒫(ℕ)` has cardinality `𝔠` -/

/-- The book's injection `A ↦ ∑_{i ∈ A} 10^(-i)` from subsets of `ℕ` into `[0,1]`
(we index digits from `0`, i.e. `A ↦ ∑_{i ∈ A} 10^(-(i+1))`). -/
noncomputable def powersetToReal (A : Set ℕ) : ℝ :=
  open Classical in decimal (fun i => if i ∈ A then 1 else 0)

theorem powersetToReal_injective : Function.Injective powersetToReal := by
  classical
  have hd : ∀ (A : Set ℕ) (i : ℕ), (fun i => if i ∈ A then 1 else 0) i ≤ 8 := by
    intro A i; simp only; split_ifs <;> norm_num
  intro A B h
  ext i
  have hA := decDigit_decimal (hd A) i
  have hB := decDigit_decimal (hd B) i
  have hAB : decDigit (powersetToReal A) i = decDigit (powersetToReal B) i := by rw [h]
  unfold powersetToReal at hAB
  rw [hA, hB] at hAB
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp_all

/-- Nonempty sets are sent into `(0,1]`. -/
theorem powersetToReal_mem {A : Set ℕ} (hA : A.Nonempty) : powersetToReal A ∈ Ioc (0 : ℝ) 1 := by
  classical
  have hd : ∀ i, (fun i => if i ∈ A then 1 else 0) i ≤ 8 := by
    intro i; simp only; split_ifs <;> norm_num
  obtain ⟨i, hi⟩ := hA
  exact ⟨decimal_pos hd i (by simp [hi]), (decimal_lt_one hd).le⟩

/-- The set `𝒫(ℕ)` of all subsets of `ℕ` has cardinality `𝔠`. -/
theorem card_set_nat : #(Set ℕ) = 𝔠 := by
  rw [Cardinal.mk_set, mk_nat, Cardinal.two_power_aleph0]

end Reals

end Chapter19


/-! ======================================================================
## Part: Cardinals
====================================================================== -/

/-!
# Comparing cardinalities: Theorem 4 (Cantor–Bernstein) and the continuum hypothesis

* `#M ≤ #N` means that there is an injection `M → N`.
* Theorem 4 (Cantor–Bernstein), with Julius König's proof by chains.
* Trichotomy and transitivity for cardinals, `ℵ₀` is the smallest infinite cardinal.
* Hilbert's hotel for every infinite set, and the characterization of infinite sets as those
  having the same size as a proper subset.
* The continuum hypothesis `𝔠 = ℵ₁`, and its equivalent form "there is no cardinal strictly
  between `ℵ₀` and `𝔠`".

The theorem of Gödel and Cohen that the continuum hypothesis is independent of the
Zermelo–Fraenkel axioms is a metamathematical statement about provability and is *not*
formalized here.
-/



namespace Chapter19

section Cardinals

open Cardinal Function Set

universe u v

/-- `m ≤ n` for cardinal numbers means that there is an injection from a set of size `m` into
a set of size `n`. -/
theorem card_le_iff_exists_injective (M N : Type u) :
    #M ≤ #N ↔ ∃ f : M → N, Injective f := by
  rw [Cardinal.le_def]
  exact ⟨fun ⟨e⟩ => ⟨e, e.injective⟩, fun ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩⟩

/-- For finite cardinals, `≤` is the usual order: an `m`-set is at most as large as an
`n`-set iff `m ≤ n`. -/
theorem natCast_card_le_iff (m n : ℕ) : (m : Cardinal) ≤ n ↔ m ≤ n := Nat.cast_le

section CantorBernstein

variable {M : Type u} {N : Type v} (f : M → N) (g : N → M)

/-- The elements of `M` lying on a chain of Case 4, i.e. a chain which, followed backwards,
stops at an element `n₀ ∈ N \ f(M)`: these are the elements `(g ∘ f)^[k] (g n₀)`. -/
def case4Chains : Set M :=
  {m | ∃ n₀ ∉ range f, ∃ k : ℕ, m = (g ∘ f)^[k] (g n₀)}

/-- König's bijection: `m ↦ g⁻¹ m` on chains of Case 4, and `m ↦ f m` on all other chains. -/
noncomputable def koenigMap [Nonempty N] : M → N :=
  open Classical in fun m => if m ∈ case4Chains f g then invFun g m else f m

theorem koenigMap_bijective [Nonempty N] (hf : Injective f) (hg : Injective g) :
    Bijective (koenigMap f g) := by
  classical
  have hginv : ∀ n, invFun g (g n) = n := fun n => leftInverse_invFun hg n
  have hA_succ : ∀ m, m ∈ case4Chains f g → g (f m) ∈ case4Chains f g := by
    rintro m ⟨n₀, hn₀, k, rfl⟩
    exact ⟨n₀, hn₀, k + 1, by rw [iterate_succ_apply']; rfl⟩
  have hA_g : ∀ m ∈ case4Chains f g, ∃ n, g n = m ∧
      (n ∉ range f ∨ ∃ m' ∈ case4Chains f g, n = f m') := by
    rintro m ⟨n₀, hn₀, k, rfl⟩
    rcases k with _ | k
    · exact ⟨n₀, rfl, Or.inl hn₀⟩
    · exact ⟨f ((g ∘ f)^[k] (g n₀)), by rw [iterate_succ_apply']; rfl,
        Or.inr ⟨_, ⟨n₀, hn₀, k, rfl⟩, rfl⟩⟩
  have hK : ∀ m, koenigMap f g m = if m ∈ case4Chains f g then invFun g m else f m := by
    intro m; unfold koenigMap; congr
  have key : ∀ m m', m ∈ case4Chains f g → m' ∉ case4Chains f g → invFun g m ≠ f m' := by
    intro m m' h1 h2 h
    obtain ⟨n, rfl, hn⟩ := hA_g m h1
    rw [hginv] at h
    subst h
    rcases hn with hn | ⟨m'', hm'', he⟩
    · exact hn ⟨m', rfl⟩
    · rw [hf he] at h2
      exact h2 hm''
  constructor
  · intro m m' h
    rw [hK, hK] at h
    split_ifs at h with h1 h2 h2
    · obtain ⟨n, rfl, -⟩ := hA_g m h1
      obtain ⟨n', rfl, -⟩ := hA_g m' h2
      rw [hginv, hginv] at h
      rw [h]
    · exact absurd h (key m m' h1 h2)
    · exact absurd h.symm (key m' m h2 h1)
    · exact hf h
  · intro n
    by_cases h : g n ∈ case4Chains f g
    · exact ⟨g n, by rw [hK, ite_cond_eq_true _ _ (eq_true h), hginv]⟩
    · have hn : n ∈ range f := by
        by_contra hn
        exact h ⟨n, hn, 0, rfl⟩
      obtain ⟨m, rfl⟩ := hn
      have hm : m ∉ case4Chains f g := fun hm => h (hA_succ m hm)
      exact ⟨m, by rw [hK, ite_cond_eq_false _ _ (eq_false hm)]⟩

/-- **Theorem 4 (Cantor–Bernstein).** If each of two sets `M` and `N` can be mapped injectively
into the other, then there is a bijection from `M` to `N`. -/
theorem cantor_bernstein (hf : Injective f) (hg : Injective g) : ∃ h : M → N, Bijective h := by
  rcases isEmpty_or_nonempty N with hN | hN
  · have : IsEmpty M := ⟨fun m => hN.false (f m)⟩
    exact ⟨f, hf, fun n => hN.elim n⟩
  · exact ⟨koenigMap f g, koenigMap_bijective f g hf hg⟩

end CantorBernstein

/-- Consequently `m ≤ n` and `n ≤ m` imply `m = n` for cardinal numbers. -/
theorem card_eq_of_le_of_le {M N : Type u} (h₁ : #M ≤ #N) (h₂ : #N ≤ #M) : #M = #N := by
  obtain ⟨f, hf⟩ := (card_le_iff_exists_injective M N).1 h₁
  obtain ⟨g, hg⟩ := (card_le_iff_exists_injective N M).1 h₂
  obtain ⟨h, hh⟩ := cantor_bernstein f g hf hg
  exact Cardinal.mk_congr (Equiv.ofBijective h hh)

/-- For any two cardinals precisely one of `m < n`, `m = n`, `m > n` holds. -/
theorem cardinal_trichotomy (m n : Cardinal.{u}) :
    (m < n ∧ ¬ m = n ∧ ¬ n < m) ∨ (¬ m < n ∧ m = n ∧ ¬ n < m) ∨ (¬ m < n ∧ ¬ m = n ∧ n < m) := by
  rcases lt_trichotomy m n with h | h | h
  · exact Or.inl ⟨h, h.ne, not_lt.mpr h.le⟩
  · exact Or.inr (Or.inl ⟨h.not_lt, h, h.symm.not_lt⟩)
  · exact Or.inr (Or.inr ⟨not_lt.mpr h.le, h.ne', h⟩)

/-- The relation `<` on cardinals is transitive. -/
theorem cardinal_lt_trans {m n p : Cardinal.{u}} (h₁ : m < n) (h₂ : n < p) : m < p :=
  h₁.trans h₂

/-- Every infinite set contains a countable subset `{m₁, m₂, m₃, …}`. -/
theorem exists_nat_injective_of_infinite (M : Type u) [Infinite M] : ∃ f : ℕ → M, Injective f :=
  ⟨Infinite.natEmbedding M, (Infinite.natEmbedding M).injective⟩

/-- `ℵ₀ ≤ m` for every infinite cardinal `m`: the size of a countable set is the smallest
infinite cardinal. -/
theorem aleph0_le_of_infinite (M : Type u) [Infinite M] : ℵ₀ ≤ #M := by
  exact Cardinal.infinite_iff.mp inferInstance

/-- A set is infinite iff its cardinality is at least `ℵ₀`. -/
theorem infinite_iff_aleph0_le (M : Type u) : Infinite M ↔ ℵ₀ ≤ #M := Cardinal.infinite_iff

/-- **Hilbert's hotel** for every infinite set: `|M ∪ {x}| = |M|`. Here `Option M` is `M`
together with one new element. -/
theorem hilbert_hotel (M : Type u) [Infinite M] : Nonempty (Option M ≃ M) := by
  exact Cardinal.eq.mp (by rw [mk_option, add_one_of_aleph0_le (aleph0_le_of_infinite M)])

/-- Hilbert's hotel for subsets: if `S` is infinite and `x ∉ S`, then `|S ∪ {x}| = |S|`. -/
theorem hilbert_hotel_set {α : Type u} {S : Set α} (hS : S.Infinite) {x : α} (hx : x ∉ S) :
    #(insert x S : Set α) = #S := by
  have := hS.to_subtype
  rw [mk_insert hx, add_one_of_aleph0_le (aleph0_le_of_infinite S)]

/-- A set is infinite if and only if it has the same size as some proper subset. -/
theorem infinite_iff_exists_proper_subset_equiv (M : Type u) :
    Infinite M ↔ ∃ S : Set M, S ≠ Set.univ ∧ Nonempty (S ≃ M) := by
  constructor
  · intro hM
    obtain ⟨e⟩ := hilbert_hotel M
    refine ⟨range (e ∘ some), ?_,
      ⟨(Equiv.ofInjective _ (e.injective.comp (Option.some_injective M))).symm⟩⟩
    intro h
    have : e none ∈ range (e ∘ some) := h ▸ mem_univ _
    obtain ⟨m, hm⟩ := this
    exact Option.some_ne_none m (e.injective hm)
  · rintro ⟨S, hS, ⟨e⟩⟩
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
      by_contra h
      push Not at h
      exact hS (eq_univ_of_forall h)
    have hinj : Injective (fun m => (e.symm m : M)) := Subtype.val_injective.comp e.symm.injective
    obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hinj x
    exact hx (hm ▸ (e.symm m).2)

/-! ### The continuum hypothesis -/

/-- The continuum hypothesis: `𝔠 = ℵ₁`. -/
def ContinuumHypothesis : Prop := (𝔠 : Cardinal.{0}) = ℵ_ 1

/-- `ℵ₀ < 𝔠`: the cardinality of `ℝ` is bigger than that of `ℚ`. -/
theorem aleph0_lt_continuum' : (ℵ₀ : Cardinal.{0}) < 𝔠 := Cardinal.aleph0_lt_continuum

/-- `ℵ₁` is the next cardinal number after `ℵ₀`. -/
theorem aleph_one_is_next : (ℵ₀ : Cardinal.{u}) < ℵ_ 1 ∧ ∀ c : Cardinal.{u}, ℵ₀ < c → ℵ_ 1 ≤ c := by
  exact ⟨aleph0_lt_aleph_one, fun c hc => succ_aleph0 ▸ Order.succ_le_of_lt hc⟩

/-- The continuum hypothesis says precisely that `𝔠` is the next infinite cardinal after `ℵ₀`,
i.e. there is no cardinal strictly between `ℵ₀` and `𝔠`. -/
theorem continuumHypothesis_iff : ContinuumHypothesis ↔ ¬ ∃ c : Cardinal.{0}, ℵ₀ < c ∧ c < 𝔠 := by
  unfold ContinuumHypothesis
  constructor
  · rintro h ⟨c, h1, h2⟩
    have := aleph_one_is_next.2 c h1
    rw [h] at h2
    exact absurd h2 (not_lt.mpr this)
  · intro h
    by_contra hne
    exact h ⟨ℵ_ 1, aleph_one_is_next.1, lt_of_le_of_ne aleph_one_le_continuum (Ne.symm hne)⟩

end Cardinals

end Chapter19


/-! ======================================================================
## Part: Appendix
====================================================================== -/

/-!
# Appendix: On cardinal and ordinal numbers

* Cantor's theorem `|M| < |𝒫(M)|` with the barber argument; hence there is always a larger
  cardinal.
* Ordered and well-ordered sets, similarity (order isomorphism), ordinal numbers.
* `ω ≤ α` for every infinite ordinal `α`; the orderings `1, 2, 3, …` and `1, 3, 5, …, 2, 4, 6, …`
  of `ℕ` are not similar.
* Propositions 1–6 of the appendix.

In Lean, an *ordered set* in the sense of the book is a type with a `LinearOrder`, a
*well-ordered set* is one which is in addition `WellFoundedLT`, *similar* well-ordered sets are
related by an order isomorphism `≃o`, ordinal numbers are `Ordinal`, the ordinal number of a
well-ordered set `α` is `typeLT α`, cardinal numbers are `Cardinal`, and the *initial ordinal
number* `ω_m` of a cardinal `m` is `m.ord`.
-/



namespace Chapter19

section Appendix

open Cardinal Ordinal Set Function

universe u

/-! ### Cantor's theorem -/

/-- The barber argument: no map `φ : M → 𝒫(M)` is surjective. -/
theorem cantor_not_surjective {M : Type u} (φ : M → Set M) : ¬ Surjective φ := by
  intro h
  obtain ⟨u, hu⟩ := h {m | m ∉ φ m}
  have key : u ∈ φ u ↔ u ∉ φ u := by
    constructor
    · intro h1; rw [hu] at h1; exact h1
    · intro h1; rw [hu]; exact h1
  exact iff_not_self key

/-- The book's formulation: `𝒫(M)` cannot be mapped bijectively onto a subset `N` of `M`. -/
theorem cantor_no_bijection_from_subset {M : Type u} (N : Set M) : IsEmpty (N ≃ Set M) := by
  refine ⟨fun φ => ?_⟩
  let U : Set M := {m | ∃ h : m ∈ N, m ∉ φ ⟨m, h⟩}
  set u := φ.symm U
  have hu : φ u = U := φ.apply_symm_apply U
  by_cases h : (u : M) ∈ U
  · have h' := h
    obtain ⟨hN, hnot⟩ := h'
    rw [show (⟨(u : M), hN⟩ : N) = u from Subtype.ext rfl, hu] at hnot
    exact hnot h
  · apply h
    refine ⟨u.2, ?_⟩
    rw [show (⟨(u : M), u.2⟩ : N) = u from Subtype.ext rfl, hu]
    exact h

/-- **Cantor's theorem.** The set `𝒫(M)` of all subsets of `M` has larger size than `M`. -/
theorem card_lt_card_powerset (M : Type u) : #M < #(Set M) := by
  refine lt_of_le_of_ne (Cardinal.mk_le_of_injective (f := fun m => ({m} : Set M))
    Set.singleton_injective) ?_
  intro h
  obtain ⟨e⟩ := Cardinal.eq.mp h
  exact cantor_not_surjective e e.surjective

/-- To every cardinal number `m` there is a larger cardinal number. -/
theorem exists_larger_cardinal (m : Cardinal.{u}) : ∃ n, m < n := by
  induction m using Cardinal.inductionOn with
  | _ M => exact ⟨#(Set M), card_lt_card_powerset M⟩

/-! ### Ordered and well-ordered sets -/

/-- `ℕ` in its usual order `1, 2, 3, …` is well-ordered. -/
theorem nat_wellOrdered : WellFounded (· < · : ℕ → ℕ → Prop) := wellFounded_lt

/-- `ℕ` ordered the other way round, `…, 4, 3, 2, 1`, is not well-ordered. -/
theorem nat_reverse_not_wellOrdered : ¬ WellFounded (· > · : ℕ → ℕ → Prop) := by
  intro h
  obtain ⟨m, -, hm⟩ := h.has_min Set.univ ⟨0, trivial⟩
  exact hm (m + 1) trivial (Nat.lt_succ_self m)

/-- The ordering `1, 3, 5, …, 2, 4, 6, …` (first the odd numbers, then the even numbers):
we model it as the lexicographic sum `ℕ ⊕ ℕ` of two copies of `ℕ` (the left copy listing the
odd numbers, the right copy the even numbers). -/
abbrev oddsThenEvens : ℕ ⊕ ℕ → ℕ ⊕ ℕ → Prop := Sum.Lex (· < ·) (· < ·)

/-- The ordering `1, 3, 5, …, 2, 4, 6, …` is a well-ordering. -/
theorem oddsThenEvens_wellOrdered : WellFounded oddsThenEvens :=
  Sum.lex_wf wellFounded_lt wellFounded_lt

/-- The well-ordered sets `1, 2, 3, …` and `1, 3, 5, …, 2, 4, 6, …` are not similar. -/
theorem nat_not_similar_oddsThenEvens : IsEmpty ((· < · : ℕ → ℕ → Prop) ≃r oddsThenEvens) := by
  refine ⟨fun e => ?_⟩
  set a := e.symm (Sum.inr 0)
  have hlt : ∀ n, e.symm (Sum.inl n) < a := by
    intro n
    have : oddsThenEvens (Sum.inl n) (Sum.inr 0) := Sum.Lex.sep _ _
    rw [← e.apply_symm_apply (Sum.inl n), ← e.apply_symm_apply (Sum.inr 0)] at this
    exact e.map_rel_iff.mp this
  have hinj : Function.Injective (fun n => e.symm (Sum.inl n)) :=
    fun n m h => Sum.inl_injective (e.symm.injective h)
  exact Set.infinite_range_of_injective hinj
    ((Set.finite_Iio a).subset (by rintro _ ⟨n, rfl⟩; exact hlt n))

/-- Any ordered set which is similar to a well-ordered set is itself well-ordered. -/
theorem wellFoundedLT_of_similar {α β : Type*} [LinearOrder α] [LinearOrder β] (e : α ≃o β)
    [WellFoundedLT β] : WellFoundedLT α := by
  exact e.toOrderEmbedding.wellFoundedLT

/-- Any subset of a well-ordered set is well-ordered under the induced ordering. -/
theorem wellFoundedLT_subset {α : Type*} [LinearOrder α] [WellFoundedLT α] (S : Set α) :
    WellFoundedLT S := inferInstance

/-- Similar well-ordered sets have the same ordinal number, and the same cardinality. -/
theorem similar_same_type_and_card {α β : Type u} [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] (e : α ≃o β) : typeLT α = typeLT β ∧ #α = #β := by
  exact ⟨Ordinal.type_eq.mpr ⟨e.toRelIsoLT⟩, Cardinal.mk_congr e.toEquiv⟩

/-- `n < ω` for every finite ordinal `n`. -/
theorem nat_lt_omega (n : ℕ) : (n : Ordinal) < ω := Ordinal.lt_omega0.mpr ⟨n, rfl⟩

/-- `ω ≤ α` for every infinite ordinal number `α`. -/
theorem omega_le_type_of_infinite (α : Type u) [LinearOrder α] [WellFoundedLT α] [Infinite α] :
    ω ≤ typeLT α := by
  calc ω = (ℵ₀ : Cardinal.{u}).ord := ord_aleph0.symm
    _ ≤ (#α).ord := ord_le_ord.mpr (aleph0_le_mk α)
    _ ≤ typeLT α := ord_le_type _

/-- The ordinal number of `1, 2, 3, …` is `ω`, that of `1, 3, 5, …, 2, 4, 6, …` is `ω + ω`, and
the first is smaller than the second. -/
theorem type_nat_lt_type_oddsThenEvens :
    typeLT ℕ = ω ∧ type oddsThenEvens = ω + ω ∧ ω < ω + ω := by
  refine ⟨type_nat_lt, ?_, lt_add_of_pos_right _ omega0_pos⟩
  unfold oddsThenEvens
  rw [type_sum_lex, type_nat_lt]

/-! ### Propositions 1–3 -/

/-- **Proposition 1.** Let `μ` be an ordinal number and `W_μ` the set of ordinal numbers smaller
than `μ`. Then (i) the elements of `W_μ` are pairwise comparable, and (ii) ordered by magnitude,
`W_μ` is well-ordered and has ordinal number `μ`. -/
theorem proposition1 (μ : Ordinal.{u}) :
    (∀ a b : Iio μ, a ≤ b ∨ b ≤ a) ∧ WellFoundedLT (Iio μ) ∧
      typeLT (Iio μ) = Ordinal.lift.{u + 1} μ := by
  refine ⟨fun a b => le_total a b, inferInstance, ?_⟩
  have h := (Ordinal.lift_type_eq.{u + 1, u, u} (r := (· < · : Iio μ → Iio μ → Prop))
    (s := (· < · : μ.ToType → μ.ToType → Prop))).2 ⟨Ordinal.ToType.mk.toRelIsoLT⟩
  rw [Ordinal.type_toType, Ordinal.lift_id'.{u, u + 1}] at h
  exact h

/-- **Proposition 2.** Any two ordinal numbers `μ` and `ν` satisfy precisely one of the relations
`μ < ν`, `μ = ν`, `μ > ν`. -/
theorem proposition2 (μ ν : Ordinal.{u}) :
    (μ < ν ∧ ¬ μ = ν ∧ ¬ ν < μ) ∨ (¬ μ < ν ∧ μ = ν ∧ ¬ ν < μ) ∨ (¬ μ < ν ∧ ¬ μ = ν ∧ ν < μ) := by
  rcases lt_trichotomy μ ν with h | h | h
  · exact Or.inl ⟨h, h.ne, not_lt.mpr h.le⟩
  · exact Or.inr (Or.inl ⟨h.not_lt, h, h.symm.not_lt⟩)
  · exact Or.inr (Or.inr ⟨not_lt.mpr h.le, h.ne', h⟩)

/-- **Proposition 3.** Every set of ordinal numbers is well-ordered: every nonempty set of
ordinals has a smallest element. -/
theorem proposition3 (S : Set Ordinal.{u}) (hS : S.Nonempty) : ∃ μ ∈ S, ∀ ν ∈ S, μ ≤ ν := by
  obtain ⟨m, hm, hmin⟩ := wellFounded_lt.has_min S hS
  exact ⟨m, hm, fun ν hν => not_lt.mp (hmin ν hν)⟩

/-- The initial ordinal number `ω_m = m.ord` of a cardinal `m` is the smallest ordinal number
with cardinality `m`. -/
theorem initial_ordinal_spec (m : Cardinal.{u}) :
    m.ord.card = m ∧ ∀ μ : Ordinal.{u}, μ.card = m → m.ord ≤ μ := by
  exact ⟨Cardinal.card_ord m, fun μ hμ => Cardinal.ord_le.mpr hμ.ge⟩

/-- `ω` is the initial ordinal number of `ℵ₀`. -/
theorem initial_ordinal_aleph0 : (ℵ₀ : Cardinal.{u}).ord = ω := Cardinal.ord_aleph0

/-! ### Propositions 4–6 -/

/-- **Proposition 4.** For every cardinal number `m` there is a definite next larger cardinal
number. -/
theorem proposition4 (m : Cardinal.{u}) : ∃ n, m < n ∧ ∀ p, m < p → n ≤ p := by
  obtain ⟨p, hp, hmin⟩ := Cardinal.lt_wf.has_min {p | m < p} (exists_larger_cardinal m)
  exact ⟨p, hp, fun q hq => not_lt.mp (hmin q hq)⟩

/-- A set is countable iff its cardinality is less than `ℵ₁`. -/
theorem set_countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ_ 1 := by
  rw [← succ_aleph0, Order.lt_succ_iff, le_aleph0_iff_set_countable]

/-- In the initial well-order of cardinality `c`, every initial segment has cardinality `< c`. -/
theorem mk_Iio_lt_of_toType_ord {c : Cardinal.{u}} (i : c.ord.ToType) : #(Iio i) < c := by
  first
  | exact Cardinal.mk_Iio_toType_ord_lt i
  | exact Cardinal.mk_Iio_toType_ord_lt _ i
  | exact Cardinal.mk_Iio_toType_ord_lt
  | exact Cardinal.card_typein_toType_lt c i

/-- **Proposition 5.** Let the infinite set `M` have cardinality `m`, and let `M` be well-ordered
according to the initial ordinal number `ω_m`. Then `M` has no last element. -/
theorem proposition5 (m : Cardinal.{u}) (hm : ℵ₀ ≤ m) (x : m.ord.ToType) : ∃ y, x < y := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set m.ord.ToType) ⊆ insert x (Iio x) := by
    intro y _
    rcases (h y).lt_or_eq with hy | hy
    · exact Or.inr hy
    · exact Or.inl hy
  have h1 := mk_Iio_lt_of_toType_ord x
  have h2 : #(Set.univ : Set m.ord.ToType) ≤ #(Iio x) + 1 :=
    (mk_le_mk_of_subset hsub).trans mk_insert_le
  rw [mk_univ, mk_ord_toType] at h2
  have h3 : #(Iio x) + 1 < m := add_lt_of_lt hm h1 (one_lt_aleph0.trans_le hm)
  exact absurd h2 (not_le.mpr h3)

/-- **Proposition 6.** Suppose `{A_α}` is a family of size `m` of countable sets, where `m` is an
infinite cardinal. Then the union `⋃ A_α` has size at most `m`. -/
theorem proposition6 {ι α : Type u} (A : ι → Set α) (hA : ∀ i, (A i).Countable) (hι : ℵ₀ ≤ #ι) :
    #(⋃ i, A i) ≤ #ι := by
  calc #(⋃ i, A i) ≤ #ι * ⨆ i, #(A i) := mk_iUnion_le A
    _ ≤ #ι * ℵ₀ := mul_le_mul_right (ciSup_le' fun i => le_aleph0_iff_set_countable.mpr (hA i)) _
    _ ≤ #ι * #ι := mul_le_mul_right hι _
    _ = #ι := mul_eq_self hι

end Appendix

end Chapter19


/-! ======================================================================
## Part: Interpolation
====================================================================== -/

/-!
# Analytic ingredients for Theorem 5

* The set `D` of complex numbers with rational real and imaginary parts is countable and dense.
* Two distinct entire functions agree in at most countably many points (they agree only in
  finitely many points of each disk `C_k`).
* The interpolation step of Erdős' construction: given a countable set of points `w₁, w₂, …` and
  forbidden values, there is an entire function
  `f(z) = ε₀ + ε₁ (z - w₁) + ε₂ (z - w₁)(z - w₂) + ⋯` whose value at each `wₙ` lies in `D` and
  differs from the forbidden value.
-/



namespace Chapter19

section Interpolation

open Complex Set Filter Topology

/-- The set `D` of complex numbers `p + iq` with rational real and imaginary part. -/
def gaussRat : Set ℂ := {z | ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * I}

/-- `D` is countable. -/
theorem gaussRat_countable : gaussRat.Countable := by
  have : gaussRat = range (fun pq : ℚ × ℚ => (pq.1 : ℂ) + (pq.2 : ℂ) * I) := by
    ext z
    simp only [gaussRat, mem_range, Prod.exists]
    constructor
    · rintro ⟨p, q, rfl⟩; exact ⟨p, q, rfl⟩
    · rintro ⟨p, q, rfl⟩; exact ⟨p, q, rfl⟩
  rw [this]
  exact countable_range _

/-- `D` is dense, even after removing one point: every open disk contains a point of `D`
different from any prescribed value `c`. -/
theorem gaussRat_dense_avoid (z c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ d ∈ gaussRat, d ≠ c ∧ ‖d - z‖ < r := by
  obtain ⟨p1, hp1a, hp1b⟩ := exists_rat_btwn (show z.re - r / 2 < z.re by linarith)
  obtain ⟨p2, hp2a, hp2b⟩ := exists_rat_btwn (show z.re < z.re + r / 2 by linarith)
  obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn (show z.im - r / 2 < z.im + r / 2 by linarith)
  have key : ∀ p : ℚ, z.re - r / 2 < p → (p : ℝ) < z.re + r / 2 → (p : ℝ) ≠ c.re →
      ∃ d ∈ gaussRat, d ≠ c ∧ ‖d - z‖ < r := by
    intro p h1 h2 h3
    refine ⟨(p : ℂ) + (q : ℂ) * I, ⟨p, q, rfl⟩, ?_, ?_⟩
    · intro h; apply h3; rw [← h]; simp
    · have e1 : ((p : ℂ) + (q : ℂ) * I - z).re = p - z.re := by simp
      have e2 : ((p : ℂ) + (q : ℂ) * I - z).im = q - z.im := by simp
      calc ‖(p : ℂ) + q * I - z‖ ≤ |((p : ℂ) + q * I - z).re| + |((p : ℂ) + q * I - z).im| :=
            norm_le_abs_re_add_abs_im _
        _ < r / 2 + r / 2 := by
            rw [e1, e2]
            apply add_lt_add <;> rw [abs_lt] <;> constructor <;> linarith
        _ = r := by ring
  by_cases h : (p1 : ℝ) = c.re
  · exact key p2 (by linarith) hp2b (by intro h'; linarith)
  · exact key p1 hp1a (by linarith) h

/-- Two distinct entire functions agree in at most countably many points. -/
theorem countable_setOf_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : f ≠ g) : {z | f z = g z}.Countable := by
  have han : AnalyticOnNhd ℂ (f - g) univ :=
    analyticOnNhd_univ_iff_differentiable.mpr (hf.sub hg)
  have hfin : ∀ k : ℕ, ({z | f z = g z} ∩ Metric.closedBall 0 k).Finite := by
    intro k
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
      (isCompact_closedBall 0 (k : ℝ)) inter_subset_right
    have hfreq : ∃ᶠ z in 𝓝[≠] x, (f - g) z = 0 := by
      rw [Filter.frequently_iff_neBot]
      refine Filter.NeBot.mono hx (inf_le_inf_left _ (principal_mono.mpr ?_))
      intro z hz
      simp only [Pi.sub_apply, sub_eq_zero]
      exact hz.1
    have h0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ x) hfreq
    apply hfg
    funext z
    have := h0 (mem_univ z)
    simpa [sub_eq_zero] using this
  have hU : {z | f z = g z} = ⋃ k : ℕ, ({z | f z = g z} ∩ Metric.closedBall 0 k) := by
    ext z
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := exists_nat_ge ‖z‖
      exact ⟨k, hz, by simpa using hk⟩
    · rintro ⟨k, hz, -⟩
      exact hz
  rw [hU]
  exact countable_iUnion (fun k => (hfin k).countable)

/-- The polynomial `(z - w₀)(z - w₁) ⋯ (z - w_{n-1})`. -/
noncomputable def interpProd (w : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ := ∏ k ∈ Finset.range n, (z - w k)

/-- The auxiliary bound `∏_{k<n} (1 + ‖w k‖)`. -/
noncomputable def interpBound (w : ℕ → ℂ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (1 + ‖w k‖)

theorem interpBound_pos (w : ℕ → ℂ) (n : ℕ) : 0 < interpBound w n :=
  Finset.prod_pos (fun k _ => by positivity)

theorem norm_interpProd_le (w : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    ‖interpProd w n z‖ ≤ (1 + ‖z‖) ^ n * interpBound w n := by
  unfold interpProd interpBound
  have h : (1 + ‖z‖) ^ n = ∏ _k ∈ Finset.range n, (1 + ‖z‖) := by simp [Finset.prod_const]
  rw [norm_prod, h, ← Finset.prod_mul_distrib]
  gcongr with k
  calc ‖z - w k‖ ≤ ‖z‖ + ‖w k‖ := norm_sub_le _ _
    _ ≤ (1 + ‖z‖) * (1 + ‖w k‖) := by nlinarith [norm_nonneg z, norm_nonneg (w k)]

theorem interpProd_eq_zero (w : ℕ → ℂ) {n m : ℕ} (hnm : n < m) : interpProd w m (w n) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hnm) (sub_self _)

theorem interpProd_ne_zero {w : ℕ → ℂ} (hw : Function.Injective w) (n : ℕ) :
    interpProd w n (w n) ≠ 0 := by
  unfold interpProd
  rw [Finset.prod_ne_zero_iff]
  intro k hk h
  have := hw (sub_eq_zero.mp h)
  simp only [Finset.mem_range] at hk
  omega

/-- The condition on the `n`-th coefficient `x = εₙ`, given the previous coefficients `p k`. -/
def interpCond (w c : ℕ → ℂ) (n : ℕ) (p : ℕ → ℂ) (x : ℂ) : Prop :=
  ‖x‖ ≤ 1 / ((n.factorial : ℝ) * interpBound w n) ∧
    (∑ k ∈ Finset.range n, p k * interpProd w k (w n)) + x * interpProd w n (w n) ∈ gaussRat ∧
    (∑ k ∈ Finset.range n, p k * interpProd w k (w n)) + x * interpProd w n (w n) ≠ c n

theorem interpCond_congr (w c : ℕ → ℂ) (n : ℕ) {p p' : ℕ → ℂ} (h : ∀ k < n, p k = p' k)
    (x : ℂ) : interpCond w c n p x ↔ interpCond w c n p' x := by
  have hs : ∑ k ∈ Finset.range n, p k * interpProd w k (w n) =
      ∑ k ∈ Finset.range n, p' k * interpProd w k (w n) :=
    Finset.sum_congr rfl (fun k hk => by rw [h k (Finset.mem_range.mp hk)])
  unfold interpCond
  rw [hs]

theorem interpCond_exists {w : ℕ → ℂ} (hw : Function.Injective w) (c : ℕ → ℂ) (n : ℕ)
    (p : ℕ → ℂ) : ∃ x, interpCond w c n p x := by
  set s := ∑ k ∈ Finset.range n, p k * interpProd w k (w n)
  set P := interpProd w n (w n)
  have hP : P ≠ 0 := interpProd_ne_zero hw n
  have hPn : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hδ : 0 < 1 / ((n.factorial : ℝ) * interpBound w n) := by
    have := interpBound_pos w n
    have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    positivity
  obtain ⟨d, hd, hdc, hds⟩ := gaussRat_dense_avoid s (c n) (mul_pos hδ hPn)
  refine ⟨(d - s) / P, ?_, ?_, ?_⟩
  · rw [norm_div, div_le_iff₀ hPn]
    exact hds.le
  · rw [div_mul_cancel₀ _ hP, add_sub_cancel]
    exact hd
  · rw [div_mul_cancel₀ _ hP, add_sub_cancel]
    exact hdc

/-- The interpolation step: for distinct points `w n` and forbidden values `c n` there is an
entire function `f` with `f (w n) ∈ D` and `f (w n) ≠ c n` for all `n`. -/
theorem exists_entire_seq (w : ℕ → ℂ) (hw : Function.Injective w) (c : ℕ → ℂ) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ n, f (w n) ∈ gaussRat ∧ f (w n) ≠ c n := by
  classical
  -- choose the coefficients `εₙ` step by step
  let ε : ℕ → ℂ := (wellFounded_lt : WellFounded (· < · : ℕ → ℕ → Prop)).fix
    (fun n IH => Classical.choose
      (interpCond_exists hw c n (fun k => if hk : k < n then IH k hk else 0)))
  have hε : ∀ n, interpCond w c n ε (ε n) := by
    intro n
    have e1 : ε n = Classical.choose
        (interpCond_exists hw c n (fun k => if hk : k < n then ε k else 0)) :=
      WellFounded.fix_eq _ _ _
    have h1 := Classical.choose_spec
      (interpCond_exists hw c n (fun k => if hk : k < n then ε k else 0))
    rw [← e1] at h1
    exact (interpCond_congr w c n (fun k hk => by simp [hk]) _).mp h1
  -- the series `∑ εₙ (z - w₀) ⋯ (z - w_{n-1})`
  refine ⟨fun z => ∑' n, ε n * interpProd w n z, ?_, ?_⟩
  · intro z₀
    set R := ‖z₀‖ + 1
    have hU : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
    have hz₀ : z₀ ∈ Metric.ball (0 : ℂ) R := by simp [R]
    have hd : DifferentiableOn ℂ (fun z => ∑' n, ε n * interpProd w n z) (Metric.ball 0 R) := by
      refine differentiableOn_tsum_of_summable_norm
        (u := fun n => (1 + R) ^ n / (n.factorial : ℝ)) (Real.summable_pow_div_factorial _)
        (fun n => ?_) hU (fun n z hz => ?_)
      · apply Differentiable.differentiableOn
        unfold interpProd
        fun_prop
      · have hzR : ‖z‖ ≤ R := by
          rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le
        have hB := interpBound_pos w n
        have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
        rw [norm_mul]
        calc ‖ε n‖ * ‖interpProd w n z‖
            ≤ (1 / ((n.factorial : ℝ) * interpBound w n)) * ((1 + R) ^ n * interpBound w n) := by
              apply mul_le_mul (hε n).1 _ (norm_nonneg _) (by positivity)
              refine (norm_interpProd_le w n z).trans ?_
              apply mul_le_mul_of_nonneg_right _ hB.le
              exact pow_le_pow_left₀ (by positivity) (by linarith) n
          _ = (1 + R) ^ n / (n.factorial : ℝ) := by
              field_simp
    exact hd.differentiableAt (hU.mem_nhds hz₀)
  · intro n
    have hval : (∑' m, ε m * interpProd w m (w n)) =
        (∑ k ∈ Finset.range n, ε k * interpProd w k (w n)) + ε n * interpProd w n (w n) := by
      rw [tsum_eq_sum (s := Finset.range (n + 1)), Finset.sum_range_succ]
      intro m hm
      rw [interpProd_eq_zero w (show n < m by simp only [Finset.mem_range] at hm; omega),
        mul_zero]
    simp only
    rw [hval]
    exact ⟨(hε n).2.1, (hε n).2.2⟩

/-- The interpolation step for an arbitrary countable set `W` of points and forbidden values
`c w`. -/
theorem exists_entire_countable (W : Set ℂ) (hW : W.Countable) (c : ℂ → ℂ) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ w ∈ W, f w ∈ gaussRat ∧ f w ≠ c w := by
  classical
  set W' := W ∪ range (fun n : ℕ => (n : ℂ))
  have hW' : W'.Countable := hW.union (countable_range _)
  have hinf : W'.Infinite :=
    (Set.infinite_range_of_injective Nat.cast_injective).mono subset_union_right
  have := hW'.to_subtype
  have := hinf.to_subtype
  obtain ⟨d⟩ := nonempty_denumerable W'
  let w : ℕ → ℂ := fun n => ((Denumerable.eqv W').symm n : ℂ)
  have hw : Function.Injective w :=
    Subtype.val_injective.comp (Denumerable.eqv W').symm.injective
  obtain ⟨f, hf, hfw⟩ := exists_entire_seq w hw (fun n => c (w n))
  refine ⟨f, hf, fun x hx => ?_⟩
  have := hfw (Denumerable.eqv W' ⟨x, Or.inl hx⟩)
  simpa [w] using this

end Interpolation

end Chapter19


/-! ======================================================================
## Part: Erdos
====================================================================== -/

/-!
# Theorem 5 (Erdős): analytic functions and the continuum hypothesis

Wetzel's question: let `{f_α}` be a family of pairwise distinct analytic functions on `ℂ` such
that for each `z ∈ ℂ` the set of values `{f_α(z)}` is at most countable (property `(P₀)`).
Is the family itself at most countable?

Erdős showed that the answer depends on the continuum hypothesis:
* if `𝔠 > ℵ₁`, every family with `(P₀)` is countable;
* if `𝔠 = ℵ₁`, there is a family with `(P₀)` of size `𝔠`.

Analytic functions on `ℂ` (entire functions) are the functions `f : ℂ → ℂ` with
`Differentiable ℂ f`; a family of pairwise distinct functions is a set `F : Set (ℂ → ℂ)`.
-/



namespace Chapter19

section Erdos

open Cardinal Set

/-- Property `(P₀)` of a family `F` of functions: for each `z ∈ ℂ` the set of values
`{f(z) : f ∈ F}` is at most countable. -/
def PropertyP0 (F : Set (ℂ → ℂ)) : Prop := ∀ z : ℂ, ((fun f : ℂ → ℂ => f z) '' F).Countable

/-- The key step of the first part: if `𝔠 > ℵ₁`, then for every family of at most `ℵ₁` distinct
analytic functions there is a point `z₀` at which all the values `f(z₀)` are distinct. -/
theorem exists_point_injOn (h : ℵ_ 1 < (𝔠 : Cardinal.{0})) (G : Set (ℂ → ℂ)) (hG : ∀ f ∈ G, Differentiable ℂ f)
    (hcard : #G ≤ ℵ_ 1) : ∃ z₀ : ℂ, InjOn (fun f : ℂ → ℂ => f z₀) G := by
  classical
  let ι := {p : G × G // p.1 ≠ p.2}
  let S : ι → Set ℂ := fun p => {z | (p.1.1 : ℂ → ℂ) z = (p.1.2 : ℂ → ℂ) z}
  have hS : ∀ p, (S p).Countable := fun p =>
    countable_setOf_eq (hG _ p.1.1.2) (hG _ p.1.2.2) (fun h => p.2 (Subtype.ext h))
  have h11 : ℵ_ 1 * ℵ_ 1 = (ℵ_ 1 : Cardinal.{0}) := mul_eq_self (aleph0_le_aleph 1)
  have hι : #ι ≤ ℵ_ 1 := by
    calc #ι ≤ #(G × G) := mk_subtype_le _
      _ = #G * #G := by rw [mk_prod, lift_id]
      _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' hcard hcard
      _ = ℵ_ 1 := h11
  have hU : #(⋃ p, S p) ≤ ℵ_ 1 := by
    calc #(⋃ p, S p) ≤ #ι * ⨆ p, #(S p) := mk_iUnion_le S
      _ ≤ ℵ_ 1 * ℵ_ 1 := mul_le_mul' hι (ciSup_le' fun p =>
          (le_aleph0_iff_set_countable.mpr (hS p)).trans (aleph0_le_aleph 1))
      _ = ℵ_ 1 := h11
  have hne : (⋃ p, S p) ≠ Set.univ := by
    intro he
    have : #(univ : Set ℂ) ≤ ℵ_ 1 := he ▸ hU
    rw [mk_univ, mk_complex] at this
    exact absurd h (not_lt.mpr this)
  obtain ⟨z₀, hz₀⟩ := (ne_univ_iff_exists_notMem _).mp hne
  refine ⟨z₀, fun f hf g hg hfg => ?_⟩
  by_contra hne'
  apply hz₀
  exact mem_iUnion.mpr ⟨⟨(⟨f, hf⟩, ⟨g, hg⟩), fun h => hne' (congrArg Subtype.val h)⟩, hfg⟩

/-- **Theorem 5, first part.** If `𝔠 > ℵ₁`, then every family of analytic functions satisfying
`(P₀)` is countable. -/
theorem erdos_countable (h : ℵ_ 1 < (𝔠 : Cardinal.{0})) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hP : PropertyP0 F) : F.Countable := by
  by_contra hF'
  have h1 : ℵ_ 1 ≤ #F := by
    rw [set_countable_iff_lt_aleph_one] at hF'
    exact not_lt.mp hF'
  obtain ⟨G, hGF, hGcard⟩ := le_mk_iff_exists_subset.mp h1
  obtain ⟨z₀, hinj⟩ := exists_point_injOn h G (fun f hf => hF f (hGF hf)) hGcard.le
  have hc : ((fun f : ℂ → ℂ => f z₀) '' G).Countable := (hP z₀).mono (image_mono hGF)
  rw [set_countable_iff_lt_aleph_one, mk_image_eq_of_injOn _ _ hinj, hGcard] at hc
  exact lt_irrefl _ hc

section Construction

variable {T : Type} [LinearOrder T] [WellFoundedLT T] (e : ℂ ≃ T) (hT : ∀ γ : T, (Iio γ).Countable)

/-- Erdős' family `{f_γ}`, constructed by transfinite induction along a well-ordering `T` of
`ℂ = {z_α}` all of whose initial segments are countable: `f_γ` is an entire function with
`f_γ(z_α) ∈ D` and `f_γ(z_α) ≠ f_α(z_α)` for all `α < γ`. -/
noncomputable def erdosFamily : T → ℂ → ℂ :=
  (wellFounded_lt : WellFounded (· < · : T → T → Prop)).fix fun γ IH =>
    Classical.choose (exists_entire_countable (e ⁻¹' Iio γ) ((hT γ).preimage e.injective)
      (fun w => if hw : e w < γ then IH (e w) hw w else 0))

theorem erdosFamily_spec (γ : T) : Differentiable ℂ (erdosFamily e hT γ) ∧
    ∀ w : ℂ, e w < γ →
      erdosFamily e hT γ w ∈ gaussRat ∧ erdosFamily e hT γ w ≠ erdosFamily e hT (e w) w := by
  have e1 : erdosFamily e hT γ = Classical.choose (exists_entire_countable (e ⁻¹' Iio γ)
      ((hT γ).preimage e.injective)
      (fun w => if hw : e w < γ then erdosFamily e hT (e w) w else 0)) := by
    unfold erdosFamily
    exact WellFounded.fix_eq _ _ _
  have h1 := Classical.choose_spec (exists_entire_countable (e ⁻¹' Iio γ)
      ((hT γ).preimage e.injective)
      (fun w => if hw : e w < γ then erdosFamily e hT (e w) w else 0))
  rw [← e1] at h1
  refine ⟨h1.1, fun w hw => ?_⟩
  have := h1.2 w hw
  rwa [dite_cond_eq_true (eq_true hw)] at this

theorem erdosFamily_injective : Function.Injective (erdosFamily e hT) := by
  intro γ γ' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := (erdosFamily_spec e hT γ').2 (e.symm γ) (by simpa using hlt)
    simp only [Equiv.apply_symm_apply] at this
    exact this.2 (by rw [h])
  · have := (erdosFamily_spec e hT γ).2 (e.symm γ') (by simpa using hlt)
    simp only [Equiv.apply_symm_apply] at this
    exact this.2 (by rw [h])

theorem erdosFamily_P0 : PropertyP0 (range (erdosFamily e hT)) := by
  intro z
  have hsub : (fun f : ℂ → ℂ => f z) '' range (erdosFamily e hT) ⊆
      gaussRat ∪ ((fun γ => erdosFamily e hT γ z) '' Iic (e z)) := by
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    by_cases hγ : e z < γ
    · exact Or.inl ((erdosFamily_spec e hT γ).2 z hγ).1
    · exact Or.inr ⟨γ, not_lt.mp hγ, rfl⟩
  refine (gaussRat_countable.union ?_).mono hsub
  apply Countable.image
  rw [← Iio_insert]
  exact (hT (e z)).insert _

end Construction

/-- **Theorem 5, second part.** If `𝔠 = ℵ₁`, then there exists a family of analytic functions
with property `(P₀)` which has size `𝔠`. -/
theorem erdos_family (h : (𝔠 : Cardinal.{0}) = ℵ_ 1) :
    ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧ PropertyP0 F ∧ #F = 𝔠 := by
  have hT : ∀ γ : (ℵ_ 1 : Cardinal.{0}).ord.ToType, (Iio γ).Countable :=
    fun γ => (set_countable_iff_lt_aleph_one _).mpr (mk_Iio_lt_of_toType_ord γ)
  have hcard : #ℂ = #((ℵ_ 1 : Cardinal.{0}).ord.ToType) := by
    rw [mk_complex, h, mk_ord_toType]
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  refine ⟨range (erdosFamily e hT), ?_, erdosFamily_P0 e hT, ?_⟩
  · rintro _ ⟨γ, rfl⟩
    exact (erdosFamily_spec e hT γ).1
  · rw [mk_range_eq _ (erdosFamily_injective e hT), mk_ord_toType, h]

/-- **Theorem 5.** Both parts together. -/
theorem erdos_theorem :
    (ℵ_ 1 < (𝔠 : Cardinal.{0}) → ∀ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) → PropertyP0 F → F.Countable) ∧
    ((𝔠 : Cardinal.{0}) = ℵ_ 1 → ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧ PropertyP0 F ∧ #F = 𝔠) :=
  ⟨erdos_countable, erdos_family⟩

/-- Consequently, the answer to Wetzel's question is "no" if and only if the continuum
hypothesis holds. -/
theorem continuumHypothesis_iff_wetzel :
    ContinuumHypothesis ↔
      ∃ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) ∧ PropertyP0 F ∧ ¬ F.Countable := by
  unfold ContinuumHypothesis
  constructor
  · intro hCH
    obtain ⟨F, hF, hP, hc⟩ := erdos_family hCH
    refine ⟨F, hF, hP, fun hcount => ?_⟩
    rw [set_countable_iff_lt_aleph_one, hc, hCH] at hcount
    exact lt_irrefl _ hcount
  · rintro ⟨F, hF, hP, hnc⟩
    by_contra hne
    exact hnc (erdos_countable (lt_of_le_of_ne aleph_one_le_continuum (Ne.symm hne)) F hF hP)

end Erdos

end Chapter19
