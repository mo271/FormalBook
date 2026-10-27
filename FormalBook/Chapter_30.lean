/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, OpenClaw
-/
module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Combinatorics.KatonaCircle
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Finset.Slice
public import Mathlib.Tactic

@[expose] public section

/-!
# Three famous theorems on finite sets

  - [x] Theorem 1 (Sperner) — Lubell's chain-counting proof
  - [x] Theorem 2 (Erdős–Ko–Rado) — Katona's cyclic permutation proof

  - [x] Theorem 3 (Hall's marriage theorem) — the inductive proof of Easterfield and
        Halmos–Vaughan

This file contains the proofs from the book together with the remarks of the
chapter (sharpness of Sperner's bound, intersecting families of size `2^(n-1)`, the families of
`k`-sets through a fixed point, the example for `n = 4`, `k = 2`, the necessity of Hall's
condition). The final section collects the three theorems in the form stated in the book.

## References

* Aigner, M. and Ziegler, G.M., "Proofs from THE BOOK", Chapter 30
* Katona, G.O.H., "A simple proof of the Erdős–Ko–Rado theorem", 1972
-/

/-! ============================================================ -/

section SpernerFile

/-!
# Sperner's theorem (Lubell's proof)

We work with a finite ground set `X` with `n = card X` elements (the book's `N = {1, …, n}`).

A maximal chain `∅ = C₀ ⊂ C₁ ⊂ ⋯ ⊂ Cₙ = X` is the same thing as an ordering of the elements of
`X`, i.e. a *numbering* `f : X ≃ Fin n`: the chain consists of the prefixes
`Cᵢ = {x | f x < i}`. A set `A` lies on the chain given by `f` iff `A` is a prefix of `f`
(`Numbering.IsPrefix f A`). There are `n!` numberings, and exactly `|A|! (n - |A|)!` of them have
`A` as a prefix (`Numbering.card_prefixed`). No chain passes through two different members of an
antichain.
-/

open Finset Fintype Nat

namespace chapter30

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Lubell's counting.** For an antichain `𝒜`, the chains through members of `𝒜` are
pairwise distinct, hence `∑_{A ∈ 𝒜} |A|! (n - |A|)! ≤ n!`. -/
theorem lubell_sum_factorial_le (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    ∑ A ∈ 𝒜, (#A)! * (card X - #A)! ≤ (card X)! := by
  have hdisj : (𝒜 : Set (Finset X)).PairwiseDisjoint Numbering.prefixed := by
    intro A hA B hB hAB
    exact Numbering.disjoint_prefixed_prefixed (h𝒜 hA hB hAB) (h𝒜 hB hA hAB.symm)
  calc ∑ A ∈ 𝒜, (#A)! * (card X - #A)! = ∑ A ∈ 𝒜, #(Numbering.prefixed A) := by
        simp [Numbering.card_prefixed]
    _ = #(𝒜.biUnion Numbering.prefixed) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset (Numbering X)) := card_le_univ _
    _ = (card X)! := by simp

/-- **The LYM inequality**, in the form stated in the book:
`∑_{A ∈ 𝒜} 1 / C(n, |A|) ≤ 1` for every antichain `𝒜`. -/
theorem lym_inequality (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    ∑ A ∈ 𝒜, (((card X).choose #A : ℕ) : ℚ)⁻¹ ≤ 1 := by
  have hpos : (0 : ℚ) < (card X)! := by exact_mod_cast factorial_pos _
  have key : ∀ A ∈ 𝒜, (((card X).choose #A : ℕ) : ℚ)⁻¹
      = (((#A)! * (card X - #A)! : ℕ) : ℚ) / (card X)! := by
    intro A _
    rw [Nat.cast_choose ℚ (card_le_univ A), inv_div]
    push_cast; ring
  rw [sum_congr rfl key, ← sum_div, div_le_one hpos]
  exact_mod_cast lubell_sum_factorial_le 𝒜 h𝒜

/-- **Theorem 1 (Sperner).** An antichain of subsets of an `n`-set has at most
`C(n, ⌊n/2⌋)` members. -/
theorem sperner_lubell (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    #𝒜 ≤ (card X).choose (card X / 2) := by
  have hle : ∀ A ∈ 𝒜, (card X)! ≤ (#A)! * (card X - #A)! * (card X).choose (card X / 2) := by
    intro A _
    calc (card X)! = (card X).choose #A * (#A)! * (card X - #A)! :=
          (choose_mul_factorial_mul_factorial (card_le_univ A)).symm
      _ ≤ (card X).choose (card X / 2) * (#A)! * (card X - #A)! := by
          gcongr; exact choose_le_middle _ _
      _ = _ := by ring
  have h1 : #𝒜 * (card X)! ≤ (card X).choose (card X / 2) * (card X)! := by
    calc #𝒜 * (card X)! = ∑ A ∈ 𝒜, (card X)! := by simp
      _ ≤ ∑ A ∈ 𝒜, (#A)! * (card X - #A)! * (card X).choose (card X / 2) := sum_le_sum hle
      _ = (∑ A ∈ 𝒜, (#A)! * (card X - #A)!) * (card X).choose (card X / 2) := by
          rw [sum_mul]
      _ ≤ (card X)! * (card X).choose (card X / 2) := by
          gcongr; exact lubell_sum_factorial_le 𝒜 h𝒜
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h1 (factorial_pos _)

omit [DecidableEq X] in
/-- The family of all `k`-subsets is an antichain. -/
theorem powersetCard_isAntichain (k : ℕ) :
    IsAntichain (· ⊆ ·)
      ((powersetCard k (univ : Finset X) : Finset (Finset X)) : Set (Finset X)) := by
  intro A hA B hB hAB hsub
  simp only [mem_coe, mem_powersetCard] at hA hB
  exact hAB (eq_of_subset_of_card_le hsub (by rw [hA.2, hB.2]))

omit [DecidableEq X] in
/-- The family of all `k`-subsets has `C(n, k)` members. -/
theorem card_powersetCard_univ (k : ℕ) :
    #(powersetCard k (univ : Finset X)) = (card X).choose k := by
  simp

omit [DecidableEq X] in
/-- **Sharpness of Sperner's theorem.** The `⌊n/2⌋`-subsets form an antichain of size
`C(n, ⌊n/2⌋)`. -/
theorem sperner_sharp :
    IsAntichain (· ⊆ ·)
        ((powersetCard (Fintype.card X / 2) (univ : Finset X) : Finset (Finset X))
          : Set (Finset X)) ∧
      #(powersetCard (Fintype.card X / 2) (univ : Finset X)) =
        (Fintype.card X).choose (Fintype.card X / 2) :=
  ⟨powersetCard_isAntichain _, card_powersetCard_univ _⟩

/-- **Theorem 1 (Sperner), as stated in the book.** The size of a largest antichain of an
`n`-set is `C(n, ⌊n/2⌋)`. -/
theorem sperner_isGreatest :
    IsGreatest {m | ∃ 𝒜 : Finset (Finset X),
        IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)) ∧ #𝒜 = m}
      ((Fintype.card X).choose (Fintype.card X / 2)) := by
  refine ⟨⟨_, sperner_sharp.1, sperner_sharp.2⟩, ?_⟩
  rintro m ⟨𝒜, h𝒜, rfl⟩
  exact sperner_lubell 𝒜 h𝒜

end chapter30

end SpernerFile

/-! ============================================================ -/

section ErdosKoRadoFile

/-!
# The Erdős–Ko–Rado theorem (Katona's proof)

## The circle

A circle `C` divided by `n` points into `n` edges is modelled by `Fin n` (the edges), with
addition modulo `n`. An *arc of length `k`* starting at edge `i` consists of the `k` consecutive
edges `i, i+1, …, i+k-1` (mod `n`); this is `arc k i = {p | (p - i) mod n < k}`.

## Placing `X` on the circle

A cyclic arrangement of the ground set `X` (with `n = card X`) is given by a numbering
`f : X ≃ Fin n`, writing `x` next to edge `f x`. The set of numbers written next to the arc
`arc k i` is `arcSet k f i`. Instead of the `(n-1)!` cyclic permutations we count over all `n!`
numberings together with all `n` starting points `i`; every cyclic permutation is counted `n`
times, which does not affect the argument.
-/

open Finset Fintype Nat

namespace chapter30

section Circle

variable {N : ℕ}

lemma fin_sub_val (a b : Fin N) :
    ((a - b : Fin N) : ℕ) = if (b : ℕ) ≤ a then (a : ℕ) - b else N + a - b := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr h
  · exact Fin.coe_sub_iff_lt.mpr (not_le.mp h)

/-- The arc of length `k` on the circle with `N` edges starting at edge `i`: the edges
`i, i+1, …, i+k-1` (mod `N`). -/
def arc (k : ℕ) (i : Fin N) : Finset (Fin N) := {p | ((p - i : Fin N) : ℕ) < k}

lemma mem_arc {k : ℕ} {i p : Fin N} :
    p ∈ arc k i ↔ ((i : ℕ) ≤ p ∧ (p : ℕ) < i + k) ∨ ((p : ℕ) < i ∧ (p : ℕ) + N < i + k) := by
  simp only [arc, mem_filter, mem_univ, true_and, fin_sub_val]
  have := p.isLt; have := i.isLt
  split_ifs <;> omega

/-- **Katona's Lemma.** Let `n ≥ 2k`, and let `S` be a set of arcs of length `k` (given by their
starting edges) such that any two of them have an edge in common. Then `|S| ≤ k`.

Following the book, fix one arc `A₁` (starting at `i₀`). Every other arc of `S` has an endpoint
which is an inner point of `A₁`, and distinct arcs have distinct endpoints. Concretely, we map
each arc starting at `j` to the position of the relevant endpoint inside `A₁`, which gives an
injection of `S` into `{0, …, k-1}`. -/
theorem katona_arc_lemma {k : ℕ} (hk : 2 * k ≤ N) (S : Finset (Fin N))
    (hS : ∀ i ∈ S, ∀ j ∈ S, (arc k i ∩ arc k j).Nonempty) : #S ≤ k := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  let pos : Fin N → ℕ := fun j =>
    if ((j - i₀ : Fin N) : ℕ) < k then ((j - i₀ : Fin N) : ℕ) else ((j - i₀ : Fin N) : ℕ) + k - N
  have hmaps : ∀ j ∈ S, pos j ∈ range k := by
    intro j hj
    obtain ⟨p, hp⟩ := hS i₀ hi₀ j hj
    rw [mem_inter, mem_arc, mem_arc] at hp
    have := p.isLt; have := i₀.isLt; have := j.isLt
    simp only [pos, mem_range, fin_sub_val]
    split_ifs <;> omega
  have hinj : Set.InjOn pos S := by
    intro j hj j' hj' hjj
    obtain ⟨p, hp⟩ := hS j hj j' hj'
    obtain ⟨q, hq⟩ := hS i₀ hi₀ j hj
    obtain ⟨r, hr⟩ := hS i₀ hi₀ j' hj'
    rw [mem_inter, mem_arc, mem_arc] at hp hq hr
    have := p.isLt; have := i₀.isLt; have := j.isLt; have := j'.isLt
    have := q.isLt; have := r.isLt
    apply Fin.ext
    simp only [pos, fin_sub_val] at hjj
    split_ifs at hjj <;> omega
  simpa using card_le_card_of_injOn (t := range k) pos (fun j hj => hmaps j hj) hinj

end Circle

section Katona

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The set of elements of `X` written next to the arc of length `k` starting at edge `i`,
when `X` is placed around the circle according to the numbering `f`. -/
def arcSet (k : ℕ) (f : Numbering X) (i : Fin (card X)) : Finset X :=
  {x | f x ∈ arc k i}

omit [DecidableEq X] in
/-- A `k`-set `A` appears on the arc starting at `i` in the arrangement `f` iff `A` is a prefix
of the rotated numbering `x ↦ f x - i`. -/
lemma arcSet_eq_iff_isPrefix [NeZero (card X)] {k : ℕ} (f : Numbering X) (i : Fin (card X))
    {A : Finset X} (hA : #A = k) :
    arcSet k f i = A ↔ Numbering.IsPrefix (f.trans (Equiv.subRight i)) A := by
  subst hA
  simp only [Numbering.IsPrefix, arcSet, arc, Equiv.trans_apply, Equiv.subRight_apply,
    Finset.ext_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

/-- A fixed `k`-set appears on a fixed arc in exactly `k! (n-k)!` arrangements. -/
lemma card_arcSet_eq [NeZero (card X)] {k : ℕ} (i : Fin (card X)) {A : Finset X}
    (hA : #A = k) :
    #({f | arcSet k f i = A} : Finset (Numbering X)) = k ! * (card X - k)! := by
  subst hA
  rw [← Numbering.card_prefixed A]
  let e : Numbering X ≃ Numbering X :=
    { toFun := fun f => f.trans (Equiv.subRight i)
      invFun := fun g => g.trans (Equiv.subRight i).symm
      left_inv := fun f => by ext; simp
      right_inv := fun g => by ext; simp }
  apply Finset.card_equiv e
  intro f
  simp only [mem_filter, mem_univ, true_and, Numbering.mem_prefixed]
  exact arcSet_eq_iff_isPrefix f i rfl

/-- **Katona's double counting.** For an intersecting family `𝒜` of `k`-sets with `n ≥ 2k`,
`|𝒜| · n · k! (n-k)! ≤ k · n!`. -/
theorem katona_double_counting [NeZero (card X)] {k : ℕ} (hk : 2 * k ≤ card X)
    (𝒜 : Finset (Finset X)) (h𝒜 : (𝒜 : Set (Finset X)).Intersecting)
    (hs : (𝒜 : Set (Finset X)).Sized k) :
    #𝒜 * (card X * (k ! * (card X - k)!)) ≤ k * (card X)! := by
  -- each arrangement shows at most `k` members of `𝒜` on arcs, by Katona's lemma
  have upper : ∑ f : Numbering X, #({i | arcSet k f i ∈ 𝒜} : Finset (Fin (card X)))
      ≤ k * (card X)! := by
    calc _ ≤ ∑ _f : Numbering X, k := by
          refine sum_le_sum fun f _ => katona_arc_lemma hk _ ?_
          intro i hi j hj
          simp only [mem_filter, mem_univ, true_and] at hi hj
          obtain ⟨x, hx⟩ := not_disjoint_iff_nonempty_inter.mp (h𝒜 hi hj)
          simp only [arcSet, mem_inter, mem_filter, mem_univ, true_and] at hx
          exact ⟨f x, mem_inter.mpr hx⟩
      _ = k * (card X)! := by simp [mul_comm]
  -- each member of `𝒜` is counted exactly `n · k! (n-k)!` times
  have lower : ∑ f : Numbering X, #({i | arcSet k f i ∈ 𝒜} : Finset (Fin (card X)))
      = #𝒜 * (card X * (k ! * (card X - k)!)) := by
    calc ∑ f : Numbering X, #({i | arcSet k f i ∈ 𝒜} : Finset (Fin (card X)))
        = ∑ f : Numbering X, ∑ i : Fin (card X), if arcSet k f i ∈ 𝒜 then 1 else 0 := by
          simp only [Finset.card_filter]
      _ = ∑ i : Fin (card X), ∑ f : Numbering X, if arcSet k f i ∈ 𝒜 then 1 else 0 :=
          sum_comm
      _ = ∑ i : Fin (card X), #({f | arcSet k f i ∈ 𝒜} : Finset (Numbering X)) := by
          simp only [Finset.card_filter]
      _ = ∑ i : Fin (card X), ∑ A ∈ 𝒜, #({f | arcSet k f i = A} : Finset (Numbering X)) := by
          refine sum_congr rfl fun i _ => ?_
          rw [card_eq_sum_card_fiberwise (f := fun f => arcSet k f i) (t := 𝒜)
            (s := ({f | arcSet k f i ∈ 𝒜} : Finset (Numbering X)))
            (by intro f hf; simpa using hf)]
          refine sum_congr rfl fun A hA => ?_
          congr 1
          ext f
          simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
          rintro rfl; exact hA
      _ = ∑ _i : Fin (card X), ∑ _A ∈ 𝒜, k ! * (card X - k)! := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun A hA => ?_
          exact card_arcSet_eq i (hs hA)
      _ = #𝒜 * (card X * (k ! * (card X - k)!)) := by
          simp only [sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  omega

/-- The identity `C(n-1, k-1) · n · k! (n-k)! = k · n!` for `1 ≤ k ≤ n`. -/
lemma choose_pred_mul_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n - 1).choose (k - 1) * (n * (k ! * (n - k)!)) = k * n ! := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjm : j ≤ m := by omega
  simp only [Nat.add_sub_cancel, Nat.add_sub_add_right, factorial_succ]
  rw [← choose_mul_factorial_mul_factorial hjm]
  ring

/-- **Theorem 2 (Erdős–Ko–Rado)**, for an arbitrary `n`-element ground set: if `n ≥ 2k`, an
intersecting family of `k`-sets has at most `C(n-1, k-1)` members. -/
theorem erdos_ko_rado_katona {k : ℕ} (hk : 2 * k ≤ card X)
    (𝒜 : Finset (Finset X)) (h𝒜 : (𝒜 : Set (Finset X)).Intersecting)
    (hs : (𝒜 : Set (Finset X)).Sized k) :
    #𝒜 ≤ (card X - 1).choose (k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | h1k
  · -- the only `0`-set is `∅`, which does not intersect itself
    have : 𝒜 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro A hA
      exact h𝒜 hA hA (by rw [disjoint_self_iff_empty, ← Finset.card_eq_zero]; exact hs hA)
    simp [this]
  haveI : NeZero (card X) := ⟨by omega⟩
  have hdc := katona_double_counting hk 𝒜 h𝒜 hs
  rw [← choose_pred_mul_eq h1k (by omega)] at hdc
  have hpos : 0 < card X * (k ! * (card X - k)!) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (factorial_pos _) (factorial_pos _))
  exact Nat.le_of_mul_le_mul_right hdc hpos

end Katona

section Remarks

/-! ## The remarks of the chapter around Theorem 2 -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- An intersecting family of subsets of an `n`-set has at most `2^(n-1)` members, since it
cannot contain both a set and its complement. -/
theorem intersecting_card_le (𝒜 : Finset (Finset X))
    (h𝒜 : (𝒜 : Set (Finset X)).Intersecting) :
    #𝒜 ≤ 2 ^ (card X - 1) := by
  have hdisj : Disjoint 𝒜 (𝒜.image compl) := by
    rw [disjoint_left]
    intro A hA hA'
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA'
    exact h𝒜 hB hA disjoint_compl_right
  have h2 : 2 * #𝒜 ≤ 2 ^ card X := by
    have := card_le_univ (𝒜 ∪ 𝒜.image compl)
    rw [card_union_of_disjoint hdisj, Finset.card_image_of_injective _ compl_injective] at this
    simpa [two_mul, Fintype.card_finset] using this
  rcases Nat.eq_zero_or_pos (card X) with h | h
  · rw [h] at h2 ⊢; simp at h2 ⊢; omega
  · obtain ⟨m, hm⟩ : ∃ m, card X = m + 1 := ⟨card X - 1, by omega⟩
    rw [hm, pow_succ] at h2
    rw [hm, Nat.add_sub_cancel]
    omega

/-- The family of all sets containing a fixed element `a` is intersecting. -/
theorem star_intersecting (a : X) :
    (({A | a ∈ A} : Finset (Finset X)) : Set (Finset X)).Intersecting := by
  intro A hA B hB hAB
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hA hB
  exact disjoint_left.mp hAB hA hB

/-- The family of all sets containing a fixed element has `2^(n-1)` members. -/
theorem card_star (a : X) : #({A | a ∈ A} : Finset (Finset X)) = 2 ^ (card X - 1) := by
  rw [show 2 ^ (card X - 1) = #((univ.erase a).powerset) by
    simp [card_erase_of_mem (mem_univ a)]]
  refine card_nbij' (fun A => A.erase a) (insert a) ?_ ?_ ?_ ?_
  · intro A _; simp
  · intro B _; simp
  · intro A hA
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hA
    exact insert_erase hA
  · intro B hB
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hB
    exact erase_insert (fun h => by simpa using hB h)

/-- The size of a largest intersecting family of subsets of an `n`-set (`n ≥ 1`) is
`2^(n-1)`. -/
theorem intersecting_isGreatest [Nonempty X] :
    IsGreatest {m | ∃ 𝒜 : Finset (Finset X), (𝒜 : Set (Finset X)).Intersecting ∧ #𝒜 = m}
      (2 ^ (card X - 1)) := by
  obtain ⟨a⟩ := ‹Nonempty X›
  refine ⟨⟨_, star_intersecting a, card_star a⟩, ?_⟩
  rintro m ⟨𝒜, h𝒜, rfl⟩
  exact intersecting_card_le 𝒜 h𝒜

/-- If `n < 2k`, any two `k`-subsets of an `n`-set intersect, so the problem is trivial. -/
theorem not_disjoint_of_card_lt {k : ℕ} (hk : card X < 2 * k) {A B : Finset X}
    (hA : #A = k) (hB : #B = k) : ¬ Disjoint A B := by
  intro h
  have h1 := card_union_of_disjoint h
  have h2 := card_le_univ (A ∪ B)
  omega

/-- The `k`-sets containing a fixed element `a`. -/
def kStar (k : ℕ) (a : X) : Finset (Finset X) := {A ∈ powersetCard k univ | a ∈ A}

theorem kStar_intersecting (k : ℕ) (a : X) :
    ((kStar k a : Finset (Finset X)) : Set (Finset X)).Intersecting := by
  intro A hA B hB hAB
  simp only [kStar, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hA hB
  exact disjoint_left.mp hAB hA.2 hB.2

theorem kStar_sized (k : ℕ) (a : X) :
    ((kStar k a : Finset (Finset X)) : Set (Finset X)).Sized k := by
  intro A hA
  simp only [kStar, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hA
  exact hA.1.2

/-- The `k`-sets containing a fixed element are obtained by adding it to the `(k-1)`-subsets of
the remaining `n - 1` elements; hence there are `C(n-1, k-1)` of them. -/
theorem card_kStar {k : ℕ} (hk : 1 ≤ k) (a : X) :
    #(kStar k a) = (card X - 1).choose (k - 1) := by
  rw [show (card X - 1).choose (k - 1) = #(powersetCard (k - 1) (univ.erase a)) by
    simp [card_erase_of_mem (mem_univ a)]]
  refine card_nbij' (fun A => A.erase a) (insert a) ?_ ?_ ?_ ?_
  · intro A hA
    simp only [kStar, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hA
    simp only [mem_coe, mem_powersetCard]
    exact ⟨erase_subset_erase _ hA.1.1, by rw [card_erase_of_mem hA.2, hA.1.2]⟩
  · intro B hB
    simp only [mem_coe, mem_powersetCard] at hB
    have ha : a ∉ B := fun h => by simpa using hB.1 h
    simp only [kStar, coe_filter, mem_powersetCard, Set.mem_setOf_eq, subset_univ, true_and,
      mem_insert_self, and_true]
    rw [card_insert_of_notMem ha, hB.2]; omega
  · intro A hA
    simp only [kStar, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hA
    exact insert_erase hA.2
  · intro B hB
    simp only [mem_coe, mem_powersetCard] at hB
    exact erase_insert (fun h => by simpa using hB.1 h)

/-- **Theorem 2 (Erdős–Ko–Rado), as stated in the book.** For `1 ≤ k` and `n ≥ 2k`, the largest
size of an intersecting `k`-family in an `n`-set is `C(n-1, k-1)`. -/
theorem erdos_ko_rado_isGreatest {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k ≤ card X) :
    IsGreatest {m | ∃ 𝒜 : Finset (Finset X), (𝒜 : Set (Finset X)).Intersecting ∧
        (𝒜 : Set (Finset X)).Sized k ∧ #𝒜 = m}
      ((card X - 1).choose (k - 1)) := by
  obtain ⟨a⟩ : Nonempty X := card_pos_iff.mp (by omega)
  refine ⟨⟨_, kStar_intersecting k a, kStar_sized k a, card_kStar hk1 a⟩, ?_⟩
  rintro m ⟨𝒜, h𝒜, hs, rfl⟩
  exact erdos_ko_rado_katona hk 𝒜 h𝒜 hs

/-- For `n = 4`, `k = 2` the family `{{1,2}, {1,3}, {2,3}}` (written here with elements
`0, 1, 2` of `Fin 4`) is an intersecting `2`-family of maximal size `C(3,1) = 3` which does not
consist of sets containing a fixed element. -/
theorem ekr_example_n4_k2 :
    let 𝒜 : Finset (Finset (Fin 4)) := {{0, 1}, {0, 2}, {1, 2}}
    (𝒜 : Set (Finset (Fin 4))).Intersecting ∧ (𝒜 : Set (Finset (Fin 4))).Sized 2 ∧
      #𝒜 = (4 - 1).choose (2 - 1) ∧ ¬ ∃ a, ∀ A ∈ 𝒜, a ∈ A := by
  intro 𝒜
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro A hA B hB
    simp only [𝒜, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;> decide
  · intro A hA
    simp only [𝒜, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl <;> decide

/-- For `n = 2k`, choosing exactly one set out of every pair `{A, N \ A}` of complementary
`k`-sets gives an intersecting `k`-family of the maximal size `½ C(n, k) = C(n-1, k-1)`. -/
theorem ekr_half_family {k : ℕ} (hk1 : 1 ≤ k) (hn : card X = 2 * k) (𝒜 : Finset (Finset X))
    (hsub : 𝒜 ⊆ powersetCard k univ)
    (hpick : ∀ A ∈ powersetCard k (univ : Finset X), A ∈ 𝒜 ↔ Aᶜ ∉ 𝒜) :
    (𝒜 : Set (Finset X)).Intersecting ∧ (𝒜 : Set (Finset X)).Sized k ∧
      #𝒜 = (card X - 1).choose (k - 1) := by
  have hsized : (𝒜 : Set (Finset X)).Sized k := fun A hA => (mem_powersetCard.mp (hsub hA)).2
  have hcompl_card : ∀ A : Finset X, #A = k → #Aᶜ = k := fun A hA => by
    rw [card_compl, hA]; omega
  refine ⟨?_, hsized, ?_⟩
  · intro A hA B hB hAB
    have hA' := hsized hA
    have hB' := hsized hB
    have hBA : B = Aᶜ := by
      apply eq_of_subset_of_card_le
      · intro x hx
        rw [mem_compl]
        intro hxA
        exact disjoint_left.mp hAB hxA hx
      · rw [hcompl_card A hA', hB']
    subst hBA
    exact (hpick A (hsub hA)).mp hA hB
  · have hdisj : Disjoint 𝒜 (𝒜.image compl) := by
      rw [disjoint_left]
      intro A hA hA'
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hA'
      exact (hpick B (hsub hB)).mp hB hA
    have hunion : 𝒜 ∪ 𝒜.image compl = powersetCard k univ := by
      ext A
      simp only [mem_union, mem_image]
      constructor
      · rintro (h | ⟨B, hB, rfl⟩)
        · exact hsub h
        · exact mem_powersetCard.mpr ⟨subset_univ _, hcompl_card B (hsized hB)⟩
      · intro hA
        by_cases h : A ∈ 𝒜
        · exact Or.inl h
        · have hAc : Aᶜ ∈ 𝒜 := by
            by_contra hc
            exact h ((hpick A hA).mpr hc)
          exact Or.inr ⟨Aᶜ, hAc, compl_compl A⟩
    have h2 : 2 * #𝒜 = (2 * k).choose k := by
      have := congrArg Finset.card hunion
      rw [card_union_of_disjoint hdisj, Finset.card_image_of_injective _ compl_injective,
        card_powersetCard, Finset.card_univ, hn] at this
      omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hpascal : (2 * (j + 1)).choose (j + 1) = 2 * (2 * j + 1).choose j := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.choose_succ_succ,
        Nat.choose_symm_half]
      ring
    rw [hn, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel]
    omega

end Remarks

end chapter30

end ErdosKoRadoFile

/-! ============================================================ -/

section HallFile

/-!
# Hall's marriage theorem

The sets `A₁, …, Aₙ` are given by a function `t : ι → Finset α` on a finite index type `ι`.
A *system of distinct representatives* (SDR) is an injective function `f : ι → α` with
`f i ∈ t i` for all `i`. Hall's condition (H) says that the union of any `m` of the sets
contains at least `m` elements: `|s| ≤ |⋃_{i ∈ s} t i|` for every `s ⊆ ι`.

The proof is by induction on the number of sets, distinguishing whether there is a
*critical family*, i.e. a nonempty proper subfamily `s` with `|⋃_{i ∈ s} t i| = |s|`.
To run the induction we work with a finite set `s ⊆ ι` of indices and representatives that are
injective on `s`.
-/

open Finset

namespace chapter30

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- Hall's condition for the subfamily indexed by `s`. -/
def HallCondition (t : ι → Finset α) (s : Finset ι) : Prop :=
  ∀ u ⊆ s, #u ≤ #(u.biUnion t)

/-- The inductive core of the proof of Hall's theorem: if the subfamily indexed by `s` satisfies
(H), it has a system of distinct representatives. -/
theorem hall_inductive [Nonempty α] (n : ℕ) :
    ∀ (s : Finset ι) (t : ι → Finset α), #s = n → HallCondition t s →
      ∃ f : ι → α, Set.InjOn f s ∧ ∀ i ∈ s, f i ∈ t i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t hsn hH
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨fun _ => Classical.arbitrary α, by simp, by simp⟩
  by_cases hcrit : ∃ u ⊆ s, u.Nonempty ∧ #u < #s ∧ #(u.biUnion t) = #u
  · -- Case 2: there is a critical family `u`, with union `Y` of size `|u|`.
    obtain ⟨u, hus, hune, hlt, hcard⟩ := hcrit
    -- an SDR for the critical family, by induction
    obtain ⟨f₁, hf₁inj, hf₁mem⟩ :=
      ih #u (hsn ▸ hlt) u t rfl (fun v hv => hH v (hv.trans hus))
    set Y := u.biUnion t with hY
    -- the remaining sets with `Y` removed still satisfy (H)
    have hH' : HallCondition (fun i => t i \ Y) (s \ u) := by
      intro v hv
      have hvu : Disjoint v u := by
        rw [disjoint_left]; intro i hiv hiu; exact (mem_sdiff.mp (hv hiv)).2 hiu
      have heq : v.biUnion (fun i => t i \ Y) = (v ∪ u).biUnion t \ Y := by
        ext x
        simp only [mem_biUnion, mem_sdiff, mem_union, hY]
        constructor
        · rintro ⟨i, hi, hxi, hxY⟩; exact ⟨⟨i, Or.inl hi, hxi⟩, hxY⟩
        · rintro ⟨⟨i, hi | hi, hxi⟩, hxY⟩
          · exact ⟨i, hi, hxi, hxY⟩
          · exact absurd ⟨i, hi, hxi⟩ hxY
      have hsub : Y ⊆ (v ∪ u).biUnion t :=
        biUnion_subset_biUnion_of_subset_left _ subset_union_right
      have h1 := hH (v ∪ u) (union_subset (hv.trans sdiff_subset) hus)
      rw [card_union_of_disjoint hvu] at h1
      rw [heq, card_sdiff_of_subset hsub, hcard]
      omega
    -- an SDR for the remaining sets avoiding `Y`, by induction
    obtain ⟨f₂, hf₂inj, hf₂mem⟩ :=
      ih #(s \ u) (by rw [card_sdiff_of_subset hus]; have := hune.card_pos; omega)
        (s \ u) (fun i => t i \ Y) rfl hH'
    refine ⟨fun i => if i ∈ u then f₁ i else f₂ i, ?_, ?_⟩
    · intro i hi j hj hij
      simp only at hij
      split_ifs at hij with hiu hju hju
      · exact hf₁inj hiu hju hij
      · exfalso
        have h1 : f₁ i ∈ Y := mem_biUnion.mpr ⟨i, hiu, hf₁mem i hiu⟩
        have h2 := hf₂mem j (mem_sdiff.mpr ⟨hj, hju⟩)
        rw [← hij] at h2
        exact (mem_sdiff.mp h2).2 h1
      · exfalso
        have h1 : f₁ j ∈ Y := mem_biUnion.mpr ⟨j, hju, hf₁mem j hju⟩
        have h2 := hf₂mem i (mem_sdiff.mpr ⟨hi, hiu⟩)
        rw [hij] at h2
        exact (mem_sdiff.mp h2).2 h1
      · exact hf₂inj (mem_sdiff.mpr ⟨hi, hiu⟩) (mem_sdiff.mpr ⟨hj, hju⟩) hij
    · intro i hi
      simp only
      split_ifs with hiu
      · exact hf₁mem i hiu
      · exact (mem_sdiff.mp (hf₂mem i (mem_sdiff.mpr ⟨hi, hiu⟩))).1
  · -- Case 1: there is no critical family. Pick any `x ∈ t a` and delete it.
    push_neg at hcrit
    have hta : (t a).Nonempty := by
      have := hH {a} (singleton_subset_iff.mpr ha)
      rw [singleton_biUnion, card_singleton] at this
      exact card_pos.mp this
    obtain ⟨x, hx⟩ := hta
    have hH' : HallCondition (fun i => (t i).erase x) (s.erase a) := by
      intro v hv
      rcases v.eq_empty_or_nonempty with rfl | hvne
      · simp
      have hvs : v ⊆ s := hv.trans (erase_subset _ _)
      have hvlt : #v < #s := (card_le_card hv).trans_lt (card_erase_lt_of_mem ha)
      have h1 := hH v hvs
      have h2 := hcrit v hvs hvne hvlt
      have heq : v.biUnion (fun i => (t i).erase x) = (v.biUnion t).erase x := by
        ext y; simp only [mem_biUnion, mem_erase]; aesop
      rw [heq]
      have := pred_card_le_card_erase (s := v.biUnion t) (a := x)
      omega
    obtain ⟨f', hf'inj, hf'mem⟩ :=
      ih #(s.erase a) (hsn ▸ card_erase_lt_of_mem ha) (s.erase a) (fun i => (t i).erase x) rfl hH'
    refine ⟨Function.update f' a x, ?_, ?_⟩
    · intro i hi j hj hij
      by_cases hia : i = a <;> by_cases hja : j = a
      · rw [hia, hja]
      · exfalso
        subst hia
        have h := hf'mem j (mem_erase.mpr ⟨hja, hj⟩)
        rw [Function.update_self, Function.update_of_ne hja] at hij
        rw [← hij] at h
        exact (mem_erase.mp h).1 rfl
      · exfalso
        subst hja
        have h := hf'mem i (mem_erase.mpr ⟨hia, hi⟩)
        rw [Function.update_self, Function.update_of_ne hia] at hij
        rw [hij] at h
        exact (mem_erase.mp h).1 rfl
      · rw [Function.update_of_ne hia, Function.update_of_ne hja] at hij
        exact hf'inj (mem_erase.mpr ⟨hia, hi⟩) (mem_erase.mpr ⟨hja, hj⟩) hij
    · intro i hi
      by_cases hia : i = a
      · subst hia; rw [Function.update_self]; exact hx
      · rw [Function.update_of_ne hia]
        exact (mem_erase.mp (hf'mem i (mem_erase.mpr ⟨hia, hi⟩))).2

/-- **Theorem 3 (Hall's marriage theorem).** Let `A₁, …, Aₙ` be finite sets (given by
`t : ι → Finset α` with `ι` finite). Then there exists a system of distinct representatives if
and only if the union of any `m` of the sets `Aᵢ` contains at least `m` elements. -/
theorem hall_marriage_theorem [Fintype ι] (t : ι → Finset α) :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i) ↔
      ∀ s : Finset ι, #s ≤ #(s.biUnion t) := by
  constructor
  · -- the condition is clearly necessary
    rintro ⟨f, hf, hft⟩ s
    calc #s = #(s.image f) := (card_image_of_injective s hf).symm
      _ ≤ #(s.biUnion t) := card_le_card fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
          exact mem_biUnion.mpr ⟨i, hi, hft i⟩
  · -- and sufficient
    intro hH
    cases isEmpty_or_nonempty ι with
    | inl _ => exact ⟨isEmptyElim, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
    | inr hι =>
      obtain ⟨i₀⟩ := hι
      have : Nonempty α := by
        have := hH {i₀}
        rw [singleton_biUnion, card_singleton] at this
        obtain ⟨x, _⟩ := card_pos.mp this
        exact ⟨x⟩
      obtain ⟨f, hinj, hmem⟩ := hall_inductive #(univ : Finset ι) univ t rfl
        (fun u _ => hH u)
      exact ⟨f, fun i j h => hinj (mem_univ i) (mem_univ j) h, fun i => hmem i (mem_univ i)⟩

end chapter30

end HallFile

/-! ============================================================ -/

section MainTheorems

namespace chapter30

/-! ## Theorem 1: Sperner's theorem -/

/-- **Sperner's theorem**, proved via Lubell's chain counting (`sperner_lubell`). -/
theorem sperner {α : Type*} [Fintype α]
    (𝒜 : Finset (Finset α)) (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
  exact sperner_lubell 𝒜 h𝒜

/-! ## Theorem 2: Erdős–Ko–Rado (Katona's cyclic permutation proof) -/

section ErdosKoRado

/-- **Erdős–Ko–Rado theorem** (Katona's cyclic permutation proof).
If `n ≥ 2k`, then the maximum size of an intersecting k-uniform family
of subsets of `Fin n` is `C(n-1, k-1)`.

The double counting gives `|𝒜| · n · k! · (n-k)! ≤ k · n!` (`katona_double_counting`).
Since `C(n-1, k-1) · n · k! · (n-k)! = k · n!`, we get `|𝒜| ≤ C(n-1, k-1)`. -/
theorem erdos_ko_rado {n : ℕ} {𝒜 : Finset (Finset (Fin n))} {k : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hSized : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hk : k ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  have h2k : 2 * k ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  simpa using erdos_ko_rado_katona h2k 𝒜 h𝒜 hSized

end ErdosKoRado

/-! ## Theorem 3: Hall's marriage theorem

The book's statement concerns finitely many sets `A₁, …, Aₙ`; it is `hall_marriage_theorem`
(above), proved by the book's induction on `n`, with two cases:

**Case 1:** If there is no critical family, pick any representative `x` of one of the sets,
remove `x` from the remaining sets, and apply the induction hypothesis.

**Case 2:** If some nonempty proper subfamily `S` is critical (`|⋃_{i∈S} A_i| = |S|`),
solve `S` and its complement independently (removing the union of `S` from the sets
indexed by the complement), then combine.

The version below, for an arbitrary (possibly infinite) index type with finite sets, goes
beyond the book; it follows from the finite case by a compactness argument and is taken from
Mathlib (`Finset.all_card_le_biUnion_card_iff_exists_injective`).
-/

/-- **Hall's marriage theorem**, finite case as in the book (proved above). -/
theorem hall_marriage_finite {ι : Type*} {α : Type*} [Fintype ι] [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  classical
  exact (hall_marriage_theorem t).symm

/-- **Hall's marriage theorem** for an arbitrary index type. -/
theorem hall_marriage {ι : Type*} {α : Type*} [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t

end chapter30

end MainTheorems
