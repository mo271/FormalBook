/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Tauto

/-!
# Chapter 15, Theorem 2: Fox labelings

Link diagrams are treated combinatorially (Appendix): a diagram is given by its finite set of
*arcs* (maximal pieces of the drawing running from one under-crossing to the next; arcs are named
by natural numbers) together with its list of *crossings*.  A crossing is recorded as a triple
`(o, u, v)`: `o` is the arc of the overpass, `u` and `v` are the two arcs that end at the crossing.

Two combinatorial diagrams are *equivalent* if they are connected by a finite sequence of the
Reidemeister moves defined below, in either direction, together with arc renaming and crossing
reordering. The formalization proves invariance under these algebraic moves. It does not
formalize planar embeddings or the connection to ambient isotopy given by Reidemeister's theorem.

## References

M. Aigner and G. M. Ziegler, *Proofs from THE BOOK*, sixth edition, Chapter 15, Theorem 2
and the appendix on knots and links.

## TODO

- Theorem 1: links made from pairwise unlinked perfect circles are trivial.
- Connect the combinatorial diagrams and moves to geometric links.
-/

@[expose] public section

namespace Chapter15

/-- A combinatorial link diagram. -/
structure LinkDiagram where
  /-- the (names of the) arcs of the diagram -/
  arcs : Finset ℕ
  /-- the crossings `(over, under₁, under₂)` -/
  crossings : List (ℕ × ℕ × ℕ)
  /-- every crossing only involves arcs of the diagram -/
  wf : ∀ x ∈ crossings, x.1 ∈ arcs ∧ x.2.1 ∈ arcs ∧ x.2.2 ∈ arcs

/-- The Fox `n`-labelings of a diagram: labelings of the arcs by integers modulo `n` (extended by
`0` outside of the arcs) satisfying the crossing relation `a + c ≡ 2b (mod n)` at each crossing,
where `b` is the label of the overpass. -/
def foxLabelings (n : ℕ) (D : LinkDiagram) : Set (ℕ → ZMod n) :=
  {f | (∀ x ∉ D.arcs, f x = 0) ∧ ∀ x ∈ D.crossings, f x.2.1 + f x.2.2 = 2 * f x.1}

/-- The number of Fox `n`-labelings of a diagram. -/
noncomputable def foxCount (n : ℕ) (D : LinkDiagram) : ℕ := (foxLabelings n D).ncard

/-- Apply a renaming of arcs to a crossing. -/
def map3 (φ : ℕ → ℕ) (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (φ x.1, φ x.2.1, φ x.2.2)

/-- Exchange the two under-arcs of a crossing. -/
def swapUnder (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1, x.2.2, x.2.1)

/-- The renaming that identifies the arc `b` with the arc `t`. -/
def renameTo (b t : ℕ) (x : ℕ) : ℕ := if x = b then t else x

/-- Renaming the arcs of a diagram by a bijection. -/
def Relabel (D D' : LinkDiagram) : Prop :=
  ∃ σ : ℕ ≃ ℕ, D'.arcs = D.arcs.map σ.toEmbedding ∧ D'.crossings = D.crossings.map (map3 σ)

/-- Reordering the crossings, and the two under-arcs within crossings. -/
def Rearrange (D D' : LinkDiagram) : Prop :=
  D'.arcs = D.arcs ∧ ∃ L, List.Forall₂ (fun x y => y = x ∨ y = swapUnder x) D.crossings L ∧
    L.Perm D'.crossings

/-- Reidemeister move I: a kink is added to the arc `a`.  The arc `a` is split into `a` and a new
arc `b` (or, if `a` had no under-crossings at all, stays one arc, `b = a`), the occurrences of `a`
in old crossings are distributed among `a` and `b`, and the new crossing is `(a, a, b)` or
`(b, a, b)`. -/
def ReidemeisterI (D D' : LinkDiagram) : Prop :=
  ∃ a b L', a ∈ D.arcs ∧ (b ∉ D.arcs ∨ b = a) ∧ D'.arcs = insert b D.arcs ∧
    (D'.crossings = (a, a, b) :: L' ∨ D'.crossings = (b, a, b) :: L') ∧
    L'.map (map3 (renameTo b a)) = D.crossings

/-- Reidemeister move II: the arc `t` is pushed under a part of the arc `o`, creating a short new
arc `m` and splitting `t` into `t` and `b` (or `b = t` if `t` had no under-crossings). -/
def ReidemeisterII (D D' : LinkDiagram) : Prop :=
  ∃ o t m b L', t ∈ D.arcs ∧ m ∉ D.arcs ∧ m ≠ b ∧ (b ∉ D.arcs ∨ b = t) ∧
    o ∈ insert b D.arcs ∧ D'.arcs = insert m (insert b D.arcs) ∧
    D'.crossings = (o, t, m) :: (o, m, b) :: L' ∧ L'.map (map3 (renameTo b t)) = D.crossings

/-- Reidemeister move III: the bottom strand (arcs `c`, `e`, `x`) is moved under the crossing of
the top strand `a` and the middle strand (arcs `b`, `m`).  The short middle arc `e` of the bottom
strand changes its crossings. -/
def ReidemeisterIII (D D' : LinkDiagram) : Prop :=
  ∃ a b m c e x L, D'.arcs = D.arcs ∧ e ≠ a ∧ e ≠ b ∧ e ≠ m ∧ e ≠ c ∧ e ≠ x ∧
    (∀ y ∈ L, y.1 ≠ e ∧ y.2.1 ≠ e ∧ y.2.2 ≠ e) ∧
    D.crossings = (a, b, m) :: (a, c, e) :: (m, e, x) :: L ∧
    D'.crossings = (a, b, m) :: (b, c, e) :: (a, e, x) :: L

/-- One elementary move between diagrams. -/
def DiagramMove (D D' : LinkDiagram) : Prop :=
  Relabel D D' ∨ Rearrange D D' ∨ ReidemeisterI D D' ∨ ReidemeisterII D D' ∨
    ReidemeisterIII D D'

/-- Equivalence of diagrams: connected by a finite sequence of moves (in either direction). -/
def DiagramEquiv : LinkDiagram → LinkDiagram → Prop := Relation.EqvGen DiagramMove

/-! ### The diagrams of the chapter -/

/-- The standard diagram of the Borromean rings: outer arcs `0, 1, 2` (labels `a, b, c`), inner
arcs `3, 4, 5` (labels `2b - a, 2c - b, 2a - c`). -/
def borromean : LinkDiagram where
  arcs := Finset.range 6
  crossings := [(1, 0, 3), (2, 1, 4), (0, 2, 5), (3, 2, 5), (4, 0, 3), (5, 1, 4)]
  wf := by decide

/-- Tait's link No. 18: outer arcs `0, …, 5` (labels `a, …, f`), inner arcs `6, …, 11`
(labels `2a - b, 2b - c, …, 2f - a`). -/
def tait18 : LinkDiagram where
  arcs := Finset.range 12
  crossings := [(0, 1, 6), (1, 2, 7), (2, 3, 8), (3, 4, 9), (4, 5, 10), (5, 0, 11),
    (7, 0, 8), (8, 1, 9), (9, 2, 10), (10, 3, 11), (11, 4, 6), (6, 5, 7)]
  wf := by decide

/-- The trivial link with three components: three circles without crossings. -/
def trivialLink3 : LinkDiagram where
  arcs := Finset.range 3
  crossings := []
  wf := by decide

/-! ### Invariance under the moves -/

lemma ncard_eq_of_inverse {α β : Type*} {s : Set α} {t : Set β} (F : α → β) (G : β → α)
    (hF : ∀ a ∈ s, F a ∈ t) (hG : ∀ b ∈ t, G b ∈ s) (hGF : ∀ a ∈ s, G (F a) = a)
    (hFG : ∀ b ∈ t, F (G b) = b) : s.ncard = t.ncard :=
  Set.ncard_congr (fun a _ => F a) hF
    (fun a b ha hb h => by rw [← hGF a ha, ← hGF b hb]; exact congrArg G h)
    (fun b hb => ⟨G b, hG b hb, hFG b hb⟩)

lemma foxCount_relabel {n : ℕ} {D D' : LinkDiagram} (h : Relabel D D') :
    foxCount n D = foxCount n D' := by
  obtain ⟨σ, ha, hc⟩ := h
  refine ncard_eq_of_inverse (fun f => f ∘ σ.symm) (fun f => f ∘ σ) ?_ ?_ ?_ ?_
  · rintro f ⟨h1, h2⟩
    refine ⟨fun x hx => h1 _ ?_, fun x hx => ?_⟩
    · intro hx'; apply hx; rw [ha]; exact Finset.mem_map.2 ⟨_, hx', by simp⟩
    · rw [hc] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      simpa [map3] using h2 y hy
  · rintro f ⟨h1, h2⟩
    refine ⟨fun x hx => h1 _ ?_, fun x hx => ?_⟩
    · rw [ha]; simpa using hx
    · simpa [map3] using h2 (map3 σ x) (by rw [hc]; exact List.mem_map_of_mem hx)
  · intro f _; funext x; simp
  · intro f _; funext x; simp

lemma foxCount_rearrange {n : ℕ} {D D' : LinkDiagram} (h : Rearrange D D') :
    foxCount n D = foxCount n D' := by
  obtain ⟨ha, L, hL, hp⟩ := h
  unfold foxCount foxLabelings
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq, ha]
  refine and_congr Iff.rfl ?_
  have key : ∀ (L₁ L₂ : List (ℕ × ℕ × ℕ)),
      List.Forall₂ (fun x y => y = x ∨ y = swapUnder x) L₁ L₂ →
      ((∀ x ∈ L₁, f x.2.1 + f x.2.2 = 2 * f x.1) ↔ (∀ x ∈ L₂, f x.2.1 + f x.2.2 = 2 * f x.1)) := by
    intro L₁ L₂ h
    induction h with
    | nil => simp
    | cons hxy _ ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      refine and_congr ?_ ih
      rcases hxy with rfl | rfl
      · rfl
      · simp [swapUnder, add_comm]
  rw [key _ _ hL]
  exact ⟨fun h x hx => h x (hp.mem_iff.2 hx), fun h x hx => h x (hp.mem_iff.1 hx)⟩

lemma renameTo_self (b a : ℕ) : renameTo b a a = a := by
  unfold renameTo; split_ifs with h <;> simp [h]

lemma renameTo_of_ne {b a x : ℕ} (h : x ≠ b) : renameTo b a x = x := by
  simp [renameTo, h]

lemma renameTo_eq_self {D : LinkDiagram} {a b x : ℕ} (hb : b ∉ D.arcs ∨ b = a) (hx : x ∈ D.arcs) :
    renameTo b a x = x := by
  rcases hb with hb | rfl
  · exact renameTo_of_ne (by rintro rfl; exact hb hx)
  · unfold renameTo; split_ifs with h <;> simp [h]

lemma foxCount_reidemeisterI {n : ℕ} {D D' : LinkDiagram} (h : ReidemeisterI D D') :
    foxCount n D = foxCount n D' := by
  obtain ⟨a, b, L', ha, hb, harcs, hk, hL⟩ := h
  set φ := renameTo b a
  -- a labeling of `D'` takes the same value on `a` and `b`
  have kink : ∀ f ∈ foxLabelings n D', f a = f b := by
    rintro f ⟨-, h2⟩
    rcases hk with hk | hk
    · have := h2 (a, a, b) (by rw [hk]; simp)
      simp only at this; linear_combination -this
    · have := h2 (b, a, b) (by rw [hk]; simp)
      simp only at this; linear_combination this
  have hL' : ∀ y ∈ L', y ∈ D'.crossings := by
    intro y hy; rcases hk with hk | hk <;> rw [hk] <;> exact List.mem_cons_of_mem _ hy
  let G : (ℕ → ZMod n) → ℕ → ZMod n := fun f x => if x ∈ D.arcs then f x else 0
  have hGφ : ∀ f ∈ foxLabelings n D', ∀ y ∈ D'.arcs, G f (φ y) = f y := by
    intro f hf y hy
    by_cases hyb : y = b
    · subst hyb; simp only [φ, renameTo, ite_true, G, ite_eq_left ha]; exact kink f hf
    · have hy' : y ∈ D.arcs := by
        rw [harcs, Finset.mem_insert] at hy; tauto
      simp only [φ, renameTo_of_ne hyb, G, ite_eq_left hy']
  refine ncard_eq_of_inverse (fun f x => f (φ x)) G ?_ ?_ ?_ ?_
  · rintro f ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hxb : x ≠ b := by rintro rfl; exact hx (by rw [harcs]; simp)
      have hxD : x ∉ D.arcs := by intro h; exact hx (by rw [harcs]; simp [h])
      simp only [φ, renameTo_of_ne hxb]; exact h1 x hxD
    · rcases hk with hk | hk <;> rw [hk] at hx <;> rcases List.mem_cons.1 hx with rfl | hx
      · simp [φ, renameTo, renameTo_self]; ring
      · exact h2 _ (hL ▸ List.mem_map_of_mem hx)
      · simp [φ, renameTo, renameTo_self]; ring
      · exact h2 _ (hL ▸ List.mem_map_of_mem hx)
  · rintro f hf
    refine ⟨fun x hx => by simp [G, hx], fun x hx => ?_⟩
    rw [← hL] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨w1, w2, w3⟩ := D'.wf y (hL' y hy)
    simp only [map3]
    rw [hGφ f hf _ w1, hGφ f hf _ w2, hGφ f hf _ w3]
    exact hf.2 y (hL' y hy)
  · rintro f ⟨h1, -⟩
    funext x
    by_cases hx : x ∈ D.arcs
    · simp [G, hx, φ, renameTo_eq_self hb hx]
    · simp [G, hx, h1 x hx]
  · rintro f hf
    funext x
    by_cases hx : x ∈ D'.arcs
    · exact hGφ f hf x hx
    · have hxb : x ≠ b := by rintro rfl; exact hx (by rw [harcs]; simp)
      have hxD : x ∉ D.arcs := by intro h; exact hx (by rw [harcs]; simp [h])
      simp [G, φ, renameTo_of_ne hxb, hxD, hf.1 x hx]

lemma foxCount_reidemeisterII {n : ℕ} {D D' : LinkDiagram} (h : ReidemeisterII D D') :
    foxCount n D = foxCount n D' := by
  obtain ⟨o, t, m, b, L', ht, hm, hmb, hb, ho, harcs, hc, hL⟩ := h
  set φ := renameTo b t
  have hom : o ≠ m := by
    rintro rfl; rw [Finset.mem_insert] at ho; rcases ho with h | h
    · exact hmb h
    · exact hm h
  have htm : t ≠ m := by rintro rfl; exact hm ht
  have hφm : φ m = m := renameTo_of_ne hmb
  have hφt : φ t = t := renameTo_eq_self hb ht
  have hφb : φ b = t := by simp [φ, renameTo]
  have hL' : ∀ y ∈ L', y ∈ D'.crossings := by
    intro y hy; rw [hc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
  have hnotm : ∀ y ∈ L', y.1 ≠ m ∧ y.2.1 ≠ m ∧ y.2.2 ≠ m := by
    intro y hy
    obtain ⟨w1, w2, w3⟩ := D.wf (map3 φ y) (hL ▸ List.mem_map_of_mem hy)
    simp only [map3] at w1 w2 w3
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [h, hφm] at w1; exact hm w1
    · rw [h, hφm] at w2; exact hm w2
    · rw [h, hφm] at w3; exact hm w3
  have hbt : ∀ f ∈ foxLabelings n D', f b = f t := by
    rintro f ⟨-, h2⟩
    have e1 := h2 (o, t, m) (by rw [hc]; simp)
    have e2 := h2 (o, m, b) (by rw [hc]; simp)
    simp only at e1 e2
    linear_combination e2 - e1
  let G : (ℕ → ZMod n) → ℕ → ZMod n := fun f x => if x ∈ D.arcs then f x else 0
  have hGφ : ∀ f ∈ foxLabelings n D', ∀ y ∈ D'.arcs, y ≠ m → G f (φ y) = f y := by
    intro f hf y hy hym
    by_cases hyb : y = b
    · subst hyb; rw [hφb]; simp only [G, ite_eq_left ht]; exact (hbt f hf).symm
    · have hy' : y ∈ D.arcs := by
        rw [harcs, Finset.mem_insert, Finset.mem_insert] at hy; tauto
      simp only [φ, renameTo_of_ne hyb, G, ite_eq_left hy']
  refine ncard_eq_of_inverse (fun f x => if x = m then 2 * f (φ o) - f t else f (φ x)) G
    ?_ ?_ ?_ ?_
  · rintro f ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hxm : x ≠ m := by rintro rfl; exact hx (by rw [harcs]; simp)
      have hxb : x ≠ b := by rintro rfl; exact hx (by rw [harcs]; simp)
      have hxD : x ∉ D.arcs := by intro h; exact hx (by rw [harcs]; simp [h])
      simp only [ite_eq_right hxm, φ, renameTo_of_ne hxb]; exact h1 x hxD
    · rw [hc] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp only [ite_eq_right hom, ite_eq_right htm, ite_true, hφt]; ring
      rcases List.mem_cons.1 hx with rfl | hx
      · simp only [ite_eq_right hom, ite_eq_right hmb.symm, ite_true, hφb]; ring
      obtain ⟨n1, n2, n3⟩ := hnotm x hx
      simp only [ite_eq_right n1, ite_eq_right n2, ite_eq_right n3]
      exact h2 _ (hL ▸ List.mem_map_of_mem hx)
  · rintro f hf
    refine ⟨fun x hx => by simp [G, hx], fun x hx => ?_⟩
    rw [← hL] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨w1, w2, w3⟩ := D'.wf y (hL' y hy)
    obtain ⟨n1, n2, n3⟩ := hnotm y hy
    simp only [map3]
    rw [hGφ f hf _ w1 n1, hGφ f hf _ w2 n2, hGφ f hf _ w3 n3]
    exact hf.2 y (hL' y hy)
  · rintro f ⟨h1, -⟩
    funext x
    by_cases hx : x ∈ D.arcs
    · have hxm : x ≠ m := by rintro rfl; exact hm hx
      simp [G, hx, hxm, φ, renameTo_eq_self hb hx]
    · simp [G, hx, h1 x hx]
  · rintro f hf
    funext x
    by_cases hxm : x = m
    · subst hxm
      simp only [ite_true]
      have hoD' : o ∈ D'.arcs := by rw [harcs]; exact Finset.mem_insert_of_mem ho
      rw [hGφ f hf o hoD' hom]
      simp only [G, ite_eq_left ht]
      have e1 := hf.2 (o, t, x) (by rw [hc]; simp)
      simp only at e1
      linear_combination -e1
    · simp only [ite_eq_right hxm]
      by_cases hx : x ∈ D'.arcs
      · exact hGφ f hf x hx hxm
      · have hxb : x ≠ b := by rintro rfl; exact hx (by rw [harcs]; simp)
        have hxD : x ∉ D.arcs := by intro h; exact hx (by rw [harcs]; simp [h])
        simp [G, φ, renameTo_of_ne hxb, hxD, hf.1 x hx]

lemma foxCount_reidemeisterIII {n : ℕ} {D D' : LinkDiagram} (h : ReidemeisterIII D D') :
    foxCount n D = foxCount n D' := by
  obtain ⟨a, b, m, c, e, x, L, harcs, hea, heb, hem, hec, hex, hL, hD, hD'⟩ := h
  have hLeq : ∀ (f : ℕ → ZMod n) (v : ZMod n),
      ((∀ y ∈ L, f y.2.1 + f y.2.2 = 2 * f y.1) ↔
        (∀ y ∈ L, Function.update f e v y.2.1 + Function.update f e v y.2.2 =
          2 * Function.update f e v y.1)) := by
    intro f v
    refine forall₂_congr fun y hy => ?_
    obtain ⟨n1, n2, n3⟩ := hL y hy
    simp [Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3]
  have heD : e ∈ D.arcs := (D.wf (a, c, e) (by rw [hD]; simp)).2.2
  refine ncard_eq_of_inverse (fun f => Function.update f e (2 * f b - f c))
    (fun f => Function.update f e (2 * f a - f c)) ?_ ?_ ?_ ?_
  · rintro f ⟨h1, h2⟩
    rw [hD] at h2
    simp only [List.mem_cons, forall_eq_or_imp] at h2
    obtain ⟨e1, e2, e3, e4⟩ := h2
    refine ⟨fun y hy => ?_, ?_⟩
    · have hye : y ≠ e := by rintro rfl; exact hy (harcs ▸ heD)
      rw [Function.update_of_ne hye]; exact h1 y (harcs ▸ hy)
    rw [hD']
    simp only [List.mem_cons, forall_eq_or_imp]
    simp only [Function.update_of_ne hea.symm, Function.update_of_ne heb.symm,
      Function.update_of_ne hem.symm, Function.update_of_ne hec.symm,
      Function.update_of_ne hex.symm, Function.update_self] at e1 e2 e3 ⊢
    refine ⟨e1, by ring, by linear_combination e3 + 2 * e1 - e2, (hLeq f _).1 e4⟩
  · rintro f ⟨h1, h2⟩
    rw [hD'] at h2
    simp only [List.mem_cons, forall_eq_or_imp] at h2
    obtain ⟨e1, e2, e3, e4⟩ := h2
    refine ⟨fun y hy => ?_, ?_⟩
    · have hye : y ≠ e := by rintro rfl; exact hy (harcs ▸ heD)
      rw [Function.update_of_ne hye]; exact h1 y (harcs ▸ hy)
    rw [hD]
    simp only [List.mem_cons, forall_eq_or_imp]
    simp only [Function.update_of_ne hea.symm, Function.update_of_ne heb.symm,
      Function.update_of_ne hem.symm, Function.update_of_ne hec.symm,
      Function.update_of_ne hex.symm, Function.update_self] at e1 e2 e3 ⊢
    refine ⟨e1, by ring, by linear_combination e3 - e2 - 2 * e1, (hLeq f _).1 e4⟩
  · rintro f ⟨-, h2⟩
    have e2 := h2 (a, c, e) (by rw [hD]; simp)
    simp only at e2
    rw [Function.update_idem, Function.update_of_ne hea.symm, Function.update_of_ne hec.symm]
    exact Function.update_eq_self_iff.2 (by linear_combination -e2)
  · rintro f ⟨-, h2⟩
    have e2 := h2 (b, c, e) (by rw [hD']; simp)
    simp only at e2
    rw [Function.update_idem, Function.update_of_ne heb.symm, Function.update_of_ne hec.symm]
    exact Function.update_eq_self_iff.2 (by linear_combination -e2)

/-- **Claim (Theorem 2).** Equivalent diagrams have the same number of Fox `n`-labelings. -/
theorem foxCount_eq_of_diagramEquiv (n : ℕ) {D D' : LinkDiagram} (h : DiagramEquiv D D') :
    foxCount n D = foxCount n D' := by
  induction h with
  | rel D D' hm =>
    rcases hm with h | h | h | h | h
    · exact foxCount_relabel h
    · exact foxCount_rearrange h
    · exact foxCount_reidemeisterI h
    · exact foxCount_reidemeisterII h
    · exact foxCount_reidemeisterIII h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Counting labelings -/

/-- A constant label on the arcs satisfies every crossing relation. -/
theorem const_mem_foxLabelings (n : ℕ) (D : LinkDiagram) (a : ZMod n) :
    (fun x => if x ∈ D.arcs then a else 0) ∈ foxLabelings n D := by
  refine ⟨fun x hx => by simp [hx], fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := D.wf x hx
  simp [h1, h2, h3]; ring

/-- The trivial three component link has `n ^ 3` Fox `n`-labelings. -/
theorem foxCount_trivialLink3 (n : ℕ) : foxCount n trivialLink3 = n ^ 3 := by
  let g : (Fin 3 → ZMod n) → ℕ → ZMod n := fun v x => if h : x < 3 then v ⟨x, h⟩ else 0
  have hg : Function.Injective g := by
    intro v w h
    funext i
    have := congrFun h i
    simpa [g, i.2] using this
  have : foxLabelings n trivialLink3 = Set.range g := by
    ext f
    simp only [foxLabelings, trivialLink3, Finset.mem_range, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · intro hf
      refine ⟨fun i => f i, funext fun x => ?_⟩
      by_cases hx : x < 3
      · simp [g, hx]
      · simp [g, hx, hf x hx]
    · rintro ⟨v, rfl⟩ x hx
      simp [g, hx]
  rw [foxCount, this, Set.ncard_range_of_injective hg, Nat.card_fun]
  simp

lemma two_mul_cancel_of_odd {n : ℕ} (hn : Odd n) {u v : ZMod n} (h : 2 * u = 2 * v) : u = v := by
  have hu : IsUnit (2 : ZMod n) := by
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hn)).isUnit
    simpa using this
  exact hu.mul_left_cancel h

/-- For odd `n`, the Borromean rings have only the `n` trivial Fox `n`-labelings. -/
theorem foxCount_borromean_of_odd {n : ℕ} (hn : Odd n) : foxCount n borromean = n := by
  let g : ZMod n → ℕ → ZMod n := fun a x => if x < 6 then a else 0
  have hg : Function.Injective g := by
    intro a b h
    simpa [g] using congrFun h 0
  have : foxLabelings n borromean = Set.range g := by
    ext f
    constructor
    · rintro ⟨h1, h2⟩
      simp only [borromean, Finset.mem_range, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at h1 h2
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h2
      have c : ∀ {u v : ZMod n}, 2 * u = 2 * v → u = v := two_mul_cancel_of_odd hn
      have h10 : f 1 = f 0 := c <| c <| by linear_combination -2 * e1 + e3 - e4
      have h21 : f 2 = f 1 := c <| c <| by linear_combination -2 * e2 + e1 - e5
      have h30 : f 3 = f 0 := c <| by linear_combination e3 - e4
      have h41 : f 4 = f 1 := c <| by linear_combination e1 - e5
      have h52 : f 5 = f 2 := c <| by linear_combination e2 - e6
      refine ⟨f 0, funext fun x => ?_⟩
      by_cases hx : x < 6
      · simp only [g, ite_eq_left hx]
        interval_cases x
        · rfl
        · exact h10.symm
        · exact (h21.trans h10).symm
        · exact h30.symm
        · exact (h41.trans h10).symm
        · exact (h52.trans (h21.trans h10)).symm
      · simp only [g, ite_eq_right hx, h1 x hx]
    · rintro ⟨a, rfl⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simp only [borromean, Finset.mem_range] at hx; simp [g, hx]
      · simp only [borromean, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [g] <;> ring
  rw [foxCount, this, Set.ncard_range_of_injective hg, Nat.card_zmod]

/-- For every even `n ≥ 2`, the Borromean rings have a nontrivial Fox `n`-labeling. -/
theorem borromean_nontrivial_of_even {n : ℕ} (hn : Even n) (h2 : 2 ≤ n) :
    ∃ f ∈ foxLabelings n borromean, f 0 ≠ f 1 := by
  set k := n / 2
  have hk : 2 * (k : ZMod n) = 0 := by
    have : ((2 * k : ℕ) : ZMod n) = 0 := by
      rw [Nat.two_mul_div_two_of_even hn]; exact ZMod.natCast_self n
    simpa using this
  have hk0 : (k : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have : 0 < k := by omega
    have : k < n := by omega
    exact absurd (Nat.le_of_dvd ‹0 < k› h) (by omega)
  refine ⟨fun x => if x = 0 ∨ x = 3 then (k : ZMod n) else 0, ⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · simp only [borromean, Finset.mem_range] at hx
    have : ¬ (x = 0 ∨ x = 3) := by omega
    simp [this]
  · simp only [borromean, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
      first | linear_combination hk | linear_combination -hk
  · simpa using hk0

/-- Tait's link No. 18 has only the 3 trivial Fox 3-labelings. -/
theorem foxCount_tait18_three : foxCount 3 tait18 = 3 := by
  let g : ZMod 3 → ℕ → ZMod 3 := fun a x => if x < 12 then a else 0
  have hg : Function.Injective g := by
    intro a b h
    simpa [g] using congrFun h 0
  have : foxLabelings 3 tait18 = Set.range g := by
    ext f
    constructor
    · rintro ⟨h1, h2⟩
      simp only [tait18, Finset.mem_range, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at h1 h2
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h2
      have T0 : f 0 + f 2 = f 1 + f 3 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) e7 - e3 + 2 * e2
      have T1 : f 1 + f 3 = f 2 + f 4 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) e8 - e4 + 2 * e3
      have T2 : f 2 + f 4 = f 3 + f 5 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) e9 - e5 + 2 * e4
      have T3 : f 3 + f 5 = f 4 + f 0 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) e10 - e6 + 2 * e5
      have T4 : f 4 + f 0 = f 5 + f 1 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) e11 - e1 + 2 * e6
      have h4 : f 4 = f 0 := by linear_combination -T0 - T1
      have h2 : f 2 = f 0 := by linear_combination T2 + T3
      have h5 : f 5 = f 1 := by linear_combination -T1 - T2
      have h3 : f 3 = f 1 := by linear_combination T3 + T4
      have h1' : f 1 = f 0 := by
        linear_combination (norm := (ring_nf; reduce_mod_char)) T0 - h2 + h3
      have h6 : f 6 = f 0 := by linear_combination e1 - h1'
      have h7 : f 7 = f 0 := by linear_combination e2 - h2 + 2 * h1'
      have h8 : f 8 = f 0 := by linear_combination e3 - h3 - h1' + 2 * h2
      have h9 : f 9 = f 0 := by linear_combination e4 - h4 + 2 * h3 + 2 * h1'
      have h10 : f 10 = f 0 := by linear_combination e5 - h5 - h1' + 2 * h4
      have h11 : f 11 = f 0 := by linear_combination e6 + 2 * h5 + 2 * h1'
      refine ⟨f 0, funext fun x => ?_⟩
      by_cases hx : x < 12
      · simp only [g, ite_eq_left hx]
        interval_cases x <;> simp only [h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
      · simp only [g, ite_eq_right hx, h1 x hx]
    · rintro ⟨a, rfl⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simp only [tait18, Finset.mem_range] at hx; simp [g, hx]
      · simp only [tait18, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [g] <;> ring
  rw [foxCount, this, Set.ncard_range_of_injective hg, Nat.card_zmod]

/-- Tait's link No. 18 has `5 ^ 2 = 25` Fox 5-labelings: `a ≡ c ≡ e` and `b ≡ d ≡ f` arbitrary. -/
theorem foxCount_tait18_five : foxCount 5 tait18 = 25 := by
  let g : ZMod 5 × ZMod 5 → ℕ → ZMod 5 := fun p x =>
    if x < 6 then (if x % 2 = 0 then p.1 else p.2)
    else if x < 12 then (if x % 2 = 0 then 2 * p.1 - p.2 else 2 * p.2 - p.1) else 0
  have hg : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [g] at h0 h1
    norm_num at h0 h1
    rw [h0, h1]
  have h5 : (5 : ZMod 5) = 0 := rfl
  have : foxLabelings 5 tait18 = Set.range g := by
    ext f
    constructor
    · rintro ⟨h1, h2⟩
      simp only [tait18, Finset.mem_range, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at h1 h2
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h2
      have T0 : f 0 + f 1 = f 2 + f 3 := by
        linear_combination e7 - e3 + 2 * e2 + (f 1 - f 2) * h5
      have T1 : f 1 + f 2 = f 3 + f 4 := by
        linear_combination e8 - e4 + 2 * e3 + (f 2 - f 3) * h5
      have T2 : f 2 + f 3 = f 4 + f 5 := by
        linear_combination e9 - e5 + 2 * e4 + (f 3 - f 4) * h5
      have T3 : f 3 + f 4 = f 5 + f 0 := by
        linear_combination e10 - e6 + 2 * e5 + (f 4 - f 5) * h5
      have T4 : f 4 + f 5 = f 0 + f 1 := by
        linear_combination e11 - e1 + 2 * e6 + (f 5 - f 0) * h5
      have T5 : f 5 + f 0 = f 1 + f 2 := by
        linear_combination e12 - e2 + 2 * e1 + (f 0 - f 1) * h5
      have h42 : f 4 = f 2 := by
        linear_combination 2 * (T0 - T1 - T2 + T3) - (f 4 - f 2) * h5
      have h04 : f 0 = f 4 := by
        linear_combination 2 * (T2 - T3 - T4 + T5) - (f 0 - f 4) * h5
      have h53 : f 5 = f 3 := by
        linear_combination 2 * (T1 - T2 - T3 + T4) - (f 5 - f 3) * h5
      have h15 : f 1 = f 5 := by
        linear_combination 2 * (T3 - T4 - T5 + T0) - (f 1 - f 5) * h5
      have h2 : f 2 = f 0 := by linear_combination -h42 - h04
      have h3 : f 3 = f 1 := by linear_combination -h53 - h15
      have h4 : f 4 = f 0 := by linear_combination -h04
      have h5 : f 5 = f 1 := by linear_combination -h15
      have h6 : f 6 = 2 * f 0 - f 1 := by linear_combination e1
      have h7 : f 7 = 2 * f 1 - f 0 := by linear_combination e2 - h2
      have h8 : f 8 = 2 * f 0 - f 1 := by linear_combination e3 - h3 + 2 * h2
      have h9 : f 9 = 2 * f 1 - f 0 := by linear_combination e4 - h4 + 2 * h3
      have h10 : f 10 = 2 * f 0 - f 1 := by linear_combination e5 - h5 + 2 * h4
      have h11 : f 11 = 2 * f 1 - f 0 := by linear_combination e6 + 2 * h5
      refine ⟨(f 0, f 1), funext fun x => ?_⟩
      by_cases hx : x < 12
      · interval_cases x <;> norm_num [g, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
      · have : ¬ x < 6 := by omega
        simp only [g, ite_eq_right hx, ite_eq_right this, h1 x hx]
    · rintro ⟨⟨a, b⟩, rfl⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simp only [tait18, Finset.mem_range] at hx
        have : ¬ x < 6 := by omega
        simp only [g, ite_eq_right hx, ite_eq_right this]
      · simp only [tait18, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num [g] <;>
          first | ring1 | linear_combination (a - b) * h5 | linear_combination (b - a) * h5
  rw [foxCount, this, Set.ncard_range_of_injective hg, Nat.card_prod, Nat.card_zmod]

/-- **Theorem 2.** The Borromean rings are nontrivial, and they are not equivalent to Tait's link
No. 18 (which is nontrivial as well): the three diagrams have 5, 25 and 125 Fox 5-labelings. -/
theorem borromean_theorem :
    ¬ DiagramEquiv borromean trivialLink3 ∧ ¬ DiagramEquiv borromean tait18 ∧
      ¬ DiagramEquiv tait18 trivialLink3 := by
  have hB : foxCount 5 borromean = 5 := foxCount_borromean_of_odd (by decide)
  have hT : foxCount 5 tait18 = 25 := foxCount_tait18_five
  have h0 : foxCount 5 trivialLink3 = 125 := foxCount_trivialLink3 5
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    have := foxCount_eq_of_diagramEquiv 5 h <;> omega

end Chapter15
