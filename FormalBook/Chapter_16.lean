/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Tactic

/-!
# Touching simplices

A formalization of the chapter "Touching simplices" of *Proofs from THE BOOK*.

Source: Aigner and Ziegler, sixth edition, Chapter 16, pp. 107–110,
https://doi.org/10.1007/978-3-662-57265-8_16.

* `IsSimplex`, `Touching`, `IsTouchingFamily`, `touchingNumber` (the number `f(d)`),
  `IsTransversal`;
* the conjecture (Bagemihl) `BagemihlConjecture`, stated as a proposition;
* **Theorem 1** (Zaks) `TouchingSimplices.zaks`: for `d ≥ 2` there are `2^d` pairwise touching
  `d`-simplices in `ℝ^d` with a common transversal line; hence `2^d ≤ f(d)`;
* **Theorem 2** (Perles) `TouchingSimplices.perles` / `TouchingSimplices.touchingNumber_lt`:
  `f(d) < 2^(d+1)`;
* `f(1) = 2`, `4 ≤ f(2) ≤ 7`, `8 ≤ f(3) ≤ 15`; the statements `f(2) = 4` and `f(3) = 8` quoted in
  the chapter are recorded as propositions.

The file is organised in sections following the structure of the chapter.
-/

@[expose] public section

noncomputable section


section Defs

/-!
# Touching simplices: basic definitions

We work in an arbitrary real vector space `E` (in the applications `E = Fin d → ℝ`, i.e. `ℝ^d`).

* `IsSimplex n P` : `P` is an `n`-simplex, the convex hull of `n + 1` affinely independent points.
* `Touching n P Q` : the intersection `P ∩ Q` is nonempty and has (affine) dimension `n - 1`,
  i.e. `dim (P ∩ Q) + 1 = n`.
* `IsTouchingFamily n P` : a family of `n`-simplices which pairwise touch.
* `touchingNumber d` : the number `f(d)` of the chapter, the maximal number of pairwise touching
  `d`-simplices in `ℝ^d`.
-/


open Set Module

namespace TouchingSimplices

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `P` is an `n`-dimensional simplex: the convex hull of `n + 1` affinely independent points. -/
def IsSimplex (n : ℕ) (P : Set E) : Prop :=
  ∃ v : Fin (n + 1) → E, AffineIndependent ℝ v ∧ P = convexHull ℝ (range v)

/-- Two (`n`-dimensional) simplices *touch* if their intersection is `(n-1)`-dimensional:
it is nonempty and its affine span has dimension `n - 1`. -/
def Touching (n : ℕ) (P Q : Set E) : Prop :=
  (P ∩ Q).Nonempty ∧ finrank ℝ (vectorSpan ℝ (P ∩ Q)) + 1 = n

/-- A family of `n`-simplices, any two of which (with different indices) touch. -/
def IsTouchingFamily (n : ℕ) {ι : Type*} (P : ι → Set E) : Prop :=
  (∀ i, IsSimplex n (P i)) ∧ Pairwise fun i j => Touching n (P i) (P j)

/-- `f(d)`: the maximal number of pairwise touching `d`-simplices in `ℝ^d`
(defined as a supremum; by Theorem 2 the set of such numbers is bounded for `d ≥ 1`). -/
noncomputable def touchingNumber (d : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ P : Fin r → Set (Fin d → ℝ), IsTouchingFamily d P}

/-- A line `{p + t • v | t ∈ ℝ}` (with `v ≠ 0`) is a *transversal* of a family of sets
if it hits the interior of each of them. -/
def IsTransversal {ι : Type*} [TopologicalSpace E] (P : ι → Set E) (p v : E) : Prop :=
  v ≠ 0 ∧ ∀ i, ∃ t : ℝ, p + t • v ∈ interior (P i)

end TouchingSimplices

end Defs


section Simplex

/-!
# Basic facts about simplices and touching families

* simplices of full dimension come from affine bases;
* affine equivalences preserve simplices, touching and touching families;
* two affine functionals with the same zero set are proportional.
-/


open Set Module

namespace TouchingSimplices

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Membership in a set-builder set (stated locally to be stable across Mathlib versions). -/
theorem mem_setOf_iff' {α : Type*} {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a := Iff.rfl

/-- A `d`-simplex in a `d`-dimensional space is the convex hull of an affine basis. -/
lemma IsSimplex.exists_affineBasis [FiniteDimensional ℝ E] {d : ℕ} (hE : finrank ℝ E = d)
    {P : Set E} (hP : IsSimplex d P) :
    ∃ b : AffineBasis (Fin (d + 1)) ℝ E, P = convexHull ℝ (range b) := by
  obtain ⟨v, hv, rfl⟩ := hP
  have htot : affineSpan ℝ (range v) = ⊤ := by
    rw [hv.affineSpan_eq_top_iff_card_eq_finrank_add_one]; simp [hE]
  exact ⟨⟨v, hv, htot⟩, rfl⟩

lemma IsSimplex.image {n : ℕ} {P : Set E} (hP : IsSimplex n P) (e : E ≃ᵃ[ℝ] F) :
    IsSimplex n (e '' P) := by
  obtain ⟨v, hv, rfl⟩ := hP
  refine ⟨e ∘ v, e.affineIndependent_iff.2 hv, ?_⟩
  rw [range_comp]
  exact (e : E →ᵃ[ℝ] F).image_convexHull _

lemma finrank_vectorSpan_image (e : E ≃ᵃ[ℝ] F) (S : Set E) :
    finrank ℝ (vectorSpan ℝ (e '' S)) = finrank ℝ (vectorSpan ℝ S) := by
  have h := AffineMap.map_vectorSpan (e : E →ᵃ[ℝ] F) (s := S)
  change Submodule.map (e.linear : E →ₗ[ℝ] F) (vectorSpan ℝ S) = vectorSpan ℝ (e '' S) at h
  rw [← h]
  exact LinearEquiv.finrank_map_eq e.linear _

lemma Touching.image {n : ℕ} {P Q : Set E} (h : Touching n P Q) (e : E ≃ᵃ[ℝ] F) :
    Touching n (e '' P) (e '' Q) := by
  obtain ⟨hne, hdim⟩ := h
  rw [Touching, ← image_inter e.injective, finrank_vectorSpan_image]
  exact ⟨hne.image _, hdim⟩

lemma IsTouchingFamily.image {n : ℕ} {ι : Type*} {P : ι → Set E} (h : IsTouchingFamily n P)
    (e : E ≃ᵃ[ℝ] F) : IsTouchingFamily n (fun i => e '' P i) :=
  ⟨fun i => (h.1 i).image e, fun _ _ hij => (h.2 hij).image e⟩

/-- Two affine functionals with the same zero set are proportional (provided the first one
vanishes somewhere and does not vanish identically). -/
lemma affineMap_eq_mul_of_zero_iff (f g : E →ᵃ[ℝ] ℝ) (h : ∀ x, f x = 0 ↔ g x = 0) (p₀ a : E)
    (hp₀ : f p₀ = 0) (ha : f a ≠ 0) (x : E) : g x = g a / f a * f x := by
  set z : E := (f x / f a) • (p₀ - a) + x with hz
  have hlin : ∀ φ : E →ᵃ[ℝ] ℝ, φ z = φ x + f x / f a * (φ p₀ - φ a) := by
    intro φ
    have h1 : φ z = φ.linear ((f x / f a) • (p₀ - a)) + φ x := φ.map_vadd x _
    have h2 : φ.linear (p₀ - a) = φ p₀ - φ a := by
      have := φ.map_vadd a (p₀ - a)
      simp only [vadd_eq_add, sub_add_cancel] at this
      linarith
    rw [h1, map_smul, h2, smul_eq_mul]; ring
  have hfz : f z = 0 := by rw [hlin, hp₀]; field_simp; ring
  have hgz : g z = 0 := (h z).1 hfz
  have hgp : g p₀ = 0 := (h p₀).1 hp₀
  rw [hlin, hgp] at hgz
  field_simp at hgz ⊢
  linarith

end TouchingSimplices

end Simplex


section Perles

/-!
# Theorem 2 (Perles): `f(d) < 2^(d+1)`

We follow Perles' proof from the chapter.  For a touching configuration `P₁, …, P_r` of
`d`-simplices we enumerate the different facet hyperplanes `H₁, …, H_s`, choose a positive side
for each of them, and consider the sets `C_i` of all `±1`-vectors (here: `Bool`-vectors) indexed
by the hyperplanes that agree with the "B-matrix row" of `P_i` on the facet hyperplanes of `P_i`
(the zeros of that row being replaced arbitrarily).  These are the rows of the matrix `C`.
Each `C_i` has `2^(s-d-1)` elements, the `C_i` are pairwise disjoint (because touching simplices
lie on opposite sides of a common facet hyperplane), and the sign vector of a point outside all
the simplices lies in none of them.  Hence `r * 2^(s-d-1) < 2^s`.
-/


open Set Module Finset

namespace TouchingSimplices

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The value of a continuous linear functional, written in barycentric coordinates. -/
lemma functional_sub_eq_sum_coord {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ E)
    (f : StrongDual ℝ E) (u : ℝ) (x : E) :
    f x - u = ∑ i, b.coord i x * (f (b i) - u) := by
  have h1 := b.linear_combination_coord_eq_self x
  have h2 := b.sum_coord_apply_eq_one x
  have h3 : f x = ∑ i, b.coord i x * f (b i) := by
    conv_lhs => rw [← h1]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2, one_mul, h3]

omit [FiniteDimensional ℝ E] in
/-- A point all of whose barycentric coordinates outside `t` vanish lies in the affine span
of the vertices indexed by `t`. -/
lemma mem_affineSpan_of_coord_eq_zero {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ E)
    (t : Set ι) (x : E) (hx : ∀ i ∉ t, b.coord i x = 0) : x ∈ affineSpan ℝ (b '' t) := by
  rw [← b.affineCombination_coord_eq_self x]
  exact affineCombination_mem_affineSpan_image (b.sum_coord_apply_eq_one x)
    (fun i _ hi => hx i hi) b

/-- **Face lemma.** Let `P` be a `d`-simplex in a `d`-dimensional space, lying in the closed
half-space `f ≤ u` but not inside the hyperplane `f = u`.  If the hyperplane `f = u` meets `P` in
a `(d-1)`-dimensional set, then it is the hyperplane spanned by a facet of `P`: the affine
function `f - u` is a negative multiple of one of the barycentric coordinates of `P`. -/
lemma face_lemma {d : ℕ} (b : AffineBasis (Fin (d + 1)) ℝ E) (f : StrongDual ℝ E) (u : ℝ)
    (hle : ∀ x ∈ convexHull ℝ (range b), f x ≤ u) (c : E) (hc : f c < u)
    (S : Set E) (hS : S ⊆ convexHull ℝ (range b)) (hSf : ∀ x ∈ S, f x = u) (hSne : S.Nonempty)
    (hSdim : finrank ℝ (vectorSpan ℝ S) + 1 = d) :
    ∃ k : Fin (d + 1), ∃ a : ℝ, a < 0 ∧ ∀ x, f x - u = a * b.coord k x := by
  classical
  have hv : ∀ i, f (b i) ≤ u := fun i => hle _ (subset_convexHull ℝ _ (mem_range_self i))
  set J : Finset (Fin (d + 1)) := univ.filter fun i => f (b i) < u with hJ
  -- `J` is nonempty
  have hJne : J.Nonempty := by
    by_contra hJe
    rw [Finset.not_nonempty_iff_eq_empty] at hJe
    have : f c - u = 0 := by
      rw [functional_sub_eq_sum_coord b f u c]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : ¬ f (b i) < u := by
        intro h; have : i ∈ J := by simp [hJ, h]
        simp [hJe] at this
      have : f (b i) = u := le_antisymm (hv i) (not_lt.1 this)
      simp [this]
    linarith
  -- every point of `S` has vanishing coordinates in `J`
  have hzero : ∀ x ∈ S, ∀ i ∈ J, b.coord i x = 0 := by
    intro x hx i hi
    have hxP := hS hx
    rw [b.convexHull_eq_nonneg_coord] at hxP
    have hsum : ∑ j, b.coord j x * (f (b j) - u) = 0 := by
      rw [← functional_sub_eq_sum_coord, hSf x hx, sub_self]
    have hnp : ∀ j ∈ (univ : Finset (Fin (d + 1))), b.coord j x * (f (b j) - u) ≤ 0 :=
      fun j _ => mul_nonpos_of_nonneg_of_nonpos (hxP j) (by linarith [hv j])
    have := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hsum i (mem_univ i)
    have hneg : f (b i) - u < 0 := by
      have := (Finset.mem_filter.1 hi).2; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hneg.ne
  -- hence `J` has at most one element
  have hJcard : J.card ≤ 1 := by
    have hsub : S ⊆ affineSpan ℝ (b '' ((Jᶜ : Finset (Fin (d + 1))) : Set (Fin (d + 1)))) := by
      intro x hx
      refine mem_affineSpan_of_coord_eq_zero b _ x fun i hi => hzero x hx i ?_
      simpa using hi
    have hvs : vectorSpan ℝ S ≤
        vectorSpan ℝ (((Jᶜ).image b : Finset E) : Set E) := by
      rw [Finset.coe_image, ← direction_affineSpan (k := ℝ) (s := b '' _)]
      exact vectorSpan_mono ℝ hsub
    have hcc : (Jᶜ).card = d + 1 - J.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    rcases Nat.eq_zero_or_eq_succ_pred (Jᶜ).card with h0 | hm
    · exfalso
      rw [Finset.card_eq_zero] at h0
      obtain ⟨x, hx⟩ := hSne
      have := hsub hx
      simp [h0] at this
    · have := finrank_vectorSpan_image_finset_le (k := ℝ) b (Jᶜ) hm
      have h2 := Submodule.finrank_mono hvs
      omega
  obtain ⟨k, hk⟩ : ∃ k, J = {k} := by
    rw [← Finset.card_eq_one]
    have := hJne.card_pos
    omega
  refine ⟨k, f (b k) - u, ?_, fun x => ?_⟩
  · have : k ∈ J := by simp [hk]
    have := (Finset.mem_filter.1 this).2; linarith
  · rw [functional_sub_eq_sum_coord b f u x, Finset.sum_eq_single k]
    · ring
    · intro j _ hjk
      have : j ∉ J := by simp [hk, hjk]
      have : f (b j) = u := le_antisymm (hv j) (by simpa [hJ] using this)
      simp [this]
    · simp

/-- **Touching simplices share a facet hyperplane and lie on opposite sides of it.**
If two `d`-simplices in a `d`-dimensional space touch, then some barycentric coordinate of the
second one is a negative multiple of some barycentric coordinate of the first one. -/
lemma exists_opposite_facet {d : ℕ} (hE : finrank ℝ E = d)
    (b₁ b₂ : AffineBasis (Fin (d + 1)) ℝ E)
    (h : Touching d (convexHull ℝ (range b₁)) (convexHull ℝ (range b₂))) :
    ∃ k₁ k₂ : Fin (d + 1), ∃ c : ℝ, c < 0 ∧ ∀ x, b₂.coord k₂ x = c * b₁.coord k₁ x := by
  set P := convexHull ℝ (range b₁)
  set Q := convexHull ℝ (range b₂)
  obtain ⟨hne, hdim⟩ := h
  have hPi : (interior P).Nonempty := ⟨_, b₁.centroid_mem_interior_convexHull⟩
  have hQi : (interior Q).Nonempty := ⟨_, b₂.centroid_mem_interior_convexHull⟩
  -- the interiors are disjoint, otherwise `P ∩ Q` would be `d`-dimensional
  have hdisj : Disjoint (interior P) (interior Q) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hc
    have hopen : IsOpen (interior P ∩ interior Q) := isOpen_interior.inter isOpen_interior
    have htop := hopen.affineSpan_eq_top (Set.nonempty_iff_ne_empty.2 hc)
    have htop' : affineSpan ℝ (P ∩ Q) = ⊤ :=
      top_unique (htop ▸ affineSpan_mono ℝ
        (Set.inter_subset_inter interior_subset interior_subset))
    have : vectorSpan ℝ (P ∩ Q) = ⊤ := by
      rw [← direction_affineSpan, htop', AffineSubspace.direction_top]
    rw [this, finrank_top, hE] at hdim
    omega
  obtain ⟨f, u, hfP, hfQ⟩ := geometric_hahn_banach_open_open (convex_convexHull ℝ _).interior
    isOpen_interior (convex_convexHull ℝ _).interior isOpen_interior hdisj
  have hclP : P ⊆ closure (interior P) := by
    rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hPi]
    exact subset_closure
  have hclQ : Q ⊆ closure (interior Q) := by
    rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hQi]
    exact subset_closure
  have hleP : ∀ x ∈ P, f x ≤ u := by
    intro x hx
    have : closure (interior P) ⊆ {y | f y ≤ u} :=
      closure_minimal (fun y hy => (hfP y hy).le) (isClosed_le f.continuous continuous_const)
    exact this (hclP hx)
  have hgeQ : ∀ x ∈ Q, u ≤ f x := by
    intro x hx
    have : closure (interior Q) ⊆ {y | u ≤ f y} :=
      closure_minimal (fun y hy => (hfQ y hy).le) (isClosed_le continuous_const f.continuous)
    exact this (hclQ hx)
  have hSf : ∀ x ∈ P ∩ Q, f x = u := fun x hx => le_antisymm (hleP x hx.1) (hgeQ x hx.2)
  obtain ⟨c₁, hc₁⟩ := hPi
  obtain ⟨c₂, hc₂⟩ := hQi
  obtain ⟨k₁, a₁, ha₁, h₁⟩ := face_lemma b₁ f u hleP c₁ (hfP c₁ hc₁) (P ∩ Q)
    Set.inter_subset_left hSf hne hdim
  obtain ⟨k₂, a₂, ha₂, h₂⟩ := face_lemma b₂ (-f) (-u) (fun x hx => by simpa using hgeQ x hx)
    c₂ (by simpa using hfQ c₂ hc₂) (P ∩ Q) Set.inter_subset_right
    (fun x hx => by simp [hSf x hx]) hne hdim
  refine ⟨k₁, k₂, -a₁ / a₂, ?_, fun x => ?_⟩
  · have : 0 < a₁ / a₂ := div_pos_of_neg_of_neg ha₁ ha₂
    rw [neg_div]; linarith
  · have e1 := h₁ x
    have e2 := h₂ x
    rw [show (-f) x = -(f x) from rfl] at e2
    have h3 : a₂ * b₂.coord k₂ x = -a₁ * b₁.coord k₁ x := by linarith
    have ha₂' : a₂ ≠ 0 := ha₂.ne
    field_simp
    linarith [h3]

end Geometry

section Counting

/-- The number of `Bool`-vectors with prescribed values on a set `T` of coordinates. -/
lemma card_filter_agree {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (τ : α → Bool) :
    (univ.filter fun σ : α → Bool => ∀ a ∈ T, σ a = τ a).card =
      2 ^ (Fintype.card α - T.card) := by
  have : (univ.filter fun σ : α → Bool => ∀ a ∈ T, σ a = τ a) =
      Fintype.piFinset fun a => if a ∈ T then {τ a} else univ := by
    ext σ
    simp only [mem_filter, Fintype.mem_piFinset]
    constructor
    · intro h a
      split_ifs with ha
      · simp [h.2 a ha]
      · simp
    · intro h
      refine ⟨mem_univ _, fun a ha => ?_⟩
      simpa [ha] using h a
  rw [this, Fintype.card_piFinset]
  have : ∀ a, (if a ∈ T then ({τ a} : Finset Bool) else univ).card = if a ∈ T then 1 else 2 := by
    intro a; split_ifs <;> simp
  simp only [this, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

end Counting

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- In a nontrivial finite-dimensional space, finitely many simplices never cover everything. -/
lemma exists_not_mem_simplices [Nontrivial E] {d r : ℕ}
    (b : Fin r → AffineBasis (Fin (d + 1)) ℝ E) :
    ∃ x : E, ∀ i, x ∉ convexHull ℝ (range (b i)) := by
  by_contra h
  push Not at h
  have hcpt : IsCompact (⋃ i, convexHull ℝ (range (b i))) :=
    isCompact_iUnion fun i => by
      show IsCompact (convexHull ℝ (range (b i)))
      exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range _)
  have : (⋃ i, convexHull ℝ (range (b i))) = Set.univ :=
    eq_univ_of_forall fun x => by obtain ⟨i, hi⟩ := h x; exact mem_iUnion.2 ⟨i, hi⟩
  rw [this] at hcpt
  exact noncompact_univ E hcpt

/-- **Theorem 2 (Perles)**, in an arbitrary `d`-dimensional real normed space:
a touching family of `r` `d`-simplices satisfies `r < 2^(d+1)`. -/
theorem card_lt_of_isTouchingFamily {d : ℕ} (hd : 1 ≤ d) (hE : finrank ℝ E = d) {r : ℕ}
    (P : Fin r → Set E) (hP : IsTouchingFamily d P) : r < 2 ^ (d + 1) := by
  classical
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · rw [hr]; positivity
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- the simplices `P i` are spanned by affine bases `b i`
  choose b hb using fun i => (hP.1 i).exists_affineBasis hE
  -- the facet hyperplanes of `P i` are the zero sets of the barycentric coordinates
  set Hyp : Fin r → Fin (d + 1) → Set E := fun i k => {x | (b i).coord k x = 0} with hHyp
  -- the different hyperplanes `H₁, …, H_s`
  set S : Finset (Set E) := univ.image (fun p : Fin r × Fin (d + 1) => Hyp p.1 p.2) with hS
  have hmem : ∀ i k, Hyp i k ∈ S := fun i k => mem_image.2 ⟨(i, k), mem_univ _, rfl⟩
  have hrep : ∀ H ∈ S, ∃ p : Fin r × Fin (d + 1), Hyp p.1 p.2 = H := by
    intro H hH
    obtain ⟨p, -, hp⟩ := mem_image.1 hH
    exact ⟨p, hp⟩
  choose! rep hrep' using hrep
  -- an affine functional `g H` defining each hyperplane: its positive side is `H⁺`
  set g : Set E → E → ℝ := fun H x => (b (rep H).1).coord (rep H).2 x with hg
  have hprop : ∀ i k, ∃ a : ℝ, a ≠ 0 ∧ ∀ x, g (Hyp i k) x = a * (b i).coord k x := by
    intro i k
    have hp := hrep' _ (hmem i k)
    set i' := (rep (Hyp i k)).1
    set k' := (rep (Hyp i k)).2
    have hiff : ∀ x, (b i).coord k x = 0 ↔ (b i').coord k' x = 0 := by
      intro x
      have := congrArg (fun H : Set E => x ∈ H) hp
      simp only [hHyp, mem_setOf_iff'] at this
      exact this.symm.to_iff
    obtain ⟨j, hj⟩ := exists_ne k
    have key := affineMap_eq_mul_of_zero_iff ((b i).coord k) ((b i').coord k') hiff
      ((b i) j) ((b i) k) ((b i).coord_apply_ne hj.symm) (by simp [(b i).coord_apply_eq k])
    refine ⟨(b i').coord k' ((b i) k), ?_, fun x => ?_⟩
    · intro h0
      have := key ((b i') k')
      rw [h0, (b i').coord_apply_eq] at this
      simp at this
    · have := key x
      rw [(b i).coord_apply_eq, div_one] at this
      exact this
  -- interior points `c i` of the simplices
  set c : Fin r → E := fun i => univ.centroid ℝ (b i) with hc
  have hcpos : ∀ i k, 0 < (b i).coord k (c i) := by
    intro i k
    rw [hc]; dsimp only
    rw [(b i).coord_apply_centroid (mem_univ k)]
    positivity
  -- the rows of the matrix `C` coming from the `i`-th row of `B`
  let τ : Fin r → S → Bool := fun i H => decide (0 < g H.1 (c i))
  let T : Fin r → Finset S := fun i => univ.image fun k => (⟨Hyp i k, hmem i k⟩ : S)
  let C : Fin r → Finset (S → Bool) := fun i => univ.filter fun σ => ∀ H ∈ T i, σ H = τ i H
  -- every row of `B` has exactly `d + 1` nonzero entries
  have hTcard : ∀ i, (T i).card = d + 1 := by
    intro i
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro k k' hkk'
    have h1 : Hyp i k = Hyp i k' := congrArg Subtype.val hkk'
    by_contra hne
    have : (b i) k' ∈ Hyp i k := by
      simp [hHyp, (b i).coord_apply_ne hne]
    rw [h1] at this
    simp [hHyp, (b i).coord_apply_eq] at this
  have hCcard : ∀ i, (C i).card = 2 ^ (S.card - (d + 1)) := by
    intro i
    rw [card_filter_agree, hTcard, Fintype.card_coe]
  -- the rows of `C` are all different
  have hdisj : ((univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint C := by
    intro i _ j _ hij
    have htouch : Touching d (P i) (P j) := hP.2 hij
    rw [hb i, hb j] at htouch
    obtain ⟨k₁, k₂, γ, hγ, hγeq⟩ := exists_opposite_facet hE (b i) (b j) htouch
    have hH : Hyp j k₂ = Hyp i k₁ := by
      ext x
      simp only [hHyp, mem_setOf_iff', hγeq x, mul_eq_zero, hγ.ne, false_or]
    obtain ⟨a, ha, hga⟩ := hprop i k₁
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσi hσj
    have hi := (mem_filter.1 hσi).2 ⟨Hyp i k₁, hmem i k₁⟩
      (mem_image.2 ⟨k₁, mem_univ _, rfl⟩)
    have hj := (mem_filter.1 hσj).2 ⟨Hyp i k₁, hmem i k₁⟩
      (mem_image.2 ⟨k₂, mem_univ _, Subtype.ext hH⟩)
    rw [hi] at hj
    simp only [τ, hga] at hj
    have p1 := hcpos i k₁
    have p2 := hcpos j k₂
    have hq : (b i).coord k₁ (c j) < 0 := by
      have := hγeq (c j)
      by_contra hq; push Not at hq
      nlinarith
    rcases lt_or_gt_of_ne ha with ha' | ha'
    · have e1 : ¬ (0 < a * (b i).coord k₁ (c i)) := by nlinarith
      have e2 : 0 < a * (b i).coord k₁ (c j) := by nlinarith
      simp [e1, e2] at hj
    · have e1 : 0 < a * (b i).coord k₁ (c i) := by nlinarith
      have e2 : ¬ (0 < a * (b i).coord k₁ (c j)) := by nlinarith
      simp [e1, e2] at hj
  -- a point outside all simplices yields a sign vector which is not a row of `C`
  obtain ⟨x, hx⟩ := exists_not_mem_simplices b
  let σx : S → Bool := fun H => decide (0 < g H.1 x)
  have hσx : ∀ i, σx ∉ C i := by
    intro i hσ
    apply hx i
    rw [(b i).convexHull_eq_nonneg_coord]
    intro k
    have h := (mem_filter.1 hσ).2 ⟨Hyp i k, hmem i k⟩ (mem_image.2 ⟨k, mem_univ _, rfl⟩)
    obtain ⟨a, ha, hga⟩ := hprop i k
    simp only [σx, τ, hga] at h
    have p1 := hcpos i k
    by_contra hneg; push Not at hneg
    rcases lt_or_gt_of_ne ha with ha' | ha'
    · have e1 : 0 < a * (b i).coord k x := by nlinarith
      have e2 : ¬ (0 < a * (b i).coord k (c i)) := by nlinarith
      simp [e1, e2] at h
    · have e1 : ¬ (0 < a * (b i).coord k x) := by nlinarith
      have e2 : 0 < a * (b i).coord k (c i) := by nlinarith
      simp [e1, e2] at h
  -- counting
  have hsub : univ.biUnion C ⊆ univ.erase σx := by
    intro σ hσ
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hσ
    exact mem_erase.2 ⟨fun h => hσx i (h ▸ hi), mem_univ _⟩
  have hcount := Finset.card_le_card hsub
  rw [card_biUnion hdisj, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe] at hcount
  simp only [hCcard, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hcount
  have hs : d + 1 ≤ S.card := by
    have := card_le_univ (T ⟨0, hr⟩)
    rw [hTcard, Fintype.card_coe] at this
    exact this
  by_contra hcon
  push Not at hcon
  have h2 : 2 ^ S.card = 2 ^ (d + 1) * 2 ^ (S.card - (d + 1)) := by
    rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ (d + 1) * 2 ^ (S.card - (d + 1)) ≤ r * 2 ^ (S.card - (d + 1)) :=
    Nat.mul_le_mul_right _ hcon
  have h4 : 0 < 2 ^ S.card := by positivity
  omega

end Main

end TouchingSimplices

end Perles


section Pyramid

/-!
# Pyramids over sets in a hyperplane

For the induction step of Theorem 1 we embed `E` as the hyperplane `{0} × E` of `ℝ × E` and
form the pyramid `conv (A ∪ {apex})` with apex `(c, 0)`, `c ≠ 0`
(in the book: `conv (P_i ∪ {± e_{d+1}})`).
-/


open Set Module

namespace TouchingSimplices

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The pyramid over `A ⊆ E ≅ {0} × E` with apex `(c, 0)`. -/
def pyr (c : ℝ) (A : Set E) : Set (ℝ × E) :=
  convexHull ℝ (insert ((c, 0) : ℝ × E) ((fun x => ((0 : ℝ), x)) '' A))

lemma image_inr_eq (A : Set E) :
    (fun x => ((0 : ℝ), x)) '' A = (LinearMap.inr ℝ ℝ E) '' A := rfl

lemma apex_mem_pyr (c : ℝ) (A : Set E) : ((c, 0) : ℝ × E) ∈ pyr c A :=
  subset_convexHull ℝ _ (mem_insert _ _)

lemma base_mem_pyr (c : ℝ) {A : Set E} {x : E} (hx : x ∈ A) : ((0 : ℝ), x) ∈ pyr c A :=
  subset_convexHull ℝ _ (mem_insert_of_mem _ ⟨x, hx, rfl⟩)

lemma pyr_mono (c : ℝ) {A B : Set E} (h : A ⊆ B) : pyr c A ⊆ pyr c B :=
  convexHull_mono (insert_subset_insert (image_mono h))

/-- Points of the pyramid over a convex set. -/
lemma mem_pyr_iff {c : ℝ} {A : Set E} (hA : Convex ℝ A) (hne : A.Nonempty) (z : ℝ × E) :
    z ∈ pyr c A ↔ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ ∃ x ∈ A, z = (s * c, t • x) := by
  have hconv : convexHull ℝ ((fun x => ((0 : ℝ), x)) '' A) = (fun x => ((0 : ℝ), x)) '' A := by
    rw [image_inr_eq, ← LinearMap.image_convexHull, hA.convexHull_eq]
  rw [pyr, convexHull_insert (hne.image _), hconv, mem_convexJoin]
  constructor
  · rintro ⟨a, ha, b, ⟨x, hx, rfl⟩, s, t, hs, ht, hst, rfl⟩
    rw [mem_singleton_iff] at ha
    subst ha
    exact ⟨s, t, hs, ht, hst, x, hx, by ext <;> simp⟩
  · rintro ⟨s, t, hs, ht, hst, x, hx, rfl⟩
    exact ⟨_, rfl, _, ⟨x, hx, rfl⟩, s, t, hs, ht, hst, by ext <;> simp⟩

lemma convex_pyr (c : ℝ) (A : Set E) : Convex ℝ (pyr c A) := convex_convexHull ℝ _

/-- Two pyramids with the same apex intersect in the pyramid over the intersection. -/
lemma pyr_inter_pyr {c : ℝ} (hc : c ≠ 0) {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) : pyr c A ∩ pyr c B = pyr c (A ∩ B) := by
  refine Subset.antisymm ?_ (subset_inter (pyr_mono c inter_subset_left)
    (pyr_mono c inter_subset_right))
  rintro z ⟨hzA, hzB⟩
  obtain ⟨s, t, hs, ht, hst, x, hx, rfl⟩ := (mem_pyr_iff hA hAne z).1 hzA
  obtain ⟨s', t', hs', ht', hst', y, hy, hxy⟩ := (mem_pyr_iff hB hBne _).1 hzB
  simp only [Prod.mk.injEq] at hxy
  have hss : s = s' := mul_right_cancel₀ hc hxy.1
  have htt : t = t' := by linarith
  subst hss htt
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have : s = 1 := by linarith
    subst this
    simpa using apex_mem_pyr c (A ∩ B)
  · have hxy' : x = y := smul_right_injective E hpos.ne' hxy.2
    subst hxy'
    have h1 := apex_mem_pyr c (A ∩ B)
    have hxAB : x ∈ A ∩ B := ⟨hx, hy⟩
    have h2 := base_mem_pyr c hxAB
    have := convex_pyr c (A ∩ B) h1 h2 hs ht hst
    convert this using 1
    ext <;> simp

/-- Two pyramids with apexes on opposite sides of the hyperplane intersect in the intersection
of their bases. -/
lemma pyr_inter_pyr_opposite {c₁ c₂ : ℝ} (hc₁ : c₁ < 0) (hc₂ : 0 < c₂) {A B : Set E}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    pyr c₁ A ∩ pyr c₂ B = (fun x => ((0 : ℝ), x)) '' (A ∩ B) := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨hzA, hzB⟩
    obtain ⟨s, t, hs, ht, hst, x, hx, rfl⟩ := (mem_pyr_iff hA hAne z).1 hzA
    obtain ⟨s', t', hs', ht', hst', y, hy, hxy⟩ := (mem_pyr_iff hB hBne _).1 hzB
    simp only [Prod.mk.injEq] at hxy
    have h1 : s * c₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hc₁.le
    have h2 : 0 ≤ s' * c₂ := mul_nonneg hs' hc₂.le
    have hs0 : s = 0 := by
      by_contra hne
      have : s * c₁ < 0 := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs (Ne.symm hne)) hc₁
      linarith
    have hs0' : s' = 0 := by
      by_contra hne
      have : 0 < s' * c₂ := mul_pos (lt_of_le_of_ne hs' (Ne.symm hne)) hc₂
      linarith
    have ht1 : t = 1 := by linarith
    have ht1' : t' = 1 := by linarith
    subst hs0 ht1 hs0' ht1'
    obtain ⟨-, hxy⟩ := hxy
    simp only [one_smul] at hxy
    subst hxy
    exact ⟨x, ⟨hx, hy⟩, by simp⟩
  · rintro z ⟨x, ⟨hxA, hxB⟩, rfl⟩
    exact ⟨base_mem_pyr c₁ hxA, base_mem_pyr c₂ hxB⟩

/-- The embedding `E → ℝ × E` preserves the dimension of affine spans. -/
lemma finrank_vectorSpan_inr (S : Set E) :
    finrank ℝ (vectorSpan ℝ ((fun x => ((0 : ℝ), x)) '' S)) = finrank ℝ (vectorSpan ℝ S) := by
  have h := AffineMap.map_vectorSpan (LinearMap.inr ℝ ℝ E).toAffineMap (s := S)
  change Submodule.map (LinearMap.inr ℝ ℝ E) (vectorSpan ℝ S) = _ at h
  rw [image_inr_eq, ← LinearMap.coe_toAffineMap, ← h]
  exact ((Submodule.equivMapOfInjective _ LinearMap.inr_injective _).finrank_eq).symm

/-- The dimension of a pyramid is one more than the dimension of its base. -/
lemma finrank_vectorSpan_pyr [FiniteDimensional ℝ E] {c : ℝ} (hc : c ≠ 0) {S : Set E}
    (hS : S.Nonempty) :
    finrank ℝ (vectorSpan ℝ (pyr c S)) = finrank ℝ (vectorSpan ℝ S) + 1 := by
  obtain ⟨x₀, hx₀⟩ := hS
  set T : Set (ℝ × E) := (fun x => ((0 : ℝ), x)) '' S
  have hp₁ : ((0 : ℝ), x₀) ∈ affineSpan ℝ T := subset_affineSpan ℝ _ ⟨x₀, hx₀, rfl⟩
  have hdir : vectorSpan ℝ (pyr c S) =
      Submodule.span ℝ {((c, 0) : ℝ × E) -ᵥ ((0 : ℝ), x₀)} ⊔ vectorSpan ℝ T := by
    rw [pyr, ← direction_affineSpan, affineSpan_convexHull, ← affineSpan_insert_affineSpan,
      AffineSubspace.direction_affineSpan_insert hp₁, direction_affineSpan]
  set u : ℝ × E := ((c, 0) : ℝ × E) -ᵥ ((0 : ℝ), x₀)
  have hu : u = (c, -x₀) := by simp [u]
  have hTfst : ∀ w ∈ vectorSpan ℝ T, w.1 = 0 := by
    intro w hw
    have hle : vectorSpan ℝ T ≤ LinearMap.ker (LinearMap.fst ℝ ℝ E) := by
      rw [vectorSpan_def]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨a, -, rfl⟩, _, ⟨b, -, rfl⟩, rfl⟩
      simp
    simpa using hle hw
  have hdisj : Submodule.span ℝ {u} ⊓ vectorSpan ℝ T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw1
    have := hTfst _ hw2
    rw [hu] at this
    simp only [Prod.smul_fst, smul_eq_mul, mul_eq_zero, hc, or_false] at this
    simp [this]
  have hu0 : u ≠ 0 := by
    rw [hu]; intro h; exact hc (congrArg Prod.fst h)
  have key := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ {u}) (vectorSpan ℝ T)
  rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hu0] at key
  rw [hdir, key, finrank_vectorSpan_inr]
  ring

/-- Affine independence of the vertices of a pyramid. -/
lemma affineIndependent_cons_apex {n : ℕ} {c : ℝ} (hc : c ≠ 0) {v : Fin (n + 1) → E}
    (hv : AffineIndependent ℝ v) :
    AffineIndependent ℝ (Fin.cons ((c, 0) : ℝ × E) (fun i => ((0 : ℝ), v i)) :
      Fin (n + 2) → ℝ × E) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
  rw [Fin.sum_univ_succ] at hw hs
  simp only [Fin.cons_zero, Fin.cons_succ] at hs
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_sum, mul_zero,
    Finset.sum_const_zero, add_zero, Prod.fst_zero, mul_eq_zero, hc, or_false] at h1
  simp only [Prod.snd_add, Prod.smul_snd, smul_zero, Prod.snd_sum, zero_add,
    Prod.snd_zero] at h2
  rw [h1, zero_add] at hw
  have hrest := (affineIndependent_iff.1 hv) Finset.univ (fun i => w i.succ) hw h2
  intro i
  refine Fin.cases h1 (fun j => hrest j (Finset.mem_univ _)) i

/-- A pyramid over an `n`-simplex is an `(n+1)`-simplex. -/
lemma IsSimplex.pyr {n : ℕ} {A : Set E} (hA : IsSimplex n A) {c : ℝ} (hc : c ≠ 0) :
    IsSimplex (n + 1) (pyr c A) := by
  obtain ⟨v, hv, rfl⟩ := hA
  refine ⟨Fin.cons ((c, 0) : ℝ × E) (fun i => ((0 : ℝ), v i)), affineIndependent_cons_apex hc hv,
    ?_⟩
  rw [Fin.range_cons, TouchingSimplices.pyr, image_inr_eq, LinearMap.image_convexHull,
    insert_eq, insert_eq,
    convexHull_convexHull_union_right, ← range_comp]
  rfl

/-- Touching simplices give touching pyramids (with a common apex). -/
lemma Touching.pyr [FiniteDimensional ℝ E] {n : ℕ} {A B : Set E} (h : Touching n A B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {c : ℝ} (hc : c ≠ 0) :
    Touching (n + 1) (TouchingSimplices.pyr c A) (TouchingSimplices.pyr c B) := by
  obtain ⟨hne, hdim⟩ := h
  rw [Touching, pyr_inter_pyr hc hA hB (hne.mono inter_subset_left)
    (hne.mono inter_subset_right), finrank_vectorSpan_pyr hc hne, hdim]
  exact ⟨⟨_, apex_mem_pyr c _⟩, rfl⟩

end TouchingSimplices

end Pyramid


section Lift

/-!
# Theorem 1 (Zaks): the induction step

Starting from a normalised configuration `Σ₁` in `ℝ^d` (each simplex containing a segment
`S¹(α) = {(α, x₂, 0, …, 0) : -1 ≤ x₂ ≤ 1}` in its interior, `-1 < α < 0`), we reflect it in the
hyperplane `x₁ = x₂` to obtain `Σ₂`, and form pyramids over the simplices of `Σ₁` with apex below
and over those of `Σ₂` with apex above.  The tilted antidiagonal `L_ε` is a transversal.
-/


open Set Module Filter Topology

namespace TouchingSimplices

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma Touching.symm {n : ℕ} {A B : Set E} (h : Touching n A B) : Touching n B A := by
  rw [Touching, inter_comm]; exact h

lemma IsTouchingFamily.comp_equiv {n : ℕ} {ι κ : Type*}
    {P : ι → Set E} (h : IsTouchingFamily n P) (φ : κ ≃ ι) : IsTouchingFamily n (P ∘ φ) :=
  ⟨fun k => h.1 (φ k), fun _ _ hkl => h.2 (φ.injective.ne hkl)⟩

lemma IsSimplex.convex {n : ℕ} {A : Set E} (h : IsSimplex n A) : Convex ℝ A := by
  obtain ⟨v, -, rfl⟩ := h; exact convex_convexHull ℝ _

end Algebraic

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
lemma mem_interior_image (e : E ≃ᵃ[ℝ] F) {A : Set E} {x : E} (hx : x ∈ interior A) :
    e x ∈ interior (e '' A) := by
  rw [← e.coe_toHomeomorphOfFiniteDimensional, ← Homeomorph.image_interior]
  exact mem_image_of_mem _ hx

omit [FiniteDimensional ℝ F] in
lemma IsTransversal.image {ι : Type*} {P : ι → Set E} {p v : E} (h : IsTransversal P p v)
    (e : E ≃ᵃ[ℝ] F) : IsTransversal (fun i => e '' P i) (e p) (e.linear v) := by
  refine ⟨fun h0 => h.1 (e.linear.injective (h0.trans (map_zero _).symm)), fun i => ?_⟩
  obtain ⟨t, ht⟩ := h.2 i
  refine ⟨t, ?_⟩
  have : e (p + t • v) = e p + t • e.linear v := by
    have h1 : p + t • v = t • v +ᵥ p := by rw [vadd_eq_add, add_comm]
    rw [h1, e.map_vadd, map_smul, vadd_eq_add, add_comm]
  rw [← this]
  exact mem_interior_image e ht

omit [FiniteDimensional ℝ E] in
/-- Pyramids over two `n`-dimensional convex sets whose interiors meet, with apexes on opposite
sides, touch. -/
lemma touching_pyr_opposite {n : ℕ} (hE : finrank ℝ E = n) {c₁ c₂ : ℝ} (hc₁ : c₁ < 0)
    (hc₂ : 0 < c₂) {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hint : (interior A ∩ interior B).Nonempty) :
    Touching (n + 1) (pyr c₁ A) (pyr c₂ B) := by
  obtain ⟨z, hzA, hzB⟩ := hint
  have hAne : A.Nonempty := ⟨z, interior_subset hzA⟩
  have hBne : B.Nonempty := ⟨z, interior_subset hzB⟩
  rw [Touching, pyr_inter_pyr_opposite hc₁ hc₂ hA hB hAne hBne, finrank_vectorSpan_inr]
  refine ⟨⟨_, z, ⟨interior_subset hzA, interior_subset hzB⟩, rfl⟩, ?_⟩
  have htop := (isOpen_interior.inter isOpen_interior).affineSpan_eq_top ⟨z, hzA, hzB⟩
  have htop' : affineSpan ℝ (A ∩ B) = ⊤ :=
    top_unique (htop ▸ affineSpan_mono ℝ (inter_subset_inter interior_subset interior_subset))
  have : vectorSpan ℝ (A ∩ B) = ⊤ := by
    rw [← direction_affineSpan, htop', AffineSubspace.direction_top]
  rw [this, finrank_top, hE]

omit [FiniteDimensional ℝ E] in
/-- An explicit open subset of the interior of a pyramid: the points strictly between the base
(interior) and the apex. -/
lemma mem_interior_pyr {c : ℝ} (hc : c ≠ 0) {A : Set E} (z : ℝ × E)
    (h1 : z.1 / c ∈ Ioo (0 : ℝ) 1) (h2 : (1 - z.1 / c)⁻¹ • z.2 ∈ interior A) :
    z ∈ interior (pyr c A) := by
  set U : Set (ℝ × E) := {w | w.1 / c ∈ Ioo (0 : ℝ) 1} ∩
    (fun w : ℝ × E => (1 - w.1 / c)⁻¹ • w.2) ⁻¹' interior A
  have hUopen : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ ?_ isOpen_interior
    · refine ContinuousOn.smul (ContinuousOn.inv₀ (by fun_prop) ?_) (by fun_prop)
      intro w hw
      have : w.1 / c < 1 := hw.2
      linarith
    · exact isOpen_Ioo.preimage (by fun_prop)
  have hUsub : U ⊆ pyr c A := by
    rintro w ⟨hw1, hw2⟩
    simp only [mem_setOf_iff', mem_Ioo] at hw1
    simp only [mem_preimage] at hw2
    set s := w.1 / c
    have ht : 0 < 1 - s := by linarith [hw1.2]
    have hb := base_mem_pyr c (interior_subset hw2)
    have ha := apex_mem_pyr c A
    have := convex_pyr c A ha hb hw1.1.le ht.le (by ring)
    convert this using 1
    ext
    · simp [s, div_mul_cancel₀ _ hc]
    · simp [smul_smul, mul_inv_cancel₀ ht.ne']
  exact interior_maximal hUsub hUopen ⟨h1, h2⟩

omit [FiniteDimensional ℝ E] in
lemma eventually_inv_smul_mem {U : Set E} (hU : IsOpen U) {w : E} (hw : w ∈ U) (a : ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + a * ε)⁻¹ • w ∈ U := by
  have hcont : ContinuousAt (fun ε : ℝ => (1 + a * ε)⁻¹ • w) 0 :=
    ContinuousAt.smul (ContinuousAt.inv₀ (by fun_prop) (by simp)) continuousAt_const
  have := hcont.eventually (hU.mem_nhds (by simpa using hw))
  exact this

end Generic

/-! ### The configurations in `ℝ^d` -/

/-- The point `(a, b, 0, …, 0)ᵀ ∈ ℝ^d`. -/
def pt2 {d : ℕ} (a b : ℝ) : Fin d → ℝ :=
  fun k => if k.val = 0 then a else if k.val = 1 then b else 0

/-- A touching family of `2^d` simplices in `ℝ^d` with a transversal line. -/
def TransversalFamily (d : ℕ) : Prop :=
  ∃ P : Fin (2 ^ d) → Set (Fin d → ℝ), IsTouchingFamily d P ∧ ∃ p v, IsTransversal P p v

/-- A touching family of `2^d` simplices in `ℝ^d` in normal position: each simplex contains a
segment `S¹(α) = {(α, x₂, 0, …, 0) : -1 ≤ x₂ ≤ 1}` in its interior, with `-1 < α < 0`. -/
def NormalizedFamily (d : ℕ) : Prop :=
  ∃ P : Fin (2 ^ d) → Set (Fin d → ℝ), IsTouchingFamily d P ∧ ∃ α : Fin (2 ^ d) → ℝ,
    ∀ i, α i ∈ Ioo (-1 : ℝ) 0 ∧ ∀ x ∈ Icc (-1 : ℝ) 1, pt2 (α i) x ∈ interior (P i)

lemma neg_pt2 {d : ℕ} (a b : ℝ) : -(pt2 a b : Fin d → ℝ) = pt2 (-a) (-b) := by
  ext k; simp only [pt2, Pi.neg_apply]; split_ifs <;> ring

lemma smul_pt2 {d : ℕ} (t a b : ℝ) : t • (pt2 a b : Fin d → ℝ) = pt2 (t * a) (t * b) := by
  ext k; simp only [pt2, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- The reflection in the hyperplane `x₁ = x₂`. -/
def swap01 {d : ℕ} (hd : 2 ≤ d) : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)

lemma swap01_pt2 {d : ℕ} (hd : 2 ≤ d) (a b : ℝ) : swap01 hd (pt2 a b) = pt2 b a := by
  ext k
  simp only [swap01, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, pt2]
  rcases k with ⟨k, hk⟩
  by_cases h0 : k = 0
  · subst h0
    rw [Equiv.swap_apply_left]; simp
  by_cases h1 : k = 1
  · subst h1
    rw [Equiv.swap_apply_right]; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff, h0]) (by simp [Fin.ext_iff, h1])]
    simp [h0, h1]

/-- **Induction step of Theorem 1.** -/
theorem lift_step {d : ℕ} (hd : 2 ≤ d) (h : NormalizedFamily d) : TransversalFamily (d + 1) := by
  obtain ⟨P, hP, α, hα⟩ := h
  set σ := swap01 hd
  set Q : Fin (2 ^ d) → Set (Fin d → ℝ) := fun j => σ '' P j with hQdef
  have hQ : IsTouchingFamily d Q := hP.image σ.toAffineEquiv
  have hQint : ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1, pt2 x (α j) ∈ interior (Q j) := by
    intro j x hx
    have := mem_interior_image σ.toAffineEquiv ((hα j).2 x hx)
    simpa [σ, swap01_pt2] using this
  have hPc : ∀ i, Convex ℝ (P i) := fun i => IsSimplex.convex (hP.1 i)
  have hQc : ∀ i, Convex ℝ (Q i) := fun i => IsSimplex.convex (hQ.1 i)
  have hE : finrank ℝ (Fin d → ℝ) = d := by simp
  -- the new configuration `Σ` in `ℝ × ℝ^d`
  let R : Fin (2 ^ d) ⊕ Fin (2 ^ d) → Set (ℝ × (Fin d → ℝ)) :=
    Sum.elim (fun i => pyr (-1) (P i)) (fun j => pyr 1 (Q j))
  have hcross : ∀ i j, Touching (d + 1) (pyr (-1) (P i)) (pyr 1 (Q j)) := by
    intro i j
    refine touching_pyr_opposite hE (by norm_num) (by norm_num) (hPc i) (hQc j) ?_
    exact ⟨pt2 (α i) (α j), (hα i).2 _ ⟨(hα j).1.1.le, by linarith [(hα j).1.2]⟩,
      hQint j _ ⟨(hα i).1.1.le, by linarith [(hα i).1.2]⟩⟩
  have hR : IsTouchingFamily (d + 1) R := by
    refine ⟨?_, ?_⟩
    · rintro (i | j)
      · exact (hP.1 i).pyr (by norm_num)
      · exact (hQ.1 j).pyr (by norm_num)
    · rintro (i | i) (j | j) hij
      · exact (hP.2 (fun h => hij (congrArg _ h))).pyr (hPc i) (hPc j) (by norm_num)
      · exact hcross i j
      · exact Touching.symm (hcross j i)
      · exact (hQ.2 (fun h => hij (congrArg _ h))).pyr (hQc i) (hQc j) (by norm_num)
  -- the tilted antidiagonal `L_ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (∀ i, (1 + α i * ε)⁻¹ • pt2 (α i) (-α i) ∈ interior (P i)) ∧
      (∀ j, (1 + α j * ε)⁻¹ • pt2 (-α j) (α j) ∈ interior (Q j)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun j => ?_)
    · exact eventually_inv_smul_mem isOpen_interior
        ((hα i).2 _ ⟨by linarith [(hα i).1.2], by linarith [(hα i).1.1]⟩) _
    · exact eventually_inv_smul_mem isOpen_interior
        (hQint j _ ⟨by linarith [(hα j).1.2], by linarith [(hα j).1.1]⟩) _
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  set ε : ℝ := min (δ / 2) (1 / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεδ : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨hεP, hεQ⟩ := hδP hεδ
  set v : ℝ × (Fin d → ℝ) := (ε, pt2 1 (-1))
  have hRt : IsTransversal R 0 v := by
    refine ⟨fun h0 => hε0.ne' (congrArg Prod.fst h0), ?_⟩
    rintro (i | j)
    · refine ⟨α i, mem_interior_pyr (by norm_num) _ ?_ ?_⟩
      · have h1 := (hα i).1
        simp only [v, zero_add, Prod.smul_fst, smul_eq_mul, mem_Ioo]
        constructor <;> nlinarith [h1.1, h1.2]
      · have := hεP i
        convert this using 2
        · simp [v]; ring
        · simp [v, smul_pt2]
    · refine ⟨-α j, mem_interior_pyr (by norm_num) _ ?_ ?_⟩
      · have h1 := (hα j).1
        simp only [v, zero_add, Prod.smul_fst, smul_eq_mul, mem_Ioo, div_one]
        constructor <;> nlinarith [h1.1, h1.2]
      · have := hεQ j
        convert this using 2
        · simp [v]
        · simp [v, smul_pt2, neg_pt2]
  -- transport to `ℝ^(d+1)` and reindex
  let e : (ℝ × (Fin d → ℝ)) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) := Fin.consLinearEquiv ℝ (fun _ => ℝ)
  let φ : Fin (2 ^ (d + 1)) ≃ Fin (2 ^ d) ⊕ Fin (2 ^ d) :=
    (finCongr (by ring)).trans finSumFinEquiv.symm
  refine ⟨(fun k => e.toAffineEquiv '' R k) ∘ φ, (hR.image e.toAffineEquiv).comp_equiv φ,
    e.toAffineEquiv 0, e.toAffineEquiv.linear v, ?_⟩
  have := hRt.image e.toAffineEquiv
  exact ⟨this.1, fun k => this.2 (φ k)⟩

end TouchingSimplices

end Lift


section Normalize

/-!
# Theorem 1 (Zaks): bringing a configuration with a transversal into normal position

Given a touching configuration with a transversal line `ℓ`, an affine coordinate transformation
maps a thin "ladder" around `ℓ` to the half-square
`R₁ = {(x₁, x₂, 0, …, 0) : -1 ≤ x₁ ≤ 0, -1 ≤ x₂ ≤ 1}`, so that every simplex contains one of the
segments `S¹(α)` in its interior.
-/


open Set Module Filter Topology

namespace TouchingSimplices

/-- We may assume that the direction of the transversal has nonzero first coordinate. -/
lemma transversal_wlog {d : ℕ} (hd : 2 ≤ d) (h : TransversalFamily d) :
    ∃ P : Fin (2 ^ d) → Set (Fin d → ℝ), IsTouchingFamily d P ∧ ∃ p v, IsTransversal P p v ∧
      v ⟨0, by omega⟩ ≠ 0 := by
  obtain ⟨P, hP, p, v, hv⟩ := h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv.1
  let τ : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap ⟨0, by omega⟩ j)
  refine ⟨fun i => τ.toAffineEquiv '' P i, hP.image _, _, _, hv.image τ.toAffineEquiv, ?_⟩
  change τ v ⟨0, by omega⟩ ≠ 0
  simpa [τ, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft] using hj

/-- **Normalisation step of Theorem 1.** -/
theorem normalize_step {d : ℕ} (hd : 2 ≤ d) (h : TransversalFamily d) : NormalizedFamily d := by
  obtain ⟨P, hP, p, v, ⟨-, ht⟩, hv0⟩ := transversal_wlog hd h
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  choose t ht using ht
  -- the length of the ladder
  set K : ℝ := 1 + ∑ i, |t i| with hK
  have hKpos : 0 < K := by positivity
  have htK : ∀ i, |t i| < K := by
    intro i
    have := Finset.single_le_sum (f := fun i => |t i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith
  -- the width of the ladder
  have hball : ∀ i, ∃ ε > 0, Metric.ball (p + t i • v) ε ⊆ interior (P i) :=
    fun i => Metric.isOpen_iff.1 isOpen_interior _ (ht i)
  choose ε hε hεsub using hball
  have hne : (Finset.univ : Finset (Fin (2 ^ d))).Nonempty := Finset.univ_nonempty
  set m := Finset.univ.inf' hne ε
  have hm : 0 < m := (Finset.lt_inf'_iff hne).2 fun i _ => hε i
  have hmε : ∀ i, m ≤ ε i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set δ := m / 2
  have hδ : 0 < δ := by positivity
  -- the linear part of the coordinate transformation
  let M : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun x k => 2 * K * x i0 * v k +
        (if k.val = 0 then 0 else if k.val = 1 then δ * x i1 else x k)
      map_add' := by
        intro x y; ext k; simp only [Pi.add_apply]; split_ifs <;> ring
      map_smul' := by
        intro c x; ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  have hMapp : ∀ x k, M x k = 2 * K * x i0 * v k +
      (if k.val = 0 then 0 else if k.val = 1 then δ * x i1 else x k) := fun _ _ => rfl
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : x i0 = 0 := by
      have := congrFun hx i0
      rw [hMapp] at this
      simp only [i0, ite_true, add_zero, Pi.zero_apply] at this
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exfalso; linarith
        · exact h'
      · exact absurd h hv0
    ext k
    have := congrFun hx k
    rw [hMapp, h0] at this
    simp only [mul_zero, zero_mul, zero_add, Pi.zero_apply] at this
    rcases k with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0; exact h0
    by_cases hk1 : k = 1
    · subst hk1
      simp only [hk0, ite_false, ite_true] at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hδ.ne'
      · exact h
    · simpa [hk0, hk1] using this
  let Me : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := LinearEquiv.ofInjectiveEndo M hinj
  -- the affine transformation `A`, mapping the half-square onto the ladder
  let A : (Fin d → ℝ) ≃ᵃ[ℝ] (Fin d → ℝ) :=
    Me.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Fin d → ℝ) (p + K • v))
  have hA : ∀ a b : ℝ, A (pt2 a b) = p + (K + 2 * K * a) • v + (δ * b) • pt2 0 1 := by
    intro a b
    ext k
    change (p + K • v) k + M (pt2 a b) k = _
    rw [hMapp]
    simp only [pt2, i0, i1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ite_true]
    rcases k with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0; simp; ring
    by_cases hk1 : k = 1
    · subst hk1; simp; ring
    · simp [hk0, hk1]; ring
  refine ⟨fun i => A.symm '' P i, hP.image A.symm, fun i => (t i / K - 1) / 2, fun i => ⟨?_, ?_⟩⟩
  · have h1 := htK i
    rw [abs_lt] at h1
    have h2 : -1 < t i / K := by rw [lt_div_iff₀ hKpos]; linarith
    have h3 : t i / K < 1 := by rw [div_lt_iff₀ hKpos]; linarith
    constructor <;> linarith
  · intro x hx
    have hmem : A (pt2 ((t i / K - 1) / 2) x) ∈ interior (P i) := by
      rw [hA]
      have hcoef : K + 2 * K * ((t i / K - 1) / 2) = t i := by field_simp; ring
      rw [hcoef]
      apply hεsub i
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hn : ‖(pt2 0 1 : Fin d → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
        simp only [pt2]
        split_ifs <;> simp
      have hx' : |x| ≤ 1 := abs_le.2 hx
      have : ‖δ * x‖ ≤ δ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
        nlinarith [abs_nonneg x]
      calc ‖δ * x‖ * ‖(pt2 0 1 : Fin d → ℝ)‖ ≤ δ * 1 :=
            mul_le_mul this hn (norm_nonneg _) hδ.le
        _ < ε i := by linarith [hmε i, show δ = m / 2 from rfl]
    have := mem_interior_image A.symm hmem
    simpa using this

end TouchingSimplices

end Normalize


section Base

/-!
# Theorem 1 (Zaks): the base case `d = 2`

Four pairwise touching triangles in the plane, together with a transversal line
(the configuration `f(2) ≥ 4` of the chapter).
-/


open Set Module Finset

namespace TouchingSimplices

/-- Three points of the plane with nonzero determinant are affinely independent. -/
lemma affineIndependent_three (a b c : Fin 2 → ℝ)
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hs
  rw [Fin.sum_univ_three] at hw hs
  have e0 := congrFun hs 0
  have e1 := congrFun hs 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one] at e0 e1
  have hw0 : w 0 = -w 1 - w 2 := by linarith
  rw [hw0] at e0 e1
  have h1 : w 1 * ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (c 1 - a 1) * e0 - (c 0 - a 0) * e1
  have h2 : w 2 * ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (b 0 - a 0) * e1 - (b 1 - a 1) * e0
  have hw1 : w 1 = 0 := by simpa [h] using h1
  have hw2 : w 2 = 0 := by simpa [h] using h2
  intro i
  fin_cases i
  · simp [hw0, hw1, hw2]
  · exact hw1
  · exact hw2

/-- A positive convex combination of the vertices of a full-dimensional simplex lies in its
interior. -/
lemma mem_interior_of_weights {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v)
    (w : Fin (d + 1) → ℝ) (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 < w i) :
    (∑ i, w i • v i) ∈ interior (convexHull ℝ (range v)) := by
  have htot : affineSpan ℝ (range v) = ⊤ := by
    rw [hv.affineSpan_eq_top_iff_card_eq_finrank_add_one]; simp
  let b : AffineBasis (Fin (d + 1)) ℝ (Fin d → ℝ) := ⟨v, hv, htot⟩
  have hb : (b : Fin (d + 1) → Fin d → ℝ) = v := rfl
  rw [← hb, b.interior_convexHull, mem_setOf_iff']
  intro i
  rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw1,
    b.coord_apply_combination_of_mem (mem_univ i) hw1]
  exact hw i

/-- The linear functional `x ↦ a x₁ + b x₂` on the plane. -/
noncomputable def lin2 (a b : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  a • LinearMap.proj 0 + b • LinearMap.proj 1

lemma lin2_apply (a b : ℝ) (x : Fin 2 → ℝ) : lin2 a b x = a * x 0 + b * x 1 := by
  simp [lin2]

/-- A criterion for touching in the plane: the two sets lie on the two sides of a line and
share two distinct points. -/
lemma touching_two {P Q : Set (Fin 2 → ℝ)} (a b u : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hP : ∀ x ∈ P, lin2 a b x ≤ u) (hQ : ∀ x ∈ Q, u ≤ lin2 a b x) {x y : Fin 2 → ℝ}
    (hx : x ∈ P ∩ Q) (hy : y ∈ P ∩ Q) (hxy : x ≠ y) : Touching 2 P Q := by
  set f := lin2 a b
  have hfu : ∀ z ∈ P ∩ Q, f z = u := fun z hz => le_antisymm (hP z hz.1) (hQ z hz.2)
  have hle : vectorSpan ℝ (P ∩ Q) ≤ LinearMap.ker f := by
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, hp, q, hq, rfl⟩
    simp [vsub_eq_sub, map_sub, hfu p hp, hfu q hq]
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff]
    rintro r -
    rcases hab with ha | hb
    · refine ⟨(Pi.single (0 : Fin 2) (r / a) : Fin 2 → ℝ), ?_⟩
      simp [f, lin2_apply]; field_simp
    · refine ⟨(Pi.single (1 : Fin 2) (r / b) : Fin 2 → ℝ), ?_⟩
      simp [f, lin2_apply]; field_simp
  have hker : finrank ℝ (LinearMap.ker f) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  have hup := Submodule.finrank_mono hle
  have hpos : 0 < finrank ℝ (vectorSpan ℝ (P ∩ Q)) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨y -ᵥ x, vsub_mem_vectorSpan ℝ hy hx⟩, ?_⟩
    intro h
    apply hxy
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero, vsub_eq_sub, sub_eq_zero] at this
    exact this.symm
  exact ⟨⟨x, hx⟩, by omega⟩

/-- The convex hull of three points lies in a half-plane if the three points do. -/
lemma hull3_le {p₀ p₁ p₂ : Fin 2 → ℝ} (a b u : ℝ) (h₀ : lin2 a b p₀ ≤ u) (h₁ : lin2 a b p₁ ≤ u)
    (h₂ : lin2 a b p₂ ≤ u) : ∀ x ∈ convexHull ℝ (range ![p₀, p₁, p₂]), lin2 a b x ≤ u := by
  intro x hx
  refine (convexHull_min ?_ (convex_halfSpace_le (lin2 a b).isLinear u)) hx
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simpa

lemma hull3_ge {p₀ p₁ p₂ : Fin 2 → ℝ} (a b u : ℝ) (h₀ : u ≤ lin2 a b p₀) (h₁ : u ≤ lin2 a b p₁)
    (h₂ : u ≤ lin2 a b p₂) : ∀ x ∈ convexHull ℝ (range ![p₀, p₁, p₂]), u ≤ lin2 a b x := by
  intro x hx
  refine (convexHull_min ?_ (convex_halfSpace_ge (lin2 a b).isLinear u)) hx
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simpa

lemma vertex_mem {p : Fin 3 → (Fin 2 → ℝ)} (i : Fin 3) : p i ∈ convexHull ℝ (range p) :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

lemma midpoint_mem {p : Fin 3 → (Fin 2 → ℝ)} (i j : Fin 3) (m : Fin 2 → ℝ)
    (hm : m = (1 / 2 : ℝ) • p i + (1 / 2 : ℝ) • p j) : m ∈ convexHull ℝ (range p) := by
  rw [hm]
  exact convex_convexHull ℝ _ (vertex_mem i) (vertex_mem j) (by norm_num) (by norm_num)
    (by norm_num)

/-- The first triangle of the base configuration. -/
def tri1 : Set (Fin 2 → ℝ) := convexHull ℝ (range ![![0, 0], ![0, -1], ![2, 0]])
/-- The second triangle of the base configuration. -/
def tri2 : Set (Fin 2 → ℝ) := convexHull ℝ (range ![![0, 0], ![1, 0], ![0, 1]])
/-- The third triangle of the base configuration. -/
def tri3 : Set (Fin 2 → ℝ) := convexHull ℝ (range ![![1, 0], ![2, 0], ![-1, 2]])
/-- The fourth triangle of the base configuration. -/
def tri4 : Set (Fin 2 → ℝ) := convexHull ℝ (range ![![0, 1], ![-1, 2], ![0, -1]])

/-- The configuration of four pairwise touching triangles. -/
def baseConfig : Fin (2 ^ 2) → Set (Fin 2 → ℝ) := ![tri1, tri2, tri3, tri4]

lemma pt_ne {x y : Fin 2 → ℝ} (h : x 0 ≠ y 0 ∨ x 1 ≠ y 1) : x ≠ y := by
  rintro rfl; simp at h

lemma touching_12 : Touching 2 tri1 tri2 :=
  touching_two 0 1 0 (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (x := ![0, 0]) (y := ![1, 0])
    ⟨vertex_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 0,
      vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 0⟩
    ⟨midpoint_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 0 2 _
        (by ext k; fin_cases k <;> simp),
      vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 1⟩
    (pt_ne (by simp))

lemma touching_13 : Touching 2 tri1 tri3 :=
  touching_two 0 1 0 (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (x := ![1, 0]) (y := ![2, 0])
    ⟨midpoint_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 0 2 _
        (by ext k; fin_cases k <;> simp),
      vertex_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 0⟩
    ⟨vertex_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 2,
      vertex_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 1⟩
    (pt_ne (by norm_num))

lemma touching_14 : Touching 2 tri1 tri4 :=
  touching_two (-1) 0 0 (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (x := ![0, 0]) (y := ![0, -1])
    ⟨vertex_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 0,
      midpoint_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 0 2 _
        (by ext k; fin_cases k <;> simp)⟩
    ⟨vertex_mem (p := ![![0, 0], ![0, -1], ![2, 0]]) 1,
      vertex_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 2⟩
    (pt_ne (by norm_num))

lemma touching_23 : Touching 2 tri2 tri3 :=
  touching_two 1 1 1 (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by norm_num [lin2_apply])
      (by norm_num [lin2_apply]))
    (x := ![1, 0]) (y := ![0, 1])
    ⟨vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 1,
      vertex_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 0⟩
    ⟨vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 2,
      midpoint_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 0 2 _
        (by ext k; fin_cases k <;> simp)⟩
    (pt_ne (by norm_num))

lemma touching_24 : Touching 2 tri2 tri4 :=
  touching_two (-1) 0 0 (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by simp [lin2_apply]) (by simp [lin2_apply]))
    (x := ![0, 0]) (y := ![0, 1])
    ⟨vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 0,
      midpoint_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 0 2 _
        (by ext k; fin_cases k <;> simp)⟩
    ⟨vertex_mem (p := ![![0, 0], ![1, 0], ![0, 1]]) 2,
      vertex_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 0⟩
    (pt_ne (by norm_num))

lemma touching_34 : Touching 2 tri3 tri4 :=
  touching_two (-1) (-1) (-1) (by norm_num)
    (hull3_le _ _ _ (by simp [lin2_apply]) (by norm_num [lin2_apply])
      (by norm_num [lin2_apply]))
    (hull3_ge _ _ _ (by simp [lin2_apply]) (by norm_num [lin2_apply])
      (by norm_num [lin2_apply]))
    (x := ![0, 1]) (y := ![-1, 2])
    ⟨midpoint_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 0 2 _
        (by ext k; fin_cases k <;> simp),
      vertex_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 0⟩
    ⟨vertex_mem (p := ![![1, 0], ![2, 0], ![-1, 2]]) 2,
      vertex_mem (p := ![![0, 1], ![-1, 2], ![0, -1]]) 1⟩
    (pt_ne (by norm_num))

lemma baseConfig_isTouchingFamily : IsTouchingFamily 2 baseConfig := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact ⟨_, affineIndependent_three _ _ _ (by norm_num), rfl⟩
    · exact ⟨_, affineIndependent_three _ _ _ (by norm_num), rfl⟩
    · exact ⟨_, affineIndependent_three _ _ _ (by norm_num), rfl⟩
    · exact ⟨_, affineIndependent_three _ _ _ (by norm_num), rfl⟩
  · fin_cases i <;> fin_cases j <;> simp at hij <;> simp only [baseConfig]
    all_goals first
      | exact touching_12 | exact touching_13 | exact touching_14
      | exact touching_23 | exact touching_24 | exact touching_34
      | exact Touching.symm touching_12 | exact Touching.symm touching_13
      | exact Touching.symm touching_14 | exact Touching.symm touching_23
      | exact Touching.symm touching_24 | exact Touching.symm touching_34

/-- The base case of Theorem 1: four touching triangles with a transversal line. -/
theorem transversalFamily_two : TransversalFamily 2 := by
  refine ⟨baseConfig, baseConfig_isTouchingFamily, ![3 / 2, -1 / 10], ![-8 / 5, 1],
    pt_ne (by norm_num), fun i => ?_⟩
  fin_cases i
  · refine ⟨0, ?_⟩
    have := mem_interior_of_weights ![![0, 0], ![0, -1], ![2, 0]]
      (affineIndependent_three _ _ _ (by norm_num)) ![3 / 20, 1 / 10, 3 / 4]
      (by simp [Fin.sum_univ_three]; norm_num) (fun k => by fin_cases k <;> simp)
    have hpt : (![3 / 2, -1 / 10] : Fin 2 → ℝ) + (0 : ℝ) • ![-8 / 5, 1] =
        ∑ i, (![3 / 20, 1 / 10, 3 / 4] : Fin 3 → ℝ) i •
          (![![0, 0], ![0, -1], ![2, 0]] : Fin 3 → Fin 2 → ℝ) i := by
      funext k; fin_cases k <;> simp [Fin.sum_univ_three] <;> norm_num
    rw [hpt]
    exact this
  · refine ⟨4 / 5, ?_⟩
    have := mem_interior_of_weights ![![0, 0], ![1, 0], ![0, 1]]
      (affineIndependent_three _ _ _ (by norm_num)) ![2 / 25, 11 / 50, 7 / 10]
      (by simp [Fin.sum_univ_three]; norm_num) (fun k => by fin_cases k <;> simp)
    have hpt : (![3 / 2, -1 / 10] : Fin 2 → ℝ) + (4 / 5 : ℝ) • ![-8 / 5, 1] =
        ∑ i, (![2 / 25, 11 / 50, 7 / 10] : Fin 3 → ℝ) i •
          (![![0, 0], ![1, 0], ![0, 1]] : Fin 3 → Fin 2 → ℝ) i := by
      funext k; fin_cases k <;> simp [Fin.sum_univ_three] <;> norm_num
    rw [hpt]
    exact this
  · refine ⟨1 / 2, ?_⟩
    have := mem_interior_of_weights ![![1, 0], ![2, 0], ![-1, 2]]
      (affineIndependent_three _ _ _ (by norm_num)) ![7 / 10, 1 / 10, 1 / 5]
      (by simp [Fin.sum_univ_three]; norm_num) (fun k => by fin_cases k <;> simp)
    have hpt : (![3 / 2, -1 / 10] : Fin 2 → ℝ) + (1 / 2 : ℝ) • ![-8 / 5, 1] =
        ∑ i, (![7 / 10, 1 / 10, 1 / 5] : Fin 3 → ℝ) i •
          (![![1, 0], ![2, 0], ![-1, 2]] : Fin 3 → Fin 2 → ℝ) i := by
      funext k; fin_cases k <;> simp [Fin.sum_univ_three] <;> norm_num
    rw [hpt]
    exact this
  · refine ⟨1, ?_⟩
    have := mem_interior_of_weights ![![0, 1], ![-1, 2], ![0, -1]]
      (affineIndependent_three _ _ _ (by norm_num)) ![4 / 5, 1 / 10, 1 / 10]
      (by simp [Fin.sum_univ_three]; norm_num) (fun k => by fin_cases k <;> simp)
    have hpt : (![3 / 2, -1 / 10] : Fin 2 → ℝ) + (1 : ℝ) • ![-8 / 5, 1] =
        ∑ i, (![4 / 5, 1 / 10, 1 / 10] : Fin 3 → ℝ) i •
          (![![0, 1], ![-1, 2], ![0, -1]] : Fin 3 → Fin 2 → ℝ) i := by
      funext k; fin_cases k <;> simp [Fin.sum_univ_three] <;> norm_num
    rw [hpt]
    exact this

end TouchingSimplices

end Base


section Main

open Set Module

namespace TouchingSimplices

/-! ## Theorem 1 (Zaks) -/

/-- **Theorem 1 (Zaks).** For every `d ≥ 2` there is a family of `2^d` pairwise touching
`d`-simplices in `ℝ^d` together with a transversal line that hits the interior of every single one
of them. -/
theorem zaks (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : Fin (2 ^ d) → Set (Fin d → ℝ), IsTouchingFamily d P ∧
      ∃ p v : Fin d → ℝ, IsTransversal P p v := by
  induction d, hd using Nat.le_induction with
  | base => exact transversalFamily_two
  | succ d hd ih => exact lift_step hd (normalize_step hd ih)

/-! ## Theorem 2 (Perles) -/

/-- **Theorem 2 (Perles)**, for configurations: a family of `r` pairwise touching `d`-simplices
in `ℝ^d` (`d ≥ 1`) has `r < 2^(d+1)`. -/
theorem perles {d : ℕ} (hd : 1 ≤ d) {r : ℕ} (P : Fin r → Set (Fin d → ℝ))
    (hP : IsTouchingFamily d P) : r < 2 ^ (d + 1) :=
  card_lt_of_isTouchingFamily hd (Module.finrank_fin_fun ℝ) P hP

/-! ## Consequences for `f(d)` -/

lemma isTouchingFamily_empty (d : ℕ) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Fin 0 → Set E) : IsTouchingFamily d P :=
  ⟨fun i => i.elim0, fun i => i.elim0⟩

lemma touchingNumber_set_bddAbove {d : ℕ} (hd : 1 ≤ d) :
    BddAbove {r : ℕ | ∃ P : Fin r → Set (Fin d → ℝ), IsTouchingFamily d P} :=
  ⟨2 ^ (d + 1), fun _ ⟨P, hP⟩ => (perles hd P hP).le⟩

/-- Every touching configuration has at most `f(d)` simplices. -/
lemma le_touchingNumber_of_isTouchingFamily {d : ℕ} (hd : 1 ≤ d) {r : ℕ}
    (P : Fin r → Set (Fin d → ℝ)) (hP : IsTouchingFamily d P) : r ≤ touchingNumber d :=
  le_csSup (touchingNumber_set_bddAbove hd) ⟨P, hP⟩

/-- `f(d)` is attained: there is a touching configuration of `f(d)` simplices. -/
lemma exists_isTouchingFamily_touchingNumber {d : ℕ} (hd : 1 ≤ d) :
    ∃ P : Fin (touchingNumber d) → Set (Fin d → ℝ), IsTouchingFamily d P :=
  Nat.sSup_mem (s := {r : ℕ | ∃ P : Fin r → Set (Fin d → ℝ), IsTouchingFamily d P})
    ⟨0, fun i => i.elim0, isTouchingFamily_empty d _⟩ (touchingNumber_set_bddAbove hd)

/-- **Theorem 2 (Perles).** For all `d ≥ 1`, `f(d) < 2^(d+1)`. -/
theorem touchingNumber_lt {d : ℕ} (hd : 1 ≤ d) : touchingNumber d < 2 ^ (d + 1) := by
  obtain ⟨P, hP⟩ := exists_isTouchingFamily_touchingNumber hd
  exact perles hd P hP

/-- The lower bound `f(d) ≥ 2^d` (consequence of Theorem 1). -/
theorem le_touchingNumber {d : ℕ} (hd : 2 ≤ d) : 2 ^ d ≤ touchingNumber d := by
  obtain ⟨P, hP, -⟩ := zaks d hd
  exact le_touchingNumber_of_isTouchingFamily (by omega) P hP

/-- `f(2) ≥ 4`. -/
theorem four_le_touchingNumber_two : 4 ≤ touchingNumber 2 := le_touchingNumber le_rfl

/-- `f(3) ≥ 8`. -/
theorem eight_le_touchingNumber_three : 8 ≤ touchingNumber 3 :=
  le_touchingNumber (d := 3) (by norm_num)

/-! ## `f(1) = 2` -/

lemma convexHull_range_two (v : Fin 2 → ℝ) :
    convexHull ℝ (range v) = Icc (v 0 ⊓ v 1) (v 0 ⊔ v 1) := by
  have : range v = {v 0, v 1} := by
    ext x; simp [Fin.exists_fin_two, eq_comm]
  rw [this, convexHull_pair, segment_eq_uIcc]
  rfl

/-- A `1`-simplex in `ℝ` is a nondegenerate closed interval. -/
lemma IsSimplex.eq_Icc {Q : Set ℝ} (h : IsSimplex 1 Q) : ∃ a b, a < b ∧ Q = Icc a b := by
  obtain ⟨v, hv, rfl⟩ := h
  have hne : v 0 ≠ v 1 := hv.injective.ne (by decide)
  exact ⟨_, _, inf_lt_sup.2 hne, convexHull_range_two v⟩

/-- Two touching intervals meet in exactly one point. -/
lemma Touching.max_eq_min {a b c d : ℝ} (h : Touching 1 (Icc a b) (Icc c d)) :
    max a c = min b d := by
  obtain ⟨hne, hdim⟩ := h
  have hsub : (Icc a b ∩ Icc c d).Subsingleton := by
    rw [← vectorSpan_eq_bot_iff_subsingleton (k := ℝ)]
    exact Submodule.finrank_eq_zero.1 (by omega)
  rw [Icc_inter_Icc] at hsub hne
  have hle := nonempty_Icc.1 hne
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have := hsub (left_mem_Icc.2 hle) (right_mem_Icc.2 hle)
  exact absurd this hlt.ne

/-- There are no three pairwise touching `1`-simplices in `ℝ`. -/
lemma no_three_touching_intervals (P : Fin 3 → Set ℝ) (hP : IsTouchingFamily 1 P) : False := by
  choose a b hab hP' using fun i => (hP.1 i).eq_Icc
  have t : ∀ i j, i ≠ j → max (a i) (a j) = min (b i) (b j) := by
    intro i j hij
    have : Touching 1 (P i) (P j) := hP.2 hij
    rw [hP' i, hP' j] at this
    exact this.max_eq_min
  have h01 := t 0 1 (by decide)
  have h02 := t 0 2 (by decide)
  have h12 := t 1 2 (by decide)
  have := hab 0
  have := hab 1
  have := hab 2
  rcases max_cases (a 0) (a 1) with ⟨e1, -⟩ | ⟨e1, -⟩ <;>
  rcases min_cases (b 0) (b 1) with ⟨f1, -⟩ | ⟨f1, -⟩ <;>
  rcases max_cases (a 0) (a 2) with ⟨e2, -⟩ | ⟨e2, -⟩ <;>
  rcases min_cases (b 0) (b 2) with ⟨f2, -⟩ | ⟨f2, -⟩ <;>
  rcases max_cases (a 1) (a 2) with ⟨e3, -⟩ | ⟨e3, -⟩ <;>
  rcases min_cases (b 1) (b 2) with ⟨f3, -⟩ | ⟨f3, -⟩ <;>
  simp only [e1, f1, e2, f2, e3, f3] at h01 h02 h12 <;>
  linarith [max_le_iff.1 (le_refl (max (a 0) (a 1))), le_max_left (a 0) (a 1),
    le_max_right (a 0) (a 1), le_max_left (a 0) (a 2), le_max_right (a 0) (a 2),
    le_max_left (a 1) (a 2), le_max_right (a 1) (a 2), min_le_left (b 0) (b 1),
    min_le_right (b 0) (b 1), min_le_left (b 0) (b 2), min_le_right (b 0) (b 2),
    min_le_left (b 1) (b 2), min_le_right (b 1) (b 2)]

/-- `f(1) = 2`. -/
theorem touchingNumber_one : touchingNumber 1 = 2 := by
  let e : (Fin 1 → ℝ) ≃ᵃ[ℝ] ℝ := (LinearEquiv.funUnique (Fin 1) ℝ ℝ).toAffineEquiv
  refine le_antisymm ?_ ?_
  · obtain ⟨P, hP⟩ := exists_isTouchingFamily_touchingNumber le_rfl
    by_contra hlt
    push Not at hlt
    let φ : Fin 3 ↪ Fin (touchingNumber 1) := Fin.castLEEmb hlt
    have hQ : IsTouchingFamily 1 (fun i : Fin 3 => e '' P (φ i)) :=
      ⟨fun i => (hP.1 (φ i)).image e, fun i j hij => (hP.2 (φ.injective.ne hij)).image e⟩
    exact no_three_touching_intervals _ hQ
  · -- the two intervals `[0, 1]` and `[1, 2]`
    let Q : Fin 2 → Set ℝ := ![convexHull ℝ (range ![0, 1]), convexHull ℝ (range ![1, 2])]
    have hQ : IsTouchingFamily 1 Q := by
      have hs : ∀ x y : ℝ, x ≠ y → IsSimplex 1 (convexHull ℝ (range ![x, y])) :=
        fun x y hxy => ⟨_, affineIndependent_of_ne ℝ hxy, rfl⟩
      have h01 : Touching 1 (Icc (0 : ℝ) 1) (Icc 1 2) := by
        have : Icc (0 : ℝ) 1 ∩ Icc 1 2 = {1} := by
          rw [Icc_inter_Icc]; norm_num
        rw [Touching, this, vectorSpan_singleton, finrank_bot]
        exact ⟨singleton_nonempty _, rfl⟩
      have hc : ∀ x y : ℝ, x ≤ y → convexHull ℝ (range ![x, y]) = Icc x y := by
        intro x y hxy
        rw [convexHull_range_two]; simp [hxy]
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · fin_cases i
        · exact hs 0 1 (by norm_num)
        · exact hs 1 2 (by norm_num)
      · fin_cases i <;> fin_cases j <;> simp at hij <;>
          simp only [Q, hc 0 1 (by norm_num),
            hc 1 2 (by norm_num)]
        · simpa using h01
        · simpa using Touching.symm h01
    have := hQ.image e.symm
    exact le_touchingNumber_of_isTouchingFamily le_rfl _ this

/-! ## Statements quoted in the chapter -/

/-- **Bagemihl's conjecture (1956).** The maximal number of pairwise touching `d`-simplices in a
configuration in `ℝ^d` is `f(d) = 2^d`. The chapter records this equality for
dimensions `1`, `2`, and `3`. Here the general conjecture is stated only. -/
def BagemihlConjecture : Prop := ∀ d : ℕ, 1 ≤ d → touchingNumber d = 2 ^ d

/-- The statement `f(2) = 4`, which the chapter derives from the non-planarity of `K₅` (via the
dual graph of a configuration of five touching triangles).  Stated only; we prove
`4 ≤ f(2) ≤ 7` below. -/
def TouchingNumberTwoEqFour : Prop := touchingNumber 2 = 4

/-- The statement `f(3) = 8`, proved in a whole book by Zaks (1991), quoted in the chapter.
Stated only; we prove `8 ≤ f(3) ≤ 15` below. -/
def TouchingNumberThreeEqEight : Prop := touchingNumber 3 = 8

theorem touchingNumber_two_bounds : 4 ≤ touchingNumber 2 ∧ touchingNumber 2 ≤ 7 :=
  ⟨four_le_touchingNumber_two, Nat.le_of_lt_succ (touchingNumber_lt (by norm_num))⟩

theorem touchingNumber_three_bounds : 8 ≤ touchingNumber 3 ∧ touchingNumber 3 ≤ 15 :=
  ⟨eight_le_touchingNumber_three, Nat.le_of_lt_succ (touchingNumber_lt (by norm_num))⟩

/-- The conjecture holds in dimension `1`. -/
theorem bagemihl_one : touchingNumber 1 = 2 ^ 1 := touchingNumber_one

end TouchingSimplices

end Main

end
