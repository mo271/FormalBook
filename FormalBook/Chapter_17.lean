/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib

/-!
# Every large point set has an obtuse angle

Formalization of Chapter 17 of *Proofs from THE BOOK* (Aigner–Ziegler).

## Contents
  - Part 1 (Basic): touching convex sets, full dimension, polytopes, central
    symmetry; angle/inner-product facts; separation lemmas.
  - Theorem 1 (Danzer–Grünbaum)
    - (1) `Chapter17.unitCube_noObtuse`, `Chapter17.unitCube_card`,
      `Chapter17.unitCube_fullDim`
    - (2) `Chapter17.step2_antipodal_of_noObtuse`
    - (3) `Chapter17.step3_hullTranslatesTouch_of_antipodal`,
      `Chapter17.step3_antipodal_of_hullTranslatesTouch`
    - (4) `Chapter17.step4_polytopeTranslatesTouch_neg`
    - (5) `Chapter17.step5_symm_of_polytopeTranslatesTouch` (Minkowski symmetrization,
      including `Chapter17.minkowskiSymm_translates_inter_nonempty_iff`),
      `Chapter17.step5_polytopeTranslatesTouch_of_symm`
    - (6) `Chapter17.step6_card_le` (volume argument)
    - the chain: `Chapter17.theorem1`, `Chapter17.theorem1_all_eq`
    - Erdős' problem: `Chapter17.noObtuse_card_le`, `Chapter17.erdos_noObtuse_isGreatest`,
      `Chapter17.erdos_obtuse_of_card_gt`, `Chapter17.five_points_plane_obtuse`
  - Theorem 2 (Erdős–Füredi, Bevan's parameters): `Chapter17.theorem2`,
    `Chapter17.theorem2_dim34`, `Chapter17.danzer_gruenbaum_conjecture_false`
  - Appendix: Three tools from probability (`Chapter17.FinProbSpace`: expectation,
    linearity of expectation, Markov's inequality)

All parts of the chapter are contained in this single file.
-/

/-! ════════════════ Part: Basic ════════════════ -/


/-!
# Basic notions for "Every large point set has an obtuse angle"

This file contains the definitions used throughout the formalization of Chapter 17
(touching convex sets, full-dimensional point sets, full-dimensional convex polytopes,
central symmetry), together with general convex-geometric helper lemmas.

We work in an arbitrary finite-dimensional real inner product space `V`; the book's
`ℝ^d` is `EuclideanSpace ℝ (Fin d)`.
-/

@[expose] public section

open Set Pointwise

namespace Chapter17

/-! ## Definitions -/

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Two sets *touch* if they have at least one boundary point in common, while their
interiors do not intersect (the book's definition). -/
def Touch (A B : Set V) : Prop :=
  (frontier A ∩ frontier B).Nonempty ∧ Disjoint (interior A) (interior B)

/-- A set of points has *full dimension* if it is not contained in a (proper affine)
hyperplane, i.e. its affine span is the whole space. -/
def FullDim (S : Set V) : Prop := affineSpan ℝ S = ⊤

/-- `Q` is a *`d`-dimensional convex polytope* in the `d`-dimensional space `V`: it is the
convex hull of finitely many points and has nonempty interior. -/
def IsFullDimPolytope (Q : Set V) : Prop :=
  (∃ T : Finset V, Q = convexHull ℝ (T : Set V)) ∧ (interior Q).Nonempty

/-- `Q` is *centrally symmetric* (with respect to the origin): `x ∈ Q → -x ∈ Q`. -/
def IsCentrallySymmetric (Q : Set V) : Prop := ∀ x ∈ Q, -x ∈ Q

end Defs

/-! ## Version-stable simp lemmas -/

/-- Membership in a set-builder set (stated locally so that the development does not depend
on the current Mathlib name of this definitional lemma). -/
@[simp] lemma mem_setOf_iff' {α : Type*} {p : α → Prop} {a : α} : a ∈ {x | p x} ↔ p a :=
  Iff.rfl

/-- Evaluation of the negation of a continuous linear functional. -/
@[simp] lemma clm_neg_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V →L[ℝ] ℝ) (x : V) : (-f) x = -f x := rfl

/-! ## Angles and inner products -/

section Angles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open Real InnerProductGeometry

lemma angle_le_pi_div_two_iff (x y : V) : angle x y ≤ π / 2 ↔ 0 ≤ inner ℝ x y := by
  unfold angle
  rw [Real.arccos_le_pi_div_two]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have : 0 < ‖x‖ * ‖y‖ := by positivity
  constructor
  · intro h
    by_contra hn
    push Not at hn
    linarith [div_neg_of_neg_of_pos hn this]
  · intro h
    exact div_nonneg h this.le

lemma angle_lt_pi_div_two_iff (x y : V) : angle x y < π / 2 ↔ 0 < inner ℝ x y := by
  unfold angle
  rw [Real.arccos_lt_pi_div_two]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have : 0 < ‖x‖ * ‖y‖ := by positivity
  exact div_pos_iff_of_pos_right this

lemma euclidean_angle_le_pi_div_two_iff (a b c : V) :
    EuclideanGeometry.angle a b c ≤ π / 2 ↔ 0 ≤ inner ℝ (a - b) (c - b) :=
  angle_le_pi_div_two_iff _ _

lemma euclidean_angle_lt_pi_div_two_iff (a b c : V) :
    EuclideanGeometry.angle a b c < π / 2 ↔ 0 < inner ℝ (a - b) (c - b) :=
  angle_lt_pi_div_two_iff _ _

end Angles

/-! ## Half-spaces, separation and touching -/

section Convex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The interior of a closed half-space `{f ≤ c}` (for `f ≠ 0`) lies in the open
half-space `{f < c}`. -/
lemma interior_le_subset_lt {f : V →L[ℝ] ℝ} (hf : f ≠ 0) (c : ℝ) :
    interior {x | f x ≤ c} ⊆ {x | f x < c} := by
  intro y hy
  simp only [mem_setOf_iff']
  by_contra hlt
  have hyc : f y ≤ c := (interior_subset hy : y ∈ {x | f x ≤ c})
  have hfy : f y = c := le_antisymm hyc (not_lt.1 hlt)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext h)
  set w := (f v)⁻¹ • v with hw
  have hfw : f w = 1 := by simp [hw, hv]
  have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), y + t • w ∈ {x | f x ≤ c} := by
    have hc : Continuous (fun t : ℝ => y + t • w) := by fun_prop
    have h1 : Filter.Tendsto (fun t : ℝ => y + t • w) (nhds 0) (nhds y) := by
      simpa using hc.tendsto 0
    exact (h1.mono_left nhdsWithin_le_nhds).eventually (mem_interior_iff_mem_nhds.1 hy)
  obtain ⟨t, ht, htpos⟩ := (hmem.and self_mem_nhdsWithin).exists
  simp only [mem_setOf_iff', map_add, map_smul, hfw, smul_eq_mul, mul_one, hfy] at ht
  linarith

/-- Two closed sets which have a common point and are weakly separated by a hyperplane
`{f = c}` (with `f ≠ 0`) touch. -/
lemma touch_of_separated {A B : Set V} (hA : IsClosed A) (hB : IsClosed B) {x : V}
    (hxA : x ∈ A) (hxB : x ∈ B) {f : V →L[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ}
    (hAf : ∀ a ∈ A, f a ≤ c) (hBf : ∀ b ∈ B, c ≤ f b) : Touch A B := by
  have hfx : f x = c := le_antisymm (hAf x hxA) (hBf x hxB)
  have hintA : interior A ⊆ {y | f y < c} :=
    (interior_mono (fun a ha => hAf a ha)).trans (interior_le_subset_lt hf c)
  have hintB : interior B ⊆ {y | c < f y} := by
    have h := interior_le_subset_lt (f := -f) (neg_ne_zero.2 hf) (-c)
    refine (interior_mono ?_).trans (h.trans ?_)
    · intro b hb
      simp only [mem_setOf_iff', clm_neg_apply, neg_le_neg_iff]
      exact hBf b hb
    · intro y hy
      simp only [mem_setOf_iff', clm_neg_apply, neg_lt_neg_iff] at hy ⊢
      exact hy
  refine ⟨⟨x, ?_, ?_⟩, ?_⟩
  · rw [hA.frontier_eq]
    refine ⟨hxA, fun hx => ?_⟩
    have := hintA hx
    simp [hfx] at this
  · rw [hB.frontier_eq]
    refine ⟨hxB, fun hx => ?_⟩
    have := hintB hx
    simp [hfx] at this
  · rw [Set.disjoint_left]
    intro y hyA hyB
    have h1 := hintA hyA
    have h2 := hintB hyB
    simp only [mem_setOf_iff'] at h1 h2
    linarith

/-- A convex set with nonempty interior is contained in the closure of its interior. -/
lemma subset_closure_interior_of_convex {A : Set V} (hA : Convex ℝ A)
    (hA' : (interior A).Nonempty) : A ⊆ closure (interior A) := by
  rw [hA.closure_interior_eq_closure_of_nonempty_interior hA']
  exact subset_closure

/-- Two touching convex sets with nonempty interiors are weakly separated by a hyperplane. -/
lemma separated_of_touch {A B : Set V} (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    (hA : (interior A).Nonempty) (hB : (interior B).Nonempty) (h : Touch A B) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∃ c : ℝ, (∀ a ∈ A, f a ≤ c) ∧ (∀ b ∈ B, c ≤ f b) := by
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open_open hAc.interior isOpen_interior
    hBc.interior isOpen_interior h.2
  refine ⟨f, ?_, u, ?_, ?_⟩
  · rintro rfl
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    have h1 := hfA a ha
    have h2 := hfB b hb
    simp at h1 h2
    linarith
  · intro a ha
    have hcl : closure (interior A) ⊆ {y | f y ≤ u} :=
      closure_minimal (fun y hy => (hfA y hy).le) (isClosed_le f.continuous continuous_const)
    exact hcl (subset_closure_interior_of_convex hAc hA ha)
  · intro b hb
    have hcl : closure (interior B) ⊆ {y | u ≤ f y} :=
      closure_minimal (fun y hy => (hfB y hy).le) (isClosed_le continuous_const f.continuous)
    exact hcl (subset_closure_interior_of_convex hBc hB hb)

omit [InnerProductSpace ℝ V] in
/-- Touching closed sets intersect. -/
lemma Touch.inter_nonempty {A B : Set V} (h : Touch A B) (hA : IsClosed A)
    (hB : IsClosed B) : (A ∩ B).Nonempty := by
  obtain ⟨x, hxA, hxB⟩ := h.1
  exact ⟨x, hA.frontier_subset hxA, hB.frontier_subset hxB⟩

/-- A full-dimensional set does not lie in a hyperplane `{f = c}` with `f ≠ 0`. -/
lemma FullDim.not_subset_hyperplane [FiniteDimensional ℝ V] {S : Set V} (hS : FullDim S)
    {f : V →L[ℝ] ℝ} (hf : f ≠ 0) (c : ℝ) : ¬ ∀ x ∈ S, f x = c := by
  intro h
  obtain ⟨y, hy⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.2 hS
  have hsub : convexHull ℝ S ⊆ {x | f x ≤ c} := by
    refine convexHull_min (fun x hx => le_of_eq (h x hx)) ?_
    exact convex_halfSpace_le f.isLinear c
  have hsub' : convexHull ℝ S ⊆ {x | c ≤ f x} := by
    refine convexHull_min (fun x hx => ge_of_eq (h x hx)) ?_
    exact convex_halfSpace_ge f.isLinear c
  have h1 := interior_le_subset_lt hf c (interior_mono hsub hy)
  have h2 := interior_le_subset_lt (f := -f) (neg_ne_zero.2 hf) (-c)
    (interior_mono (fun x hx => by simpa using hsub' hx) hy)
  simp only [mem_setOf_iff', clm_neg_apply, neg_lt_neg_iff] at h1 h2
  linarith

lemma FullDim.interior_convexHull_nonempty [FiniteDimensional ℝ V] {S : Set V}
    (hS : FullDim S) : (interior (convexHull ℝ S)).Nonempty :=
  interior_convexHull_nonempty_iff_affineSpan_eq_top.2 hS

end Convex

end Chapter17

end

/-! ════════════════ Part: Probability ════════════════ -/


/-!
# Appendix: Three tools from probability

Finite probability spaces `(Ω, p)`, random variables, the induced distribution on the image,
expectation, linearity of expectation, and Markov's inequality.
We also record the "averaging" principle used in the probabilistic method: some outcome is
at most the expectation.
-/

@[expose] public section

open Finset

namespace Chapter17

/-- A finite probability space: a finite set `Ω` with a map `p : Ω → [0,1]` such that
`∑ ω, p ω = 1`. (`p ω ≤ 1` follows from nonnegativity and the sum condition.) -/
structure FinProbSpace (Ω : Type*) [Fintype Ω] where
  /-- the probability of each elementary outcome -/
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_eq_one : ∑ ω, p ω = 1

namespace FinProbSpace

variable {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω)

lemma le_one (ω : Ω) : P.p ω ≤ 1 := by
  rw [← P.sum_eq_one]
  exact single_le_sum (fun ω _ => P.nonneg ω) (mem_univ ω)

/-- The uniform distribution on a nonempty finite set. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinProbSpace Ω where
  p _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  sum_eq_one := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    field_simp

/-- The probability of an event `A ⊆ Ω`. -/
noncomputable def prob (A : Set Ω) : ℝ := by
  classical exact ∑ ω ∈ univ.filter (· ∈ A), P.p ω

/-- The distribution of a random variable `X : Ω → ℝ` on its image:
`p(X = x) := ∑_{X ω = x} p ω`. -/
noncomputable def distrib (X : Ω → ℝ) (x : ℝ) : ℝ := P.prob {ω | X ω = x}

/-- The induced distribution is a probability distribution on the image `X(Ω)`. -/
theorem sum_distrib (X : Ω → ℝ) :
    (∑ x ∈ (univ.image X), P.distrib X x) = 1 := by
  classical
  unfold distrib prob
  rw [← P.sum_eq_one, ← sum_fiberwise_of_maps_to (g := X) (t := univ.image X)
    (fun ω _ => mem_image_of_mem X (mem_univ ω))]
  refine sum_congr rfl fun x _ => ?_
  congr 1

/-- The expectation `E X = ∑ ω, p(ω) X(ω)`. -/
def expect (X : Ω → ℝ) : ℝ := ∑ ω, P.p ω * X ω

/-- Linearity of expectation: `E(X + Y) = E X + E Y` (no independence needed). -/
theorem expect_add (X Y : Ω → ℝ) : P.expect (X + Y) = P.expect X + P.expect Y := by
  simp only [expect, Pi.add_apply, mul_add, sum_add_distrib]

theorem expect_smul (c : ℝ) (X : Ω → ℝ) : P.expect (c • X) = c * P.expect X := by
  simp only [expect, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- Linearity of expectation for finite sums of random variables. -/
theorem expect_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, P.expect (X i) := by
  simp only [expect, mul_sum]
  exact sum_comm

/-- Linearity of expectation for finite linear combinations of random variables. -/
theorem expect_linear_combination {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ s, c i * X i ω) = ∑ i ∈ s, c i * P.expect (X i) := by
  rw [expect_sum]
  exact sum_congr rfl fun i _ => P.expect_smul (c i) (X i)

/-- The expectation of the indicator of an event is its probability. -/
theorem expect_indicator (A : Set Ω) [DecidablePred (· ∈ A)] :
    P.expect (fun ω => if ω ∈ A then 1 else 0) = P.prob A := by
  classical
  simp only [expect, prob, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext ω
  simp

/-- **Markov's inequality**: for a nonnegative random variable `X` and `a > 0`,
`Prob(X ≥ a) ≤ E X / a`. -/
theorem markov (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    P.prob {ω | a ≤ X ω} ≤ P.expect X / a := by
  classical
  rw [le_div_iff₀ ha]
  unfold prob expect
  rw [sum_mul]
  calc ∑ ω ∈ univ.filter (· ∈ {ω | a ≤ X ω}), P.p ω * a
      ≤ ∑ ω ∈ univ.filter (· ∈ {ω | a ≤ X ω}), P.p ω * X ω := by
        refine sum_le_sum fun ω hω => ?_
        simp only [mem_filter, mem_setOf_iff'] at hω
        exact mul_le_mul_of_nonneg_left hω.2 (P.nonneg ω)
    _ ≤ ∑ ω, P.p ω * X ω :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ω _ _ => mul_nonneg (P.nonneg ω) (hX ω))

/-- The averaging principle ("this is the point where the probabilistic method shows its
power"): some outcome `ω` satisfies `X ω ≤ E X`. -/
theorem exists_le_expect (X : Ω → ℝ) : ∃ ω, X ω ≤ P.expect X := by
  by_contra h
  push Not at h
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, 0 < P.p ω := by
    by_contra hp
    push Not at hp
    have : ∑ ω, P.p ω ≤ 0 := sum_nonpos fun ω _ => hp ω
    rw [P.sum_eq_one] at this
    norm_num at this
  have hpos : 0 < ∑ ω, P.p ω * (X ω - P.expect X) :=
    sum_pos' (fun ω _ => mul_nonneg (P.nonneg ω) (sub_nonneg.2 (h ω).le))
      ⟨ω₀, mem_univ _, mul_pos hω₀ (sub_pos.2 (h ω₀))⟩
  have hzero : ∑ ω, P.p ω * (X ω - P.expect X) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, P.sum_eq_one, one_mul]
    unfold expect
    ring
  linarith

/-- Example from the book: an unbiased die, `X` = the number on top; `E X = 7/2`. -/
example : (uniform (Fin 6)).expect (fun ω => (ω : ℝ) + 1) = 7 / 2 := by
  simp [expect, uniform, Fin.sum_univ_succ]
  norm_num

end FinProbSpace

end Chapter17

end

/-! ════════════════ Part: Steps ════════════════ -/


/-!
# Theorem 1, steps (2)–(5)

We define the properties of finite point sets `S ⊆ V` appearing in the chain of
inequalities of Theorem 1 and prove the implications between them, which yield the
inequalities (2)–(5) of the chain.
-/

@[expose] public section

open Set Pointwise

namespace Chapter17

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The properties in the chain of Theorem 1 -/

/-- (Class of (1).) `S` determines no obtuse angle: `∠(sᵢ, sⱼ, sₖ) ≤ π/2` for every three
(distinct) points `{sᵢ, sⱼ, sₖ} ⊆ S`. -/
def NoObtuse (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
    EuclideanGeometry.angle a b c ≤ Real.pi / 2

/-- (Class of (2).) *Antipodality*: for any two (distinct) points `sᵢ, sⱼ ∈ S` there is a
strip `{x | f sᵢ ≤ f x ≤ f sⱼ}` (with `f sᵢ < f sⱼ`, so bounded by two distinct parallel
hyperplanes) that contains `S`, with `sᵢ` and `sⱼ` lying in the two boundary hyperplanes. -/
def Antipodal (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ f : V →L[ℝ] ℝ, f a < f b ∧ ∀ x ∈ S, f a ≤ f x ∧ f x ≤ f b

/-- (Class of (3).) The translates `P - sᵢ`, `sᵢ ∈ S`, of `P := conv S` intersect in a
common point, but they only touch. -/
def HullTranslatesTouch (S : Finset V) : Prop :=
  (⋂ s ∈ S, (-s) +ᵥ convexHull ℝ (S : Set V)).Nonempty ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Touch ((-a) +ᵥ convexHull ℝ (S : Set V)) ((-b) +ᵥ convexHull ℝ (S : Set V))

/-- (Class of (4).) The translates `Q + sᵢ` of some `d`-dimensional convex polytope `Q`
touch pairwise. -/
def PolytopeTranslatesTouch (S : Finset V) : Prop :=
  ∃ Q : Set V, IsFullDimPolytope Q ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Touch (a +ᵥ Q) (b +ᵥ Q)

/-- (Class of (5).) The translates `Q* + sᵢ` of some `d`-dimensional centrally symmetric
convex polytope `Q*` touch pairwise. -/
def SymmPolytopeTranslatesTouch (S : Finset V) : Prop :=
  ∃ Q : Set V, IsFullDimPolytope Q ∧ IsCentrallySymmetric Q ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Touch (a +ᵥ Q) (b +ᵥ Q)

/-! ## Elementary facts about translates and convex hulls -/

omit [InnerProductSpace ℝ V] in
lemma mem_neg_vadd_iff {s x : V} {A : Set V} : x ∈ (-s) +ᵥ A ↔ x + s ∈ A := by
  rw [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_comm]

omit [InnerProductSpace ℝ V] in
lemma mem_vadd_iff {s x : V} {A : Set V} : x ∈ s +ᵥ A ↔ x - s ∈ A := by
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]

omit [InnerProductSpace ℝ V] in
/-- The standard simplex is compact, using Mathlib's current simplex type. -/
lemma isCompact_stdSimplex' (ι : Type*) [Fintype ι] :
    IsCompact (Set.univ : Set (Convexity.StdSimplex ℝ ι)) := by
  exact isCompact_univ

/-- The convex hull of a finite set in a real normed space is compact. -/
lemma isCompact_convexHull_of_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : s.Finite) : IsCompact (convexHull ℝ s) := by
  exact hs.isCompact_convexHull ℝ

lemma isClosed_convexHull_finset (S : Finset V) : IsClosed (convexHull ℝ (S : Set V)) :=
  (isCompact_convexHull_of_finite S.finite_toSet).isClosed

lemma IsFullDimPolytope.isCompact {Q : Set V} (hQ : IsFullDimPolytope Q) : IsCompact Q := by
  obtain ⟨⟨T, rfl⟩, -⟩ := hQ
  exact isCompact_convexHull_of_finite T.finite_toSet

lemma IsFullDimPolytope.convex {Q : Set V} (hQ : IsFullDimPolytope Q) : Convex ℝ Q := by
  obtain ⟨⟨T, rfl⟩, -⟩ := hQ
  exact convex_convexHull ℝ _

lemma noObtuse_iff_inner (S : Finset V) : NoObtuse S ↔
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → 0 ≤ inner ℝ (a - b) (c - b) := by
  unfold NoObtuse
  simp only [euclidean_angle_le_pi_div_two_iff]

/-- The convex hull of `S` is contained in any strip `{f a ≤ f x ≤ f b}` containing `S`. -/
lemma convexHull_subset_strip {S : Finset V} {f : V →L[ℝ] ℝ} {α β : ℝ}
    (h : ∀ x ∈ S, α ≤ f x ∧ f x ≤ β) :
    convexHull ℝ (S : Set V) ⊆ {x | α ≤ f x ∧ f x ≤ β} := by
  refine convexHull_min (fun x hx => h x hx) ?_
  exact (convex_halfSpace_ge f.isLinear α).inter (convex_halfSpace_le f.isLinear β)

/-! ## Step (2): no obtuse angles ⟹ antipodal -/

theorem step2_antipodal_of_noObtuse {S : Finset V} (h : NoObtuse S) : Antipodal S := by
  rw [noObtuse_iff_inner] at h
  intro a ha b hb hab
  refine ⟨innerSL ℝ (b - a), ?_, fun x hx => ⟨?_, ?_⟩⟩
  · simp only [innerSL_apply_apply]
    have : 0 < inner ℝ (b - a) (b - a) := by
      rw [real_inner_self_eq_norm_sq]
      have : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      positivity
    rw [inner_sub_right] at this
    linarith
  · simp only [innerSL_apply_apply]
    rw [← sub_nonneg, ← inner_sub_right]
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · subst hxb; exact real_inner_self_nonneg
    have := h b hb a ha x hx hab.symm (Ne.symm hxa) (Ne.symm hxb)
    exact this
  · simp only [innerSL_apply_apply]
    rw [← sub_nonneg, ← inner_sub_right]
    by_cases hxb : x = b
    · simp [hxb]
    by_cases hxa : x = a
    · subst hxa
      have : inner ℝ (b - x) (b - x) ≥ 0 := real_inner_self_nonneg
      linarith [this]
    have := h a ha b hb x hx hab (Ne.symm hxb) (Ne.symm hxa)
    have h2 : inner ℝ (b - a) (b - x) = inner ℝ (a - b) (x - b) := by
      rw [← neg_sub b a, ← neg_sub b x, inner_neg_neg]
    linarith

/-! ## Step (3): antipodal ⟺ the translates of the convex hull only touch -/

lemma zero_mem_iInter_neg_vadd_convexHull (S : Finset V) :
    (0 : V) ∈ ⋂ s ∈ S, (-s) +ᵥ convexHull ℝ (S : Set V) := by
  simp only [mem_iInter]
  intro s hs
  rw [mem_neg_vadd_iff, zero_add]
  exact subset_convexHull ℝ _ hs

theorem step3_hullTranslatesTouch_of_antipodal {S : Finset V} (h : Antipodal S) :
    HullTranslatesTouch S := by
  refine ⟨⟨0, zero_mem_iInter_neg_vadd_convexHull S⟩, ?_⟩
  intro a ha b hb hab
  obtain ⟨f, hfab, hS⟩ := h a ha b hb hab
  have hP := convexHull_subset_strip hS
  have hf : -f ≠ 0 := by
    intro h0
    have : f = 0 := neg_eq_zero.1 h0
    simp [this] at hfab
  have h0 : ∀ s ∈ S, (0 : V) ∈ (-s) +ᵥ convexHull ℝ (S : Set V) := by
    intro s hs
    rw [mem_neg_vadd_iff, zero_add]
    exact subset_convexHull ℝ _ hs
  refine touch_of_separated (((isClosed_convexHull_finset S).vadd _))
    (((isClosed_convexHull_finset S).vadd _)) (h0 a ha) (h0 b hb) hf (c := 0) ?_ ?_
  · intro y hy
    rw [mem_neg_vadd_iff] at hy
    have := (hP hy).1
    simp only [clm_neg_apply, map_add] at this ⊢
    linarith
  · intro y hy
    rw [mem_neg_vadd_iff] at hy
    have := (hP hy).2
    simp only [clm_neg_apply, map_add] at this ⊢
    linarith

theorem step3_antipodal_of_hullTranslatesTouch [FiniteDimensional ℝ V] {S : Finset V}
    (hS : FullDim (S : Set V)) (h : HullTranslatesTouch S) : Antipodal S := by
  intro a ha b hb hab
  have hint := hS.interior_convexHull_nonempty
  have hconv : ∀ s : V, Convex ℝ ((-s) +ᵥ convexHull ℝ (S : Set V)) :=
    fun s => (convex_convexHull ℝ _).vadd _
  have hint' : ∀ s : V, (interior ((-s) +ᵥ convexHull ℝ (S : Set V))).Nonempty := by
    intro s
    rw [interior_vadd]
    exact hint.vadd_set
  obtain ⟨f, hf, c, hA, hB⟩ :=
    separated_of_touch (hconv a) (hconv b) (hint' a) (hint' b) (h.2 a ha b hb hab)
  have h0 : ∀ s ∈ S, (0 : V) ∈ (-s) +ᵥ convexHull ℝ (S : Set V) := by
    intro s hs
    rw [mem_neg_vadd_iff, zero_add]
    exact subset_convexHull ℝ _ hs
  have hc1 := hA 0 (h0 a ha)
  have hc2 := hB 0 (h0 b hb)
  simp only [map_zero] at hc1 hc2
  have hx : ∀ x ∈ S, f b ≤ f x ∧ f x ≤ f a := by
    intro x hx
    have hxa : x - a ∈ (-a) +ᵥ convexHull ℝ (S : Set V) := by
      rw [mem_neg_vadd_iff, sub_add_cancel]; exact subset_convexHull ℝ _ hx
    have hxb : x - b ∈ (-b) +ᵥ convexHull ℝ (S : Set V) := by
      rw [mem_neg_vadd_iff, sub_add_cancel]; exact subset_convexHull ℝ _ hx
    have h1 := hA _ hxa
    have h2 := hB _ hxb
    rw [map_sub] at h1 h2
    constructor <;> linarith
  refine ⟨-f, ?_, fun x hx' => ?_⟩
  · simp only [clm_neg_apply, neg_lt_neg_iff]
    rcases (hx a ha).1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      refine hS.not_subset_hyperplane hf (f a) fun x hx' => ?_
      have := hx x hx'
      exact le_antisymm this.2 (heq ▸ this.1)
  · have := hx x hx'
    simp only [clm_neg_apply, neg_le_neg_iff]
    exact ⟨this.2, this.1⟩

/-! ## Step (4): the translates of the convex hull touch ⟹ the translates of a polytope
touch (for the reflected set `-S`) -/

lemma FullDim.neg [FiniteDimensional ℝ V] [DecidableEq V] {S : Finset V}
    (hS : FullDim (S : Set V)) :
    FullDim ((-S : Finset V) : Set V) := by
  unfold FullDim
  rw [← interior_convexHull_nonempty_iff_affineSpan_eq_top, Finset.coe_neg, convexHull_neg]
  have := hS.interior_convexHull_nonempty
  rw [← Set.image_neg_eq_neg]
  have h2 := (Homeomorph.neg V).image_interior (convexHull ℝ (S : Set V))
  have e : ⇑(Homeomorph.neg V) = Neg.neg := rfl
  rw [e] at h2
  rw [← h2]
  exact this.image _

theorem step4_polytopeTranslatesTouch_neg [FiniteDimensional ℝ V] [DecidableEq V] {S : Finset V}
    (hS : FullDim (S : Set V)) (h : HullTranslatesTouch S) :
    PolytopeTranslatesTouch (-S) := by
  refine ⟨convexHull ℝ (S : Set V), ⟨⟨S, rfl⟩, FullDim.interior_convexHull_nonempty hS⟩, ?_⟩
  intro a ha b hb hab
  rw [Finset.mem_neg'] at ha hb
  have := h.2 (-a) ha (-b) hb (fun h' => hab (neg_injective h'))
  simpa using this

/-! ## Step (5): Minkowski symmetrization -/

/-- The Minkowski symmetrization `Q* = ½ (Q - Q)` of a set `Q`. -/
def minkowskiSymm (Q : Set V) : Set V := (1 / 2 : ℝ) • (Q - Q)

lemma mem_minkowskiSymm {Q : Set V} {z : V} :
    z ∈ minkowskiSymm Q ↔ ∃ p ∈ Q, ∃ q ∈ Q, z = (1 / 2 : ℝ) • (p - q) := by
  unfold minkowskiSymm
  constructor
  · rintro ⟨w, ⟨p, hp, q, hq, rfl⟩, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p - q, ⟨p, hp, q, hq, rfl⟩, rfl⟩

lemma minkowskiSymm_centrallySymmetric (Q : Set V) :
    IsCentrallySymmetric (minkowskiSymm Q) := by
  intro x hx
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_minkowskiSymm.1 hx
  refine mem_minkowskiSymm.2 ⟨q, hq, p, hp, ?_⟩
  rw [← smul_neg, neg_sub]

lemma IsFullDimPolytope.minkowskiSymm [DecidableEq V] {Q : Set V} (hQ : IsFullDimPolytope Q) :
    IsFullDimPolytope (minkowskiSymm Q) := by
  obtain ⟨⟨T, rfl⟩, hint⟩ := hQ
  refine ⟨⟨(1 / 2 : ℝ) • (T - T), ?_⟩, ?_⟩
  · unfold Chapter17.minkowskiSymm
    rw [Finset.coe_smul_finset, Finset.coe_sub, convexHull_smul, convexHull_sub]
  · obtain ⟨q₀, hq₀⟩ := hint
    have hq₀' : q₀ ∈ convexHull ℝ (T : Set V) := interior_subset hq₀
    set U := (1 / 2 : ℝ) • ((-q₀) +ᵥ interior (convexHull ℝ (T : Set V))) with hU
    have hUo : IsOpen U := (isOpen_interior.vadd _).smul₀ (by norm_num)
    have hUsub : U ⊆ Chapter17.minkowskiSymm (convexHull ℝ (T : Set V)) := by
      rintro z ⟨w, hw, rfl⟩
      rw [mem_neg_vadd_iff] at hw
      refine mem_minkowskiSymm.2 ⟨w + q₀, interior_subset hw, q₀, hq₀', ?_⟩
      simp
    refine ⟨0, interior_maximal hUsub hUo ?_⟩
    exact ⟨0, ⟨q₀, hq₀, by simp⟩, by simp⟩

/-- Minkowski symmetrization preserves the property that two translates intersect
(the book's displayed chain of equivalences, for a convex set `Q`). -/
theorem minkowskiSymm_translates_inter_nonempty_iff {Q : Set V} (hQ : Convex ℝ Q) (a b : V) :
    ((a +ᵥ minkowskiSymm Q) ∩ (b +ᵥ minkowskiSymm Q)).Nonempty ↔
      ((a +ᵥ Q) ∩ (b +ᵥ Q)).Nonempty := by
  constructor
  · rintro ⟨x, hxa, hxb⟩
    rw [mem_vadd_iff] at hxa hxb
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := mem_minkowskiSymm.1 hxa
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := mem_minkowskiSymm.1 hxb
    have hm₁ : (1 / 2 : ℝ) • p₁ + (1 / 2 : ℝ) • q₂ ∈ Q :=
      hQ hp₁ hq₂ (by norm_num) (by norm_num) (by norm_num)
    have hm₂ : (1 / 2 : ℝ) • p₂ + (1 / 2 : ℝ) • q₁ ∈ Q :=
      hQ hp₂ hq₁ (by norm_num) (by norm_num) (by norm_num)
    refine ⟨a + ((1 / 2 : ℝ) • p₁ + (1 / 2 : ℝ) • q₂), ?_, ?_⟩
    · rw [mem_vadd_iff]; simpa using hm₁
    · rw [mem_vadd_iff]
      convert hm₂ using 1
      have e : x - a - (x - b) = (1 / 2 : ℝ) • (p₁ - q₁) - (1 / 2 : ℝ) • (p₂ - q₂) := by
        rw [← h₁, ← h₂]
      have e2 : b = a + ((1 / 2 : ℝ) • (p₁ - q₁) - (1 / 2 : ℝ) • (p₂ - q₂)) := by
        rw [← e]; abel
      rw [e2, smul_sub, smul_sub]
      abel
  · rintro ⟨x, hxa, hxb⟩
    rw [mem_vadd_iff] at hxa hxb
    refine ⟨a + (1 / 2 : ℝ) • ((x - a) - (x - b)), ?_, ?_⟩
    · rw [mem_vadd_iff, add_sub_cancel_left]
      exact mem_minkowskiSymm.2 ⟨_, hxa, _, hxb, rfl⟩
    · rw [mem_vadd_iff]
      refine mem_minkowskiSymm.2 ⟨_, hxb, _, hxa, ?_⟩
      have : a + (1 / 2 : ℝ) • (x - a - (x - b)) - b
          = (1 / 2 : ℝ) • (x - b - (x - a)) := by
        module
      exact this

/-- Minkowski symmetrization preserves the property that two translates of a
full-dimensional convex polytope touch. -/
theorem minkowskiSymm_touch {Q : Set V} (hQ : IsFullDimPolytope Q) {a b : V}
    (h : Touch (a +ᵥ Q) (b +ᵥ Q)) : Touch (a +ᵥ minkowskiSymm Q) (b +ᵥ minkowskiSymm Q) := by
  classical
  have hQc := hQ.convex
  have hQk := hQ.isCompact
  have hint : ∀ s : V, (interior (s +ᵥ Q)).Nonempty := by
    intro s
    rw [interior_vadd]
    exact hQ.2.vadd_set
  obtain ⟨f, hf, c, hA, hB⟩ :=
    separated_of_touch (hQc.vadd a) (hQc.vadd b) (hint a) (hint b) h
  obtain ⟨x, hxa, hxb⟩ := h.inter_nonempty (hQk.isClosed.vadd a) (hQk.isClosed.vadd b)
  have hfx : f x = c := le_antisymm (hA x hxa) (hB x hxb)
  rw [mem_vadd_iff] at hxa hxb
  have hup : ∀ p ∈ Q, f p ≤ c - f a := by
    intro p hp
    have := hA (a + p) (by rw [mem_vadd_iff]; simpa using hp)
    rw [map_add] at this
    linarith
  have hlow : ∀ p ∈ Q, c - f b ≤ f p := by
    intro p hp
    have := hB (b + p) (by rw [mem_vadd_iff]; simpa using hp)
    rw [map_add] at this
    linarith
  have hQs := hQ.minkowskiSymm
  set y := a + (1 / 2 : ℝ) • ((x - a) - (x - b)) with hy
  have hfy : f y = f a + (1 / 2 : ℝ) * (f b - f a) := by
    simp only [hy, map_add, map_smul, map_sub, smul_eq_mul]
    ring
  refine touch_of_separated (hQs.isCompact.isClosed.vadd a) (hQs.isCompact.isClosed.vadd b)
    (x := y) ?_ ?_ hf (c := f y) ?_ ?_
  · rw [mem_vadd_iff]
    refine mem_minkowskiSymm.2 ⟨x - a, hxa, x - b, hxb, ?_⟩
    rw [hy]; abel
  · rw [mem_vadd_iff]
    refine mem_minkowskiSymm.2 ⟨x - b, hxb, x - a, hxa, ?_⟩
    rw [hy]; module
  · intro z hz
    rw [mem_vadd_iff] at hz
    obtain ⟨p, hp, q, hq, hz⟩ := mem_minkowskiSymm.1 hz
    have hz' : z = a + (1 / 2 : ℝ) • (p - q) := by rw [← hz]; abel
    rw [hz', hfy]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith [hup p hp, hlow q hq]
  · intro z hz
    rw [mem_vadd_iff] at hz
    obtain ⟨p, hp, q, hq, hz⟩ := mem_minkowskiSymm.1 hz
    have hz' : z = b + (1 / 2 : ℝ) • (p - q) := by rw [← hz]; abel
    rw [hz', hfy]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith [hlow p hp, hup q hq]

theorem step5_symm_of_polytopeTranslatesTouch {S : Finset V}
    (h : PolytopeTranslatesTouch S) : SymmPolytopeTranslatesTouch S := by
  classical
  obtain ⟨Q, hQ, hT⟩ := h
  exact ⟨minkowskiSymm Q, hQ.minkowskiSymm, minkowskiSymm_centrallySymmetric Q,
    fun a ha b hb hab => minkowskiSymm_touch hQ (hT a ha b hb hab)⟩

theorem step5_polytopeTranslatesTouch_of_symm {S : Finset V}
    (h : SymmPolytopeTranslatesTouch S) : PolytopeTranslatesTouch S := by
  obtain ⟨Q, hQ, -, hT⟩ := h
  exact ⟨Q, hQ, hT⟩

end Chapter17

end

/-! ════════════════ Part: Step6 ════════════════ -/


/-!
# Theorem 1, step (6)

If the translates `Q* + sᵢ` of a full-dimensional centrally symmetric convex polytope `Q*`
touch pairwise, and `S` is full-dimensional, then `|S| ≤ 2^d`.

Following the book: every `½ (sᵢ - sⱼ)` lies in `Q*`, hence the sets
`Pⱼ = ½ (P + sⱼ)` (where `P = conv S`) satisfy `Pⱼ ⊆ Q* + sⱼ`, so they have pairwise disjoint
interiors; they are contained in `P` and have volume `2^{-d} vol(P)`, with `0 < vol(P) < ∞`.
-/

@[expose] public section

open Set Pointwise MeasureTheory

namespace Chapter17

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In the situation of step (6), all half-differences `½ (a - b)`, `a, b ∈ S`, lie in `Q`. -/
lemma half_sub_mem_of_touch {S : Finset V} {Q : Set V} (hQ : IsFullDimPolytope Q)
    (hsym : IsCentrallySymmetric Q) (hT : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Touch (a +ᵥ Q) (b +ᵥ Q))
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) : (1 / 2 : ℝ) • (a - b) ∈ Q := by
  have hQc := hQ.convex
  by_cases hab : a = b
  · subst hab
    obtain ⟨x, hx⟩ := hQ.2
    have hx' : x ∈ Q := interior_subset hx
    have := hQc hx' (hsym x hx') (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simpa using this
  · obtain ⟨x, hxa, hxb⟩ := (hT a ha b hb hab).inter_nonempty
      (hQ.isCompact.isClosed.vadd a) (hQ.isCompact.isClosed.vadd b)
    rw [mem_vadd_iff] at hxa hxb
    have hax : a - x ∈ Q := by simpa using hsym _ hxa
    have := hQc hxb hax (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    convert this using 1
    module

/-- Step (6) of Theorem 1. -/
theorem step6_card_le [FiniteDimensional ℝ V] {S : Finset V} (hS : FullDim (S : Set V))
    (h : SymmPolytopeTranslatesTouch S) : S.card ≤ 2 ^ Module.finrank ℝ V := by
  obtain ⟨Q, hQ, hsym, hT⟩ := h
  have hQc := hQ.convex
  set P := convexHull ℝ (S : Set V) with hPdef
  have hPc : Convex ℝ P := convex_convexHull ℝ _
  -- `½ (x - b) ∈ Q` for all `x ∈ P`, `b ∈ S`
  have hPQ : ∀ b ∈ S, ∀ x ∈ P, (1 / 2 : ℝ) • (x - b) ∈ Q := by
    intro b hb
    have hconv : Convex ℝ {x : V | (1 / 2 : ℝ) • (x - b) ∈ Q} := by
      intro x hx y hy s t hs ht hst
      simp only [mem_setOf_iff'] at hx hy ⊢
      convert hQc hx hy hs ht hst using 1
      have : b = s • b + t • b := by rw [← add_smul, hst, one_smul]
      conv_lhs => rw [this]
      module
    exact convexHull_min (fun x hx => half_sub_mem_of_touch hQ hsym hT hx hb) hconv
  -- the sets `Pⱼ = ½ (P + sⱼ)`
  set Pj : V → Set V := fun b => (1 / 2 : ℝ) • (b +ᵥ P) with hPj
  have hPj_mem : ∀ b y, y ∈ Pj b ↔ ∃ x ∈ P, y = (1 / 2 : ℝ) • (x + b) := by
    intro b y
    simp only [hPj, mem_smul_set, mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by rw [add_comm]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b + x, ⟨x, hx, rfl⟩, by rw [add_comm]⟩
  have hPj_sub_Q : ∀ b ∈ S, Pj b ⊆ b +ᵥ Q := by
    intro b hb y hy
    obtain ⟨x, hx, rfl⟩ := (hPj_mem b y).1 hy
    rw [mem_vadd_iff]
    convert hPQ b hb x hx using 1
    module
  have hPj_sub_P : ∀ b ∈ S, Pj b ⊆ P := by
    intro b hb y hy
    obtain ⟨x, hx, rfl⟩ := (hPj_mem b y).1 hy
    have hbP : b ∈ P := subset_convexHull ℝ _ hb
    have := hPc hx hbP (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    convert this using 1
    module
  have hdisj : (S : Set V).PairwiseDisjoint (fun b => interior (Pj b)) := by
    intro a ha b hb hab
    exact ((hT a ha b hb hab).2.mono (interior_mono (hPj_sub_Q a ha))
      (interior_mono (hPj_sub_Q b hb)))
  -- measure theory
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  set μ : Measure V := Measure.addHaar with hμ
  have hPfin : μ P ≠ ⊤ := (isCompact_convexHull_of_finite S.finite_toSet).measure_lt_top.ne
  have hPpos : μ P ≠ 0 := by
    have hint := hS.interior_convexHull_nonempty
    have := isOpen_interior.measure_pos μ hint
    exact (lt_of_lt_of_le this (measure_mono interior_subset)).ne'
  set n := Module.finrank ℝ V
  have hvolPj : ∀ b, μ (Pj b) = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μ P := by
    intro b
    simp only [hPj]
    rw [Measure.addHaar_smul, measure_vadd]
    congr 2
    rw [abs_of_nonneg (by positivity)]
  have hvolint : ∀ b, μ (interior (Pj b)) = μ (Pj b) := by
    intro b
    refine le_antisymm (measure_mono interior_subset) ?_
    have hconv : Convex ℝ (Pj b) := (hPc.vadd b).smul _
    calc μ (Pj b) ≤ μ (interior (Pj b) ∪ frontier (Pj b)) := by
          apply measure_mono
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure
      _ ≤ μ (interior (Pj b)) + μ (frontier (Pj b)) := measure_union_le _ _
      _ = μ (interior (Pj b)) := by rw [hconv.addHaar_frontier μ, add_zero]
  have hsum : ∑ b ∈ S, μ (interior (Pj b)) ≤ μ P := by
    rw [← measure_biUnion_finset hdisj (fun b _ => isOpen_interior.measurableSet)]
    apply measure_mono
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨b, hb, hy⟩ := hy
    exact hPj_sub_P b hb (interior_subset hy)
  simp only [hvolint, hvolPj, Finset.sum_const, nsmul_eq_mul] at hsum
  have h1 : (S.card : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≤ 1 := by
    have : (S.card : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μ P ≤ 1 * μ P := by
      rw [one_mul, mul_assoc]; exact hsum
    exact (ENNReal.mul_le_mul_iff_left hPpos hPfin).1 this
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_one] at h1
  have h2 : (S.card : ℝ) ≤ 2 ^ n := by
    have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
    have : (S.card : ℝ) * (1 / 2) ^ n * 2 ^ n ≤ 1 * 2 ^ n :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rwa [mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, mul_one,
      one_mul] at this
  exact_mod_cast h2

end Chapter17

end

/-! ════════════════ Part: Theorem1 ════════════════ -/


/-!
# Theorem 1 and the answer to Erdős' question

* Step (1): the vertex set `{0,1}^d` of the unit cube has no obtuse angles.
* The chain of (in)equalities of Theorem 1, stated with `sSup` of cardinalities of
  full-dimensional finite point sets of `ℝ^d` with the respective property.
* Erdős' conjecture (Danzer–Grünbaum): every set of more than `2^d` points in `ℝ^d`
  (full-dimensional or not) determines an obtuse angle; and `2^d` is attained.
-/

@[expose] public section

open Set Pointwise

namespace Chapter17

/-! ## Combining the steps (general finite-dimensional inner product space) -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem symm_card_le {S : Finset V} (hS : FullDim (S : Set V))
    (h : SymmPolytopeTranslatesTouch S) : S.card ≤ 2 ^ Module.finrank ℝ V :=
  step6_card_le hS h

theorem polytope_card_le {S : Finset V} (hS : FullDim (S : Set V))
    (h : PolytopeTranslatesTouch S) : S.card ≤ 2 ^ Module.finrank ℝ V :=
  symm_card_le hS (step5_symm_of_polytopeTranslatesTouch h)

theorem hull_card_le {S : Finset V} (hS : FullDim (S : Set V))
    (h : HullTranslatesTouch S) : S.card ≤ 2 ^ Module.finrank ℝ V := by
  classical
  have := polytope_card_le hS.neg (step4_polytopeTranslatesTouch_neg hS h)
  rwa [Finset.card_neg] at this

theorem antipodal_card_le {S : Finset V} (hS : FullDim (S : Set V))
    (h : Antipodal S) : S.card ≤ 2 ^ Module.finrank ℝ V :=
  hull_card_le hS (step3_hullTranslatesTouch_of_antipodal h)

/-- A full-dimensional finite point set without obtuse angles has at most `2^d` points. -/
theorem noObtuse_card_le_of_fullDim {S : Finset V} (hS : FullDim (S : Set V))
    (h : NoObtuse S) : S.card ≤ 2 ^ Module.finrank ℝ V :=
  antipodal_card_le hS (step2_antipodal_of_noObtuse h)

/-- **Erdős' conjecture** (theorem of Danzer and Grünbaum), upper bound: every finite set of
points in a `d`-dimensional Euclidean space without obtuse angles has at most `2^d`
points. No full-dimensionality assumption is needed: a lower-dimensional set is handled by
working inside the direction of its affine span. -/
theorem noObtuse_card_le (S : Finset V) (h : NoObtuse S) :
    S.card ≤ 2 ^ Module.finrank ℝ V := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  set W : Submodule ℝ V := (affineSpan ℝ (S : Set V)).direction with hW
  have hmem : ∀ s ∈ S, s - s₀ ∈ W := fun s hs =>
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hs) (subset_affineSpan ℝ _ hs₀)
  let φ : S → W := fun s => ⟨s.1 - s₀, hmem s.1 s.2⟩
  have hφ : ∀ s, ((φ s : W) : V) = s.1 - s₀ := fun s => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have : ((φ a : W) : V) = (φ b : W) := by rw [hab]
    rw [hφ, hφ, sub_left_inj] at this
    exact Subtype.ext this
  set S' : Finset W := S.attach.image φ with hS'
  have hcard : S'.card = S.card := by
    rw [hS', Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hmemS' : ∀ w, w ∈ S' ↔ ∃ s, ∃ hs : s ∈ S, w = φ ⟨s, hs⟩ := by
    intro w
    simp only [hS', Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨⟨s, hs⟩, rfl⟩; exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩
  have hno : NoObtuse S' := by
    rw [noObtuse_iff_inner] at h ⊢
    intro a ha b hb c hc hab hbc hac
    obtain ⟨a, ha', rfl⟩ := (hmemS' a).1 ha
    obtain ⟨b, hb', rfl⟩ := (hmemS' b).1 hb
    obtain ⟨c, hc', rfl⟩ := (hmemS' c).1 hc
    have hab' : a ≠ b := fun e => hab (by subst e; rfl)
    have hbc' : b ≠ c := fun e => hbc (by subst e; rfl)
    have hac' : a ≠ c := fun e => hac (by subst e; rfl)
    have := h a ha' b hb' c hc' hab' hbc' hac'
    rw [Submodule.coe_inner]
    simp only [Submodule.coe_sub, hφ]
    convert this using 2 <;> abel
  have hfull : FullDim (S' : Set W) := by
    unfold FullDim
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty]
    swap
    · exact ⟨φ ⟨s₀, hs₀⟩, by rw [Finset.mem_coe, hmemS']; exact ⟨s₀, hs₀, rfl⟩⟩
    apply Submodule.map_injective_of_injective W.injective_subtype
    have hWeq : W = Submodule.span ℝ ((S : Set V) -ᵥ (S : Set V)) := by
      rw [hW, direction_affineSpan, vectorSpan_def]
    rw [Submodule.map_subtype_top, vectorSpan_def, Submodule.map_span]
    refine Eq.trans ?_ hWeq.symm
    congr 1
    ext v
    simp only [mem_image, Set.mem_vsub, Finset.mem_coe, Submodule.coe_subtype, vsub_eq_sub]
    constructor
    · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (hmemS' x).1 hx
      obtain ⟨b, hb, rfl⟩ := (hmemS' y).1 hy
      refine ⟨a, ha, b, hb, ?_⟩
      simp only [Submodule.coe_sub, hφ]
      abel
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨φ ⟨a, ha⟩ - φ ⟨b, hb⟩, ⟨_, (hmemS' _).2 ⟨a, ha, rfl⟩, _,
        (hmemS' _).2 ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      simp only [Submodule.coe_sub, hφ]
      abel
  have h1 := noObtuse_card_le_of_fullDim hfull hno
  rw [hcard] at h1
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_le W))

end General

/-! ## Step (1): the unit cube -/

section Cube

variable {d : ℕ}

/-- The vertex of the unit cube `{0,1}^d ⊆ ℝ^d` with coordinates given by `f`
(`true ↦ 1`, `false ↦ 0`). -/
def cubeVertex (f : Fin d → Bool) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if f i then 1 else 0)

/-- The vertex set `{0,1}^d` of the standard unit cube in `ℝ^d`. -/
noncomputable def unitCube (d : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.univ.image cubeVertex

lemma cubeVertex_apply (f : Fin d → Bool) (i : Fin d) :
    cubeVertex f i = if f i then 1 else 0 := rfl

lemma cubeVertex_injective : Function.Injective (cubeVertex (d := d)) := by
  intro f g h
  funext i
  have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  simp only [cubeVertex_apply] at this
  cases hf : f i <;> cases hg : g i <;> simp_all

theorem unitCube_card : (unitCube d).card = 2 ^ d := by
  rw [unitCube, Finset.card_image_of_injective _ cubeVertex_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

lemma inner_cubeVertex_nonneg (f g h : Fin d → Bool) :
    0 ≤ inner ℝ (cubeVertex f - cubeVertex g) (cubeVertex h - cubeVertex g) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [PiLp.sub_apply, cubeVertex_apply]
  cases f i <;> cases g i <;> cases h i <;> norm_num

/-- Step (1): `{0,1}^d` determines no obtuse angle. -/
theorem unitCube_noObtuse : NoObtuse (unitCube d) := by
  rw [noObtuse_iff_inner]
  intro a ha b hb c hc _ _ _
  simp only [unitCube, Finset.mem_image, Finset.mem_univ, true_and] at ha hb hc
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  obtain ⟨h, rfl⟩ := hc
  exact inner_cubeVertex_nonneg f g h

/-- The unit cube `{0,1}^d` is full-dimensional. -/
theorem unitCube_fullDim : FullDim (unitCube d : Set (EuclideanSpace ℝ (Fin d))) := by
  unfold FullDim
  have h0 : cubeVertex (fun _ => false) ∈ unitCube d := by simp [unitCube]
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty]
  swap
  · exact ⟨_, Finset.mem_coe.2 h0⟩
  rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  have hi : cubeVertex (fun j => decide (j = i)) ∈ unitCube d := by simp [unitCube]
  have := vsub_mem_vectorSpan ℝ (Finset.mem_coe.2 hi) (Finset.mem_coe.2 h0)
  have heq : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i =
      cubeVertex (fun j => decide (j = i)) -ᵥ cubeVertex (fun _ => false) := by
    ext j
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, vsub_eq_sub,
      PiLp.sub_apply, cubeVertex_apply]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  rw [heq]
  exact this

end Cube

/-! ## The chain of inequalities of Theorem 1 -/

section Chain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `max #S` over all full-dimensional finite point sets `S ⊆ V` with property `P`
(the maxima appearing in Theorem 1). This is the supremum in `ℕ`; all the classes in
Theorem 1 are shown to be bounded (by `2^d`) and nonempty, so the supremum is a maximum. -/
noncomputable def maxCard (P : Finset V → Prop) : ℕ :=
  sSup {n | ∃ S : Finset V, FullDim (S : Set V) ∧ P S ∧ S.card = n}

lemma le_maxCard {P : Finset V → Prop} {B : ℕ}
    (hB : ∀ S : Finset V, FullDim (S : Set V) → P S → S.card ≤ B)
    {S : Finset V} (hS : FullDim (S : Set V)) (hP : P S) : S.card ≤ maxCard P := by
  refine le_csSup ⟨B, ?_⟩ ⟨S, hS, hP, rfl⟩
  rintro n ⟨T, hT, hPT, rfl⟩
  exact hB T hT hPT

lemma maxCard_le {P : Finset V → Prop} {B : ℕ}
    (hB : ∀ S : Finset V, FullDim (S : Set V) → P S → S.card ≤ B) : maxCard P ≤ B := by
  refine csSup_le' ?_
  rintro n ⟨T, hT, hPT, rfl⟩
  exact hB T hT hPT

lemma maxCard_mem {P : Finset V → Prop} {B : ℕ}
    (hB : ∀ S : Finset V, FullDim (S : Set V) → P S → S.card ≤ B)
    (hne : ∃ S : Finset V, FullDim (S : Set V) ∧ P S) :
    ∃ S : Finset V, FullDim (S : Set V) ∧ P S ∧ S.card = maxCard P := by
  obtain ⟨S, hS, hP⟩ := hne
  have := Nat.sSup_mem (s := {n | ∃ S : Finset V, FullDim (S : Set V) ∧ P S ∧ S.card = n})
    ⟨S.card, S, hS, hP, rfl⟩ ⟨B, by rintro n ⟨T, hT, hPT, rfl⟩; exact hB T hT hPT⟩
  exact this

end Chain

section Theorem1

variable {d : ℕ}

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- **Theorem 1** (Danzer–Grünbaum). For every `d`, one has the chain of inequalities
```
2^d ≤(1) max #{S | no obtuse angles}
    ≤(2) max #{S | antipodal (strip property)}
    =(3) max #{S | the translates P - sᵢ of P = conv S meet in a point but only touch}
    ≤(4) max #{S | the translates Q + sᵢ of some d-polytope Q touch pairwise}
    =(5) max #{S | the translates Q* + sᵢ of some centrally symmetric d-polytope touch pairwise}
    ≤(6) 2^d,
```
where all maxima range over full-dimensional finite subsets `S ⊆ ℝ^d` (as assumed in the
book). -/
theorem theorem1 :
    2 ^ d ≤ maxCard (V := E d) NoObtuse ∧
    maxCard (V := E d) NoObtuse ≤ maxCard (V := E d) Antipodal ∧
    maxCard (V := E d) Antipodal = maxCard (V := E d) HullTranslatesTouch ∧
    maxCard (V := E d) HullTranslatesTouch ≤ maxCard (V := E d) PolytopeTranslatesTouch ∧
    maxCard (V := E d) PolytopeTranslatesTouch =
      maxCard (V := E d) SymmPolytopeTranslatesTouch ∧
    maxCard (V := E d) SymmPolytopeTranslatesTouch ≤ 2 ^ d := by
  classical
  have hd : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin
  have b1 : ∀ S : Finset (E d), FullDim (S : Set (E d)) → NoObtuse S → S.card ≤ 2 ^ d :=
    fun S hS h => by have := noObtuse_card_le_of_fullDim hS h; rwa [hd] at this
  have b2 : ∀ S : Finset (E d), FullDim (S : Set (E d)) → Antipodal S → S.card ≤ 2 ^ d :=
    fun S hS h => by have := antipodal_card_le hS h; rwa [hd] at this
  have b3 : ∀ S : Finset (E d), FullDim (S : Set (E d)) → HullTranslatesTouch S →
      S.card ≤ 2 ^ d := fun S hS h => by have := hull_card_le hS h; rwa [hd] at this
  have b4 : ∀ S : Finset (E d), FullDim (S : Set (E d)) → PolytopeTranslatesTouch S →
      S.card ≤ 2 ^ d := fun S hS h => by have := polytope_card_le hS h; rwa [hd] at this
  have b5 : ∀ S : Finset (E d), FullDim (S : Set (E d)) → SymmPolytopeTranslatesTouch S →
      S.card ≤ 2 ^ d := fun S hS h => by have := symm_card_le hS h; rwa [hd] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1)
    have := le_maxCard b1 unitCube_fullDim unitCube_noObtuse
    rwa [unitCube_card] at this
  · -- (2)
    exact maxCard_le fun S hS h => le_maxCard b2 hS (step2_antipodal_of_noObtuse h)
  · -- (3)
    apply le_antisymm
    · exact maxCard_le fun S hS h => le_maxCard b3 hS (step3_hullTranslatesTouch_of_antipodal h)
    · exact maxCard_le fun S hS h =>
        le_maxCard b2 hS (step3_antipodal_of_hullTranslatesTouch hS h)
  · -- (4)
    refine maxCard_le fun S hS h => ?_
    have := le_maxCard b4 hS.neg (step4_polytopeTranslatesTouch_neg hS h)
    rwa [Finset.card_neg] at this
  · -- (5)
    apply le_antisymm
    · exact maxCard_le fun S hS h =>
        le_maxCard b5 hS (step5_symm_of_polytopeTranslatesTouch h)
    · exact maxCard_le fun S hS h =>
        le_maxCard b4 hS (step5_polytopeTranslatesTouch_of_symm h)
  · -- (6)
    exact maxCard_le b5

/-- Consequently all the maxima in Theorem 1 are equal to `2^d`. -/
theorem theorem1_all_eq :
    maxCard (V := E d) NoObtuse = 2 ^ d ∧
    maxCard (V := E d) Antipodal = 2 ^ d ∧
    maxCard (V := E d) HullTranslatesTouch = 2 ^ d ∧
    maxCard (V := E d) PolytopeTranslatesTouch = 2 ^ d ∧
    maxCard (V := E d) SymmPolytopeTranslatesTouch = 2 ^ d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := theorem1 (d := d)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Erdős' problem, answered** (Danzer–Grünbaum 1962): the maximum size of a set of points
in `ℝ^d` determining no obtuse angle is exactly `2^d`. Here *all* finite subsets of `ℝ^d`
are allowed (no full-dimensionality assumption). Equivalently, every set of more than `2^d`
points in `ℝ^d` determines an obtuse angle. -/
theorem erdos_noObtuse_isGreatest :
    IsGreatest {n | ∃ S : Finset (E d), NoObtuse S ∧ S.card = n} (2 ^ d) := by
  refine ⟨⟨unitCube d, unitCube_noObtuse, unitCube_card⟩, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  have := noObtuse_card_le S hS
  rwa [finrank_euclideanSpace_fin] at this

/-- Erdős' formulation: every set of more than `2^d` points in `ℝ^d` determines at least one
obtuse angle, i.e. there are three distinct points `a, b, c ∈ S` with `∠ a b c > π/2`. -/
theorem erdos_obtuse_of_card_gt (S : Finset (E d)) (hS : 2 ^ d < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Real.pi / 2 < EuclideanGeometry.angle a b c := by
  by_contra hcon
  push Not at hcon
  have := erdos_noObtuse_isGreatest.2 ⟨S, fun a ha b hb c hc hab hbc hac =>
    hcon a ha b hb c hc hab hbc hac, rfl⟩
  exact absurd this (not_le.2 hS)

/-- The case `d = 2` discussed at the beginning of the chapter: any five points in the plane
determine an obtuse angle. -/
theorem five_points_plane_obtuse (S : Finset (E 2)) (hS : S.card = 5) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Real.pi / 2 < EuclideanGeometry.angle a b c :=
  erdos_obtuse_of_card_gt S (by rw [hS]; norm_num)

/-- The case `d = 3` (the other case solved in the Dutch prize competition): any nine points
in `ℝ³` determine an obtuse angle. -/
theorem nine_points_space_obtuse (S : Finset (E 3)) (hS : S.card = 9) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      Real.pi / 2 < EuclideanGeometry.angle a b c :=
  erdos_obtuse_of_card_gt S (by rw [hS]; norm_num)

end Theorem1

end Chapter17

end

/-! ════════════════ Part: Theorem2 ════════════════ -/


/-!
# Theorem 2: large acute sets in the cube

**Theorem 2.** For every `d ≥ 2` there is a set `S ⊆ {0,1}^d` of
`2 ⌊(√6/9) (2/√3)^d⌋` points in `ℝ^d` that determine only acute angles.
In particular, in dimension `d = 34` there is such a set of `72 > 2·34 - 1` points.

The proof is the probabilistic argument of the book: pick `3m` random 0/1-vectors; the
expected number of bad triples is `3 binom(3m,3) (3/4)^d < m`, so some choice has fewer than
`m` bad triples; delete one vector from each bad triple.

(The hypothesis `d ≥ 2` of the book is not needed: for `d ≤ 9` one has `m = 0`.)
-/

@[expose] public section

open Finset

namespace Chapter17

/-! ## Acute sets -/

section Acute

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `S` determines only acute angles: `∠(a, b, c) < π/2` for any three distinct points
`a, b, c ∈ S`. -/
def OnlyAcute (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
    EuclideanGeometry.angle a b c < Real.pi / 2

lemma OnlyAcute.mono {S T : Finset V} (h : OnlyAcute T) (hST : S ⊆ T) : OnlyAcute S :=
  fun a ha b hb c hc => h a (hST ha) b (hST hb) c (hST hc)

end Acute

/-- The parameter `m = ⌊(√6/9) (2/√3)^d⌋` of Theorem 2. -/
noncomputable def acuteParam (d : ℕ) : ℕ :=
  ⌊Real.sqrt 6 / 9 * (2 / Real.sqrt 3) ^ d⌋₊

/-! ## Counting lemmas -/

section Counting

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- The complement of three indices. -/
abbrev Rest (i j k : ι) := {l : ι // l ≠ i ∧ l ≠ j ∧ l ≠ k}

/-- Splitting a function `ι → β` into its values at three distinct points and the rest. -/
def splitThree {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (ι → β) ≃ (β × β × β) × (Rest i j k → β) where
  toFun z := ((z i, z j, z k), fun l => z l.1)
  invFun q l := if hi : l = i then q.1.1 else if hj : l = j then q.1.2.1 else
    if hk : l = k then q.1.2.2 else q.2 ⟨l, hi, hj, hk⟩
  left_inv z := by
    funext l
    by_cases hi : l = i
    · subst hi; simp
    by_cases hj : l = j
    · subst hj; simp [hi]
    by_cases hk : l = k
    · subst hk; simp [hi, hj]
    simp [hi, hj, hk]
  right_inv q := by
    obtain ⟨⟨a, b, c⟩, w⟩ := q
    simp only [dite_true, Prod.mk.injEq]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp [hij.symm]
    · simp [hik.symm, hjk.symm]
    · funext l
      obtain ⟨l, hi, hj, hk⟩ := l
      simp [hi, hj, hk]

omit [DecidableEq β] in
/-- For distinct `i, j, k`, the number of `z : ι → β` with `P (z i) (z j) (z k)` is the number
of triples satisfying `P`, times the number of functions on the remaining indices. -/
lemma card_filter_three {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (P : β × β × β → Prop) [DecidablePred P] :
    (univ.filter (fun z : ι → β => P (z i, z j, z k))).card =
      (univ.filter P).card * Fintype.card (Rest i j k → β) := by
  rw [← card_univ (α := Rest i j k → β), ← card_product]
  apply card_equiv ((splitThree hij hik hjk).trans (Equiv.refl _))
  intro z
  simp [splitThree]

end Counting

section BadTriples

variable {d n : ℕ}

/-- A triple `t = (j, i, k)` of indices (apex `j`) is *bad* for the vectors `x` if
`x(i)_ℓ = x(j)_ℓ` or `x(k)_ℓ = x(j)_ℓ` for every coordinate `ℓ`, i.e. if
`⟨x(i) - x(j), x(k) - x(j)⟩ = 0`. -/
def IsBad (x : Fin n → Fin d → Bool) (t : Fin n × Fin n × Fin n) : Prop :=
  ∀ l, x t.2.1 l = x t.1 l ∨ x t.2.2 l = x t.1 l

instance (x : Fin n → Fin d → Bool) (t : Fin n × Fin n × Fin n) : Decidable (IsBad x t) := by
  unfold IsBad; infer_instance

/-- The triples to be considered: apex `j`, two other vertices `i < k`. -/
def triples (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  univ.filter (fun t => t.2.1 < t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2)

/-- `#triples = 3 binom(n,3) < n³/2`. -/
lemma two_mul_card_triples_lt (hn : 0 < n) : 2 * (triples n).card < n ^ 3 := by
  set σ : Fin n × Fin n × Fin n → Fin n × Fin n × Fin n := fun t => (t.1, t.2.2, t.2.1)
    with hσ
  have hσinj : Function.Injective σ := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [hσ, Prod.mk.injEq] at h ⊢
    tauto
  have hdisj : Disjoint (triples n) ((triples n).image σ) := by
    rw [disjoint_left]
    rintro ⟨a, b, c⟩ ht ht'
    simp only [triples, mem_filter, mem_univ, true_and, mem_image, hσ, Prod.mk.injEq,
      Prod.exists] at ht ht'
    obtain ⟨a', b', c', ⟨h1, -⟩, rfl, rfl, rfl⟩ := ht'
    exact lt_asymm h1 ht.1
  set z : Fin n × Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)
  have hsub : triples n ∪ (triples n).image σ ⊆ univ.erase z := by
    intro t ht
    rw [mem_erase]
    refine ⟨?_, mem_univ _⟩
    rintro rfl
    simp only [mem_union, triples, mem_filter, mem_univ, true_and, mem_image, hσ, z,
      Prod.mk.injEq, Prod.exists] at ht
    rcases ht with h | ⟨a, b, c, ⟨h, -⟩, rfl, rfl, rfl⟩
    · exact lt_irrefl _ h.1
    · exact lt_irrefl _ h
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hσinj,
    card_erase_of_mem (mem_univ _), card_univ] at this
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  have h3 : n * (n * n) = n ^ 3 := by ring
  have hpos : 0 < n ^ 3 := by positivity
  omega

/-- The number of choices `q = (x(i), x(j), x(k))` of three 0/1-vectors in which the angle at
`x(j)` is right (or degenerate) is `6^d`. -/
lemma card_bad_triples_vectors :
    (univ.filter (fun q : (Fin d → Bool) × (Fin d → Bool) × (Fin d → Bool) =>
      ∀ l, q.1 l = q.2.1 l ∨ q.2.2 l = q.2.1 l)).card = 6 ^ d := by
  set G : Bool × Bool × Bool → Prop := fun a => a.1 = a.2.1 ∨ a.2.2 = a.2.1 with hG
  let e : {q : (Fin d → Bool) × (Fin d → Bool) × (Fin d → Bool) //
      ∀ l, q.1 l = q.2.1 l ∨ q.2.2 l = q.2.1 l} ≃ (Fin d → {a : Bool × Bool × Bool // G a}) :=
    { toFun := fun q l => ⟨(q.1.1 l, q.1.2.1 l, q.1.2.2 l), q.2 l⟩
      invFun := fun w => ⟨(fun l => (w l).1.1, fun l => (w l).1.2.1, fun l => (w l).1.2.2),
        fun l => (w l).2⟩
      left_inv := fun q => rfl
      right_inv := fun w => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  congr 1

lemma card_triples_vectors :
    (univ : Finset ((Fin d → Bool) × (Fin d → Bool) × (Fin d → Bool))).card = 8 ^ d := by
  simp [card_univ, Fintype.card_prod]
  rw [← mul_pow, ← mul_pow]
  norm_num

/-- The probability that one specific triple is bad is exactly `(3/4)^d`. -/
lemma prob_isBad {t : Fin n × Fin n × Fin n} (ht : t ∈ triples n) :
    (FinProbSpace.uniform (Fin n → Fin d → Bool)).prob {x | IsBad x t} = (3 / 4 : ℝ) ^ d := by
  obtain ⟨j, i, k⟩ := t
  simp only [triples, mem_filter, mem_univ, true_and] at ht
  obtain ⟨hik, hji, hjk⟩ := ht
  have hij : i ≠ j := Ne.symm hji
  have hik' : i ≠ k := hik.ne
  have hjk' : j ≠ k := hjk
  have hbad := card_filter_three (β := Fin d → Bool) hij hik' hjk'
    (fun q => ∀ l, q.1 l = q.2.1 l ∨ q.2.2 l = q.2.1 l)
  have hall := card_filter_three (β := Fin d → Bool) hij hik' hjk' (fun _ => True)
  rw [card_bad_triples_vectors] at hbad
  simp only [filter_true] at hall
  rw [card_triples_vectors] at hall
  unfold FinProbSpace.prob FinProbSpace.uniform
  simp only [sum_const, nsmul_eq_mul, mem_setOf_iff']
  have hfilter : (univ.filter (fun x : Fin n → Fin d → Bool => IsBad x (j, i, k))) =
      univ.filter (fun z : Fin n → Fin d → Bool =>
        ∀ l, (z i, z j, z k).1 l = (z i, z j, z k).2.1 l ∨
          (z i, z j, z k).2.2 l = (z i, z j, z k).2.1 l) := by
    exact Finset.filter_congr (fun x _ => Iff.rfl)
  set K := Fintype.card (Rest i j k → Fin d → Bool)
  have hcardΩ : Fintype.card (Fin n → Fin d → Bool) = 8 ^ d * K := by rw [← card_univ, hall]
  have hcardB : (univ.filter (fun x : Fin n → Fin d → Bool => IsBad x (j, i, k))).card =
      6 ^ d * K := by rw [hfilter, hbad]
  have hK : (0 : ℝ) < K := by
    have : 0 < K := Fintype.card_pos
    exact_mod_cast this
  rw [hcardΩ]
  convert_to ((6 ^ d * K : ℕ) : ℝ) * (1 / ((8 ^ d * K : ℕ) : ℝ)) = _
  · rw [hcardB]
  push_cast
  rw [div_pow]
  field_simp
  rw [← mul_pow, ← mul_pow]
  norm_num

end BadTriples

/-! ## The main argument -/

lemma acuteParam_sq_mul_le (d : ℕ) :
    ((acuteParam d : ℝ)) ^ 2 * (3 / 4 : ℝ) ^ d ≤ 2 / 27 := by
  have hx : (0 : ℝ) ≤ Real.sqrt 6 / 9 * (2 / Real.sqrt 3) ^ d := by positivity
  have hm : (acuteParam d : ℝ) ≤ Real.sqrt 6 / 9 * (2 / Real.sqrt 3) ^ d := Nat.floor_le hx
  have hm0 : (0 : ℝ) ≤ acuteParam d := Nat.cast_nonneg _
  have hsq : (acuteParam d : ℝ) ^ 2 ≤ (Real.sqrt 6 / 9 * (2 / Real.sqrt 3) ^ d) ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : (Real.sqrt 6 / 9 * (2 / Real.sqrt 3) ^ d) ^ 2 = 6 / 81 * (4 / 3 : ℝ) ^ d := by
    rw [mul_pow, div_pow, h6, ← pow_mul, mul_comm d 2, pow_mul, div_pow, h3]
    norm_num
  rw [hr] at hsq
  have hpos : (0 : ℝ) ≤ (3 / 4) ^ d := by positivity
  calc (acuteParam d : ℝ) ^ 2 * (3 / 4) ^ d ≤ 6 / 81 * (4 / 3 : ℝ) ^ d * (3 / 4) ^ d :=
        mul_le_mul_of_nonneg_right hsq hpos
    _ = 6 / 81 * ((4 / 3 : ℝ) * (3 / 4)) ^ d := by rw [mul_pow, mul_assoc]
    _ = 2 / 27 := by norm_num

lemma inner_cubeVertex_pos {d : ℕ} {f g h : Fin d → Bool} {l : Fin d}
    (hf : f l ≠ g l) (hh : h l ≠ g l) :
    0 < inner ℝ (cubeVertex f - cubeVertex g) (cubeVertex h - cubeVertex g) := by
  rw [PiLp.inner_apply]
  refine sum_pos' (fun i _ => ?_) ⟨l, mem_univ _, ?_⟩
  · simp only [PiLp.sub_apply, cubeVertex_apply]
    cases f i <;> cases g i <;> cases h i <;> norm_num
  · simp only [PiLp.sub_apply, cubeVertex_apply]
    revert hf hh
    cases f l <;> cases g l <;> cases h l <;> norm_num

/-- The probabilistic step: if `m > 0` and `m² (3/4)^d ≤ 2/27`, then some choice of `3m`
vectors in `{0,1}^d` has fewer than `m` bad triples. (The expected number of bad triples is
`#triples · (3/4)^d < m`, by linearity of expectation.) -/
lemma exists_few_bad {d m : ℕ} (hm : 0 < m) (h : (m : ℝ) ^ 2 * (3 / 4 : ℝ) ^ d ≤ 2 / 27) :
    ∃ x : Fin (3 * m) → Fin d → Bool, ((triples (3 * m)).filter (IsBad x)).card < m := by
  classical
  set P := FinProbSpace.uniform (Fin (3 * m) → Fin d → Bool)
  set X : (Fin (3 * m) → Fin d → Bool) → ℝ := fun x =>
    ∑ t ∈ triples (3 * m), if x ∈ {x | IsBad x t} then 1 else 0 with hX
  have hE : P.expect X = (triples (3 * m)).card * (3 / 4 : ℝ) ^ d := by
    rw [hX, P.expect_sum]
    rw [sum_congr rfl fun t ht => (P.expect_indicator {x | IsBad x t}).trans (prob_isBad ht)]
    rw [sum_const, nsmul_eq_mul]
  obtain ⟨x, hx⟩ := P.exists_le_expect X
  refine ⟨x, ?_⟩
  have hXx : X x = ((triples (3 * m)).filter (IsBad x)).card := by
    rw [hX]
    simp only [mem_setOf_iff']
    rw [sum_boole]
  have hT := two_mul_card_triples_lt (n := 3 * m) (by omega)
  have hT' : (2 : ℝ) * (triples (3 * m)).card < 27 * (m : ℝ) ^ 3 := by
    have : ((2 * (triples (3 * m)).card : ℕ) : ℝ) < (((3 * m) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast hT
    push_cast at this
    linarith
  have hq : (0 : ℝ) < (3 / 4) ^ d := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt : ((triples (3 * m)).card : ℝ) * (3 / 4) ^ d < m := by
    have h1 : ((triples (3 * m)).card : ℝ) * (3 / 4) ^ d < (27 / 2 * (m : ℝ) ^ 3) * (3 / 4) ^ d :=
      mul_lt_mul_of_pos_right (by linarith) hq
    have h2 : (27 / 2 * (m : ℝ) ^ 3) * (3 / 4) ^ d = 27 / 2 * m * ((m : ℝ) ^ 2 * (3 / 4) ^ d) := by
      ring
    have h3 : 27 / 2 * (m : ℝ) * ((m : ℝ) ^ 2 * (3 / 4) ^ d) ≤ 27 / 2 * m * (2 / 27) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h4 : 27 / 2 * (m : ℝ) * (2 / 27) = m := by ring
    linarith
  have : (((triples (3 * m)).filter (IsBad x)).card : ℝ) < m := by
    rw [← hXx]; linarith
  exact_mod_cast this

/-- The deletion step: from `3m` vectors with fewer than `m` bad triples, delete one vector
from each bad triple; the remaining (at least `2m + 1`) vectors are distinct and determine
only acute angles. -/
lemma exists_acute_of_few_bad {d m : ℕ} (x : Fin (3 * m) → Fin d → Bool)
    (hx : ((triples (3 * m)).filter (IsBad x)).card < m) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S ⊆ unitCube d ∧ S.card = 2 * m ∧ OnlyAcute S := by
  classical
  set B := (triples (3 * m)).filter (IsBad x) with hB
  set R := B.image (fun t => t.2.1) with hR
  set K := (univ : Finset (Fin (3 * m))) \ R with hK
  have hRc : R.card < m := card_image_le.trans_lt hx
  have hKc : 2 * m + 1 ≤ K.card := by
    have h1 : (univ : Finset (Fin (3 * m))).card ≤ K.card + R.card := by
      calc (univ : Finset (Fin (3 * m))).card = ((univ \ R) ∪ R).card := by
            rw [sdiff_union_of_subset (subset_univ R)]
        _ ≤ K.card + R.card := card_union_le _ _
    rw [card_univ, Fintype.card_fin] at h1
    omega
  have hgood : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, a ≠ b → b ≠ c → a ≠ c →
      ∃ l, x a l ≠ x b l ∧ x c l ≠ x b l := by
    intro a ha b hb c hc hab hbc hac
    by_contra hcon
    push Not at hcon
    have hbad : ∀ l, x a l = x b l ∨ x c l = x b l := by
      intro l
      by_cases h : x a l = x b l
      · exact Or.inl h
      · exact Or.inr (hcon l h)
    rcases lt_or_gt_of_ne hac with h | h
    · have hmem : (b, a, c) ∈ B := by
        simp only [hB, triples, mem_filter, mem_univ, true_and]
        exact ⟨⟨h, Ne.symm hab, hbc⟩, hbad⟩
      exact (mem_sdiff.1 ha).2 (mem_image.2 ⟨_, hmem, rfl⟩)
    · have hmem : (b, c, a) ∈ B := by
        simp only [hB, triples, mem_filter, mem_univ, true_and]
        exact ⟨⟨h, hbc, Ne.symm hab⟩, fun l => (hbad l).symm⟩
      exact (mem_sdiff.1 hc).2 (mem_image.2 ⟨_, hmem, rfl⟩)
  set v : Fin (3 * m) → EuclideanSpace ℝ (Fin d) := fun a => cubeVertex (x a) with hv
  have hinj : Set.InjOn v K := by
    intro a ha b hb hvab
    by_contra hab
    have hne : ((K.erase a).erase b).Nonempty := by
      rw [← card_pos]
      have h1 := card_erase_of_mem (Finset.mem_coe.1 ha)
      have h2 : b ∈ K.erase a := mem_erase.2 ⟨Ne.symm hab, Finset.mem_coe.1 hb⟩
      have h3 := card_erase_of_mem h2
      omega
    obtain ⟨c, hc⟩ := hne
    have hcb : c ≠ b := (mem_erase.1 hc).1
    have hca : c ≠ a := (mem_erase.1 (mem_erase.1 hc).2).1
    have hcK : c ∈ K := (mem_erase.1 (mem_erase.1 hc).2).2
    obtain ⟨l, hl, -⟩ := hgood a ha b hb c hcK hab (Ne.symm hcb) (Ne.symm hca)
    exact hl (congrFun (cubeVertex_injective hvab) l)
  set S₀ := K.image v with hS₀
  have hS₀c : S₀.card = K.card := card_image_of_injOn hinj
  obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq (show 2 * m ≤ S₀.card by omega)
  refine ⟨S, hSsub.trans ?_, hScard, ?_⟩
  · intro p hp
    obtain ⟨a, -, rfl⟩ := mem_image.1 hp
    simp [hv, unitCube]
  · refine OnlyAcute.mono ?_ hSsub
    intro p hp q hq r hr hpq hqr hpr
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hq
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hr
    have hab : a ≠ b := fun h => hpq (by rw [h])
    have hbc : b ≠ c := fun h => hqr (by rw [h])
    have hac : a ≠ c := fun h => hpr (by rw [h])
    obtain ⟨l, h1, h2⟩ := hgood a ha b hb c hc hab hbc hac
    rw [euclidean_angle_lt_pi_div_two_iff]
    exact inner_cubeVertex_pos h1 h2

/-- **Theorem 2** (Erdős–Füredi; parameters due to Bevan). For every `d` there is a set
`S ⊆ {0,1}^d` of exactly `2 ⌊(√6/9) (2/√3)^d⌋` points in `ℝ^d` that determines only acute
angles. -/
theorem theorem2 (d : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S ⊆ unitCube d ∧ S.card = 2 * acuteParam d ∧ OnlyAcute S := by
  rcases Nat.eq_zero_or_pos (acuteParam d) with h0 | hpos
  · exact ⟨∅, empty_subset _, by simp [h0], fun a ha => by simp at ha⟩
  obtain ⟨x, hx⟩ := exists_few_bad hpos (acuteParam_sq_mul_le d)
  exact exists_acute_of_few_bad x hx

/-- `⌊(√6/9) (2/√3)^34⌋ = 36`. -/
lemma acuteParam_34 : acuteParam 34 = 36 := by
  unfold acuteParam
  rw [Nat.floor_eq_iff (by positivity)]
  have h3 : (2 / Real.sqrt 3) ^ 34 = 2 ^ 34 / 3 ^ 17 := by
    have : Real.sqrt 3 ^ 34 = 3 ^ 17 := by
      rw [show (34 : ℕ) = 2 * 17 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [div_pow, this]
  rw [h3]
  have hlo : (2.449 : ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 6 < 2.4495 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/-- In dimension `d = 34` there is a set of `72 > 2·34 - 1` points (vertices of the unit
cube) with only acute angles. -/
theorem theorem2_dim34 :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 34)),
      S ⊆ unitCube 34 ∧ S.card = 72 ∧ 2 * 34 - 1 < S.card ∧ OnlyAcute S := by
  obtain ⟨S, hS, hcard, hac⟩ := theorem2 34
  rw [acuteParam_34] at hcard
  exact ⟨S, hS, hcard, by omega, hac⟩

/-- By Theorem 1, an acute set in `ℝ^d` has at most `2^d` points (every acute set determines
no obtuse angle). -/
theorem onlyAcute_card_le {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) (h : OnlyAcute S) :
    S.card ≤ 2 ^ d := by
  have := noObtuse_card_le S fun a ha b hb c hc hab hbc hac =>
    (h a ha b hb c hc hab hbc hac).le
  rwa [finrank_euclideanSpace_fin] at this

/-- The conjecture of Danzer and Grünbaum, that a set of points in `ℝ^d` with only acute
angles has at most `2d - 1` points, is false (Erdős–Füredi). -/
theorem danzer_gruenbaum_conjecture_false :
    ¬ ∀ (d : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d))), OnlyAcute S → S.card ≤ 2 * d - 1 := by
  intro h
  obtain ⟨S, -, hcard, hlt, hac⟩ := theorem2_dim34
  have := h 34 S hac
  omega

end Chapter17

end
