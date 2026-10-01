/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Daniele Cappello
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

@[expose] public section

/-!
# Lines in the plane and decompositions of graphs

## Theorem 1 (the Sylvester–Gallai theorem)

A finite set of points, not all on one line, always has an *ordinary line*: a line
containing exactly two of the points. This is `sylvester_gallai` below.

The proof is **Kelly's**, the one given in the book: over all triples of non-collinear
points, choose the one minimizing the distance from a point to the line through the other
two; on that line at least three points of the set lie, and two of them fall on the same
side of the foot of the perpendicular, yielding a strictly closer triple, a contradiction.

Kelly's argument is rendered purely vectorially: no areas, no angles, no similar triangles,
only the inner product. The strict inequality comes from the identity
`⟪A, w⟫ = ‖A‖ ^ 2 > 0`, which says that the minimizing point is not the
foot of the perpendicular. The pigeonhole step is isolated as a statement about three
distinct **real** numbers (`Pigeonhole.three`), which is exactly where the order of `ℝ`
must be used: the theorem is false over `ℂ` (the Hesse configuration).

The statement is proved in an arbitrary real inner product space with its affine torsor,
with no dimension hypothesis; the classical plane is the case `EuclideanSpace ℝ (Fin 2)`.

## Additional results in this file

Theorem 2: `SylvesterGallai.number_of_lines`.
Theorem 3: `Incidence.de_bruijn_erdos`, with its incidence quadratic identity.
Theorem 4: `GrahamPollak.graham_pollak`, with Tverberg's quadratic identity
and the sharp star decomposition.
The Fano example and its obstruction to real noncollinear realization are proved.
The graph appendix reuses Mathlib graph definitions and proves its basic correspondences.

Coverage limit: this file does not prove every supplementary assertion in the chapter.
In particular, the Green–Tao asymptotic bounds and their optimality, Coxeter's
order-only theorem, and the metric-free Euler proof mentioned for Chapter 13 are
not supplied. The PDF's odd-n bound 3n/4 differs from the actual bound
3 * floor(n/4). See Chapter_11_Coverage.md for the complete coverage ledger.

Validation: Lean 4.35.0-rc3; Mathlib commit
738e62bd6df530a89ac01b20e937ad70923a7b96.
No new axioms or proof placeholders are introduced.
-/

namespace chapter11

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace SylvesterGallaiCore

/-- The component of `z` orthogonal to `w`: what is left after subtracting the projection.
Its norm IS the distance from `z` to the line `ℝ ∙ w`. -/
noncomputable def perp (w z : V) : V := z - ((⟪z, w⟫ / ⟪w, w⟫) : ℝ) • w

/-- `perp w` is **linear** in `z`: this is what makes the distance to the line affine,
and it is the pivot of the whole proof. -/
theorem perp_add (w z₁ z₂ : V) : perp w (z₁ + z₂) = perp w z₁ + perp w z₂ := by
  simp only [perp, inner_add_left, add_div, add_smul]
  abel

theorem perp_smul (w : V) (c : ℝ) (z : V) : perp w (c • z) = c • perp w z := by
  simp only [perp, real_inner_smul_left, smul_sub, smul_smul]
  congr 1
  rw [mul_div_assoc]

/-- The orthogonal component of `w` with respect to itself vanishes. -/
theorem perp_self {w : V} (hw : w ≠ 0) : perp w w = 0 := by
  have h : ⟪w, w⟫ ≠ (0 : ℝ) := by
    simpa [real_inner_self_eq_norm_sq] using (norm_ne_zero_iff.mpr hw)
  rw [perp, div_self h, one_smul, sub_self]

/-- **Pythagoras for the orthogonal component.** -/
theorem norm_perp_sq {w : V} (hw : w ≠ 0) (z : V) :
    ‖perp w z‖ ^ 2 = ‖z‖ ^ 2 - ⟪z, w⟫ ^ 2 / ‖w‖ ^ 2 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hww : ⟪w, w⟫ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  rw [← real_inner_self_eq_norm_sq (perp w z), ← real_inner_self_eq_norm_sq z]
  simp only [perp, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hww, real_inner_comm w z]
  field_simp
  ring

/-! ## Kelly's lemma, in vectorial form

Translating `p` to the origin: `a` is the vector from `p` to the projection `q` (so
`‖a‖ = d > 0` and `a` is orthogonal to the direction `e` of the line `L`), and the points
of `L` are `a + t • e`.

`v = a + t • e` with `t ≠ 0` (i.e. `v ≠ q`), and `u = a + (s*t) • e` with `s ∈ [0,1]`
(i.e. `u` lies between `q` and `v`, possibly coinciding with `q`).

Claim: the distance from `u` to the line through `p` and `v` is **strictly smaller** than `d`.
-/

/-- **Kelly's move.** The distance from `q` to the line `p v` is strictly smaller than `d`.

This is where the theorem is decided: `⟪a, w⟫ = ‖a‖² > 0` says that `p` is NOT the foot of
the perpendicular dropped from `q`, and the inequality becomes strict. -/
theorem norm_perp_lt {a e : V} {t : ℝ} (ha : a ≠ 0) (he : e ≠ 0) (ht : t ≠ 0)
    (hperp : ⟪a, e⟫ = (0 : ℝ)) :
    ‖perp (a + t • e) a‖ < ‖a‖ := by
  set w := a + t • e with hw_def
  -- `w ≠ 0`: if it were, `a = -t • e`, but `a ⊥ e` and `a ≠ 0` forbid this
  have hw : w ≠ 0 := by
    intro h
    -- if `w = 0` then `a = -(t • e)`; but `a ⊥ e` forces `t * ‖e‖² = 0`, so `t = 0`
    have hae : a = -(t • e) := by
      have := h; rw [hw_def] at this; linear_combination (norm := module) this
    have hte : t * ‖e‖ ^ 2 = 0 := by
      have h0 : ⟪a, e⟫ = (0 : ℝ) := hperp
      rw [hae, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h0
      linarith
    have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
    exact ht ((mul_eq_zero.mp hte).resolve_right hne)
  have hna : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  -- the key inner product: ⟪a, w⟫ = ‖a‖²
  have haw : ⟪a, w⟫ = ‖a‖ ^ 2 := by
    rw [hw_def, inner_add_right, real_inner_smul_right, hperp,
      real_inner_self_eq_norm_sq]
    ring
  -- Pythagoras on the base: ‖w‖² = ‖a‖² + t²‖e‖², strictly greater than ‖a‖²
  have hnw : ‖w‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2 * ‖e‖ ^ 2 := by
    rw [hw_def, norm_add_sq_real, real_inner_smul_right, hperp, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hpos : (0:ℝ) < t ^ 2 * ‖e‖ ^ 2 := by positivity
  have hlt : ‖a‖ ^ 2 < ‖w‖ ^ 2 := by rw [hnw]; linarith
  have hw2 : (0:ℝ) < ‖w‖ ^ 2 := lt_trans (by positivity) hlt
  -- ‖perp w a‖² = ‖a‖² − ‖a‖⁴/‖w‖² < ‖a‖²
  have key : ‖perp w a‖ ^ 2 < ‖a‖ ^ 2 := by
    rw [norm_perp_sq hw, haw]
    have : (0:ℝ) < (‖a‖ ^ 2) ^ 2 / ‖w‖ ^ 2 := by positivity
    linarith
  nlinarith [norm_nonneg (perp w a), hna, key]

/-- **Kelly's lemma, full form.** Every point `u` between the projection `q` and `v`
is at distance from the line `p v` STRICTLY less than `d = ‖a‖`.

The linearity of `perp` does the rest: `u - p = (1-s) • a + s • w`, and `perp w w = 0`. -/
theorem kelly {a e : V} {t s : ℝ} (ha : a ≠ 0) (he : e ≠ 0) (ht : t ≠ 0)
    (hperp : ⟪a, e⟫ = (0 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖perp (a + t • e) (a + (s * t) • e)‖ < ‖a‖ := by
  set w := a + t • e with hw_def
  have hw : w ≠ 0 := by
    intro h
    -- if `w = 0` then `a = -(t • e)`; but `a ⊥ e` forces `t * ‖e‖² = 0`, so `t = 0`
    have hae : a = -(t • e) := by
      have := h; rw [hw_def] at this; linear_combination (norm := module) this
    have hte : t * ‖e‖ ^ 2 = 0 := by
      have h0 : ⟪a, e⟫ = (0 : ℝ) := hperp
      rw [hae, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h0
      linarith
    have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
    exact ht ((mul_eq_zero.mp hte).resolve_right hne)
  -- the affine decomposition: the point `u` is a combination of `a` (i.e. `q`) and `w` (i.e. `v`)
  have hdecomp : a + (s * t) • e = (1 - s) • a + s • w := by
    rw [hw_def]; module
  rw [hdecomp, perp_add, perp_smul, perp_smul, perp_self hw, smul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s)]
  -- ‖(1-s) • perp w a‖ = (1-s)·‖perp w a‖ ≤ ‖perp w a‖ < ‖a‖
  have hstrict : ‖perp w a‖ < ‖a‖ := norm_perp_lt ha he ht hperp
  have hnn : (0:ℝ) ≤ ‖perp w a‖ := norm_nonneg _
  nlinarith [hnn, hstrict, hs0, hs1]

/-- **The point `u` does not lie on the line `p v`.** Needed so that the new pair really
belongs to the set of configurations.

Argument: if `A + x•e = c • (A + y•e)`, projecting onto `A` (orthogonal to `e`) gives
`(1-c)‖A‖² = 0`, so `c = 1`; and then `x = y`, contradicting the hypothesis. -/
theorem not_mem_line {A e : V} {x y : ℝ} (hA : A ≠ 0) (he : e ≠ 0)
    (hperp : ⟪A, e⟫ = (0 : ℝ)) (hxy : x ≠ y) :
    ¬ ∃ c : ℝ, A + x • e = c • (A + y • e) := by
  rintro ⟨c, hc⟩
  have hAA : ⟪A, A⟫ = ‖A‖ ^ 2 := real_inner_self_eq_norm_sq A
  have hnA : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  have hA2 : ‖A‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnA
  have h1 : ⟪A, A + x • e⟫ = ‖A‖ ^ 2 := by
    rw [inner_add_right, real_inner_smul_right, hperp, hAA]; ring
  have h2 : ⟪A, c • (A + y • e)⟫ = c * ‖A‖ ^ 2 := by
    rw [real_inner_smul_right, inner_add_right, real_inner_smul_right, hperp, hAA]; ring
  have hc1 : c = 1 := by
    have hinner : ⟪A, A + x • e⟫ = ⟪A, c • (A + y • e)⟫ := by rw [hc]
    rw [h1, h2] at hinner
    have hfac : (1 - c) * ‖A‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exact absurd h hA2
  rw [hc1, one_smul] at hc
  have hzero : (x - y) • e = 0 := by
    rw [sub_smul]
    linear_combination (norm := module) hc
  rcases smul_eq_zero.mp hzero with h | h
  · exact hxy (by linarith [sub_eq_zero.mp h])
  · exact he h

end SylvesterGallaiCore

open SylvesterGallaiCore

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace SylvesterGallai

/-- The line through two points. -/
noncomputable def lineThrough (a b : P) : AffineSubspace ℝ P := affineSpan ℝ {a, b}

/-- The distance from the point `p` to the line through `a` and `b`, defined via the core's
`perp`. -/
noncomputable def distToLine (p a b : P) : ℝ := ‖perp (b -ᵥ a : V) (p -ᵥ a : V)‖

/-! ### The dictionary: `perp` ↔ membership in the line -/

/-- `perp w z = 0` exactly when `z` is a multiple of `w`. -/
theorem perp_eq_zero_iff {w z : V} (hw : w ≠ 0) :
    perp w z = 0 ↔ ∃ c : ℝ, z = c • w := by
  constructor
  · intro h
    exact ⟨⟪z, w⟫ / ⟪w, w⟫, by rw [perp, sub_eq_zero] at h; exact h⟩
  · rintro ⟨c, rfl⟩
    have hww : ⟪w, w⟫ ≠ (0 : ℝ) := by
      simpa [real_inner_self_eq_norm_sq] using (norm_ne_zero_iff.mpr hw)
    rw [perp, real_inner_smul_left, mul_div_assoc, div_self hww, mul_one, sub_self]

/-- A point lies on the line through `a` and `b` (with `a ≠ b`) exactly when the vector
`p -ᵥ a` is a multiple of `b -ᵥ a`. -/
theorem mem_lineThrough_iff {p a b : P} :
    p ∈ lineThrough (V := V) a b ↔ ∃ c : ℝ, (p -ᵥ a : V) = c • (b -ᵥ a : V) := by
  have h : p = (p -ᵥ a : V) +ᵥ a := (vsub_vadd p a).symm
  rw [lineThrough, h, vadd_left_mem_affineSpan_pair]
  simp only [vadd_vsub]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- **The dictionary.** The distance to the line vanishes exactly on the points of the line. -/
theorem distToLine_eq_zero_iff {p a b : P} (hab : a ≠ b) :
    distToLine (V := V) p a b = 0 ↔ p ∈ lineThrough (V := V) a b := by
  have hw : (b -ᵥ a : V) ≠ 0 := fun h => hab (by
    have : b = a := by rwa [vsub_eq_zero_iff_eq] at h
    exact this.symm)
  rw [distToLine, norm_eq_zero, perp_eq_zero_iff hw, mem_lineThrough_iff]

/-- The distance is positive for points off the line. -/
theorem distToLine_pos {p a b : P} (hab : a ≠ b) (hp : p ∉ lineThrough (V := V) a b) :
    0 < distToLine (V := V) p a b := by
  rcases (norm_nonneg (perp (b -ᵥ a : V) (p -ᵥ a : V))).lt_or_eq with h | h
  · exact h
  · exact absurd ((distToLine_eq_zero_iff (V := V) hab).mp h.symm) hp

end SylvesterGallai

/-! ### The pigeonhole principle, isolated as a fact about the REALS

This is the point where the proof uses that the field is ℝ and not ℂ: it speaks of SIGN
and of ORDER. Over ℂ the lemma is meaningless — and rightly so, because the
Sylvester–Gallai theorem is **false** in the complex plane (the Hesse configuration).
-/

namespace Pigeonhole

/-- If `x` and `y` have the same sign, are distinct, and `|x| ≤ |y|`, then `y ≠ 0` and
`x / y ∈ [0, 1]`. -/
theorem ratio_mem {x y : ℝ} (hxy : x ≠ y) (habs : |x| ≤ |y|)
    (hsign : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)) :
    y ≠ 0 ∧ 0 ≤ x / y ∧ x / y ≤ 1 := by
  have hy : y ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg x))
    exact hxy (hx0.trans h.symm)
  refine ⟨hy, ?_, ?_⟩
  · rcases hsign with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
    · exact div_nonneg hx0 hy0
    · exact div_nonneg_of_nonpos hx0 hy0
  · rw [div_le_one_iff]
    rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · -- y < 0: we need the branch `b < 0 ∧ b ≤ a`
      refine Or.inr (Or.inr ⟨hy0, ?_⟩)
      rcases hsign with ⟨_, h⟩ | ⟨hx0, _⟩
      · exact absurd hy0 (not_lt.mpr h)
      · rw [abs_of_nonpos hx0, abs_of_neg hy0] at habs; linarith
    · exact absurd hy0 hy
    · -- y > 0: branch `0 < b ∧ a ≤ b`
      refine Or.inl ⟨hy0, ?_⟩
      rcases hsign with ⟨hx0, _⟩ | ⟨_, h⟩
      · rw [abs_of_nonneg hx0, abs_of_pos hy0] at habs; linarith
      · exact absurd hy0 (not_lt.mpr h)

/-- **The pigeonhole principle.** Among three distinct reals one can always find two, `x`
and `y`, with `y ≠ 0` and `x / y ∈ [0, 1]`.

Geometrically: among three distinct points on a line, two lie on the same side of the
projection `q` (the origin of the parameters), with the first **between** `q` and the
second. This is where the proof uses ℝ and not ℂ: it speaks of sign and of order. -/
theorem three {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    ∃ x y : ℝ, (x = t₁ ∨ x = t₂ ∨ x = t₃) ∧ (y = t₁ ∨ y = t₂ ∨ y = t₃) ∧
      x ≠ y ∧ y ≠ 0 ∧ 0 ≤ x / y ∧ x / y ≤ 1 := by
  have key : ∀ u v : ℝ, u ≠ v → ((0 ≤ u ∧ 0 ≤ v) ∨ (u ≤ 0 ∧ v ≤ 0)) →
      ∃ x y : ℝ, (x = u ∨ x = v) ∧ (y = u ∨ y = v) ∧
        x ≠ y ∧ y ≠ 0 ∧ 0 ≤ x / y ∧ x / y ≤ 1 := by
    intro u v huv hs
    rcases le_total |u| |v| with h | h
    · obtain ⟨hy, h1, h2⟩ := ratio_mem huv h hs
      exact ⟨u, v, Or.inl rfl, Or.inr rfl, huv, hy, h1, h2⟩
    · have hs2 : (0 ≤ v ∧ 0 ≤ u) ∨ (v ≤ 0 ∧ u ≤ 0) := by tauto
      obtain ⟨hy, h1, h2⟩ := ratio_mem (Ne.symm huv) h hs2
      exact ⟨v, u, Or.inr rfl, Or.inl rfl, Ne.symm huv, hy, h1, h2⟩
  -- two of the three reals lie in the same closed half
  rcases le_total 0 t₁ with s1 | s1 <;> rcases le_total 0 t₂ with s2 | s2 <;>
    rcases le_total 0 t₃ with s3 | s3
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₂ h12 (Or.inl ⟨s1, s2⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₂ h12 (Or.inl ⟨s1, s2⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₃ h13 (Or.inl ⟨s1, s3⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₂ t₃ h23 (Or.inr ⟨s2, s3⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₂ t₃ h23 (Or.inl ⟨s2, s3⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₃ h13 (Or.inr ⟨s1, s3⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₂ h12 (Or.inr ⟨s1, s2⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩
  · obtain ⟨x, y, hx, hy, h⟩ := key t₁ t₂ h12 (Or.inr ⟨s1, s2⟩)
    exact ⟨x, y, by tauto, by tauto, h⟩

end Pigeonhole

namespace SylvesterGallai

/-! ### The two lemmas that close the bookkeeping -/

/-- If every point of `S` lies on the line through `a` and `b`, then `S` is collinear. -/
theorem collinear_of_subset_line {S : Set P} {a b : P}
    (h : ∀ p ∈ S, p ∈ lineThrough (V := V) a b) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, (b -ᵥ a : V), fun p hp => ?_⟩
  obtain ⟨c, hc⟩ := (mem_lineThrough_iff (V := V)).mp (h p hp)
  exact ⟨c, by rw [← hc, vsub_vadd]⟩

/-- A non-collinear set contains two distinct points. -/
theorem exists_ne_of_not_collinear {S : Set P} (hncol : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  by_contra h
  push Not at h
  -- if all points coincide, `S` is empty or a singleton: collinear in either case
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨a, ha⟩
  · exact hncol (collinear_empty ℝ P)
  · have : S = {a} := by
      apply Set.eq_singleton_iff_unique_mem.mpr ⟨ha, fun x hx => h x hx a ha⟩
    rw [this] at hncol
    exact hncol (collinear_singleton ℝ a)

/-! ### The theorem -/

/-- A line is **ordinary** with respect to `S` if it contains exactly two points of `S`. -/
def IsOrdinaryLine (S : Set P) (a b : P) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ c ∈ S, c ∈ lineThrough (V := V) a b → c = a ∨ c = b

/-- If the line through `a` and `b` is not ordinary, it contains a third point of `S`. -/
theorem exists_third {S : Set P} {a b : P} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (h : ¬ IsOrdinaryLine (V := V) S a b) :
    ∃ c ∈ S, c ∈ lineThrough (V := V) a b ∧ c ≠ a ∧ c ≠ b := by
  by_contra hc
  push Not at hc
  refine h ⟨ha, hb, hab, fun c hcS hcL => ?_⟩
  by_cases hca : c = a
  · exact Or.inl hca
  · exact Or.inr (hc c hcS hcL hca)

/-- **THE SYLVESTER–GALLAI THEOREM.**

A finite set of points, not all collinear, always admits an **ordinary line**: a line
passing through exactly two of them.

Proof (Kelly, 1948). By contradiction, suppose every line through two points contains a
third. Among all triples (point, pair) with the point off the line of the pair — a finite
and nonempty set, because the points are not all collinear — take one of **minimal
distance**. At least three points lie on the line; two of them fall on the same side of
the projection of the point (pigeonhole principle), and from there one builds a triple
that is **strictly closer**. -/
theorem sylvester_gallai (S : Set P) (hfin : S.Finite) (hncol : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, IsOrdinaryLine (V := V) S a b := by
  by_contra hcon
  push Not at hcon
  -- the set of configurations: a point off the line through two other points
  set T : Set (P × P × P) :=
    {x | x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S ∧ x.2.1 ≠ x.2.2 ∧
         x.1 ∉ lineThrough (V := V) x.2.1 x.2.2} with hTdef
  have hTfin : T.Finite := by
    refine Set.Finite.subset (hfin.prod (hfin.prod hfin)) ?_
    rintro ⟨q, c, d⟩ ⟨h1, h2, h3, -, -⟩
    exact ⟨h1, h2, h3⟩
  -- `T` is nonempty: if it were, `S` would be collinear
  have hTne : T.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := exists_ne_of_not_collinear (V := V) hncol
    refine hncol (collinear_of_subset_line (V := V) (a := a₀) (b := b₀) fun q hq => ?_)
    by_contra hqL
    have hmemT : (q, a₀, b₀) ∈ T := ⟨hq, ha₀, hb₀, hab₀, hqL⟩
    rw [hempty] at hmemT
    exact hmemT
  -- the configuration of minimal distance
  obtain ⟨⟨p, a, b⟩, hmem, hmin⟩ :=
    Set.exists_min_image T (fun x => distToLine (V := V) x.1 x.2.1 x.2.2) hTfin hTne
  obtain ⟨hpS, haS, hbS, hab, hpL⟩ := hmem
  -- the third point on the line (from the absurd hypothesis)
  obtain ⟨c, hcS, hcL, hca, hcb⟩ := exists_third (V := V) haS hbS hab (hcon a haS b hbS)
  -- passing to vectors: `e` is the direction, `A` the vector from `p` to the projection
  set e : V := b -ᵥ a with he_def
  have he : e ≠ 0 := by
    rw [he_def, vsub_ne_zero]
    exact fun h => hab h.symm
  set z : V := p -ᵥ a with hz_def
  set A : V := -(perp e z) with hA_def
  have hAperp : ⟪A, e⟫ = (0 : ℝ) := by
    have hne : ⟪e, e⟫ ≠ (0 : ℝ) := by
      simpa [real_inner_self_eq_norm_sq] using (norm_ne_zero_iff.mpr he)
    rw [hA_def, inner_neg_left, perp, inner_sub_left, real_inner_smul_left,
      div_mul_cancel₀ _ hne, sub_self, neg_zero]
  have hAnorm : ‖A‖ = distToLine (V := V) p a b := by rw [hA_def, norm_neg, distToLine]
  have hA : A ≠ 0 := by
    rw [← norm_ne_zero_iff, hAnorm]
    exact ne_of_gt (distToLine_pos (V := V) hab hpL)
  -- `k` is the parameter of the projection
  set k : ℝ := ⟪z, e⟫ / ⟪e, e⟫ with hk_def
  have hAeq : A = k • e - z := by rw [hA_def, perp, hk_def]; abel
  -- every point on the line can be written as `x -ᵥ p = A + t • e`
  have hline : ∀ x : P, x ∈ lineThrough (V := V) a b →
      ∃ t : ℝ, (x -ᵥ p : V) = A + t • e := by
    intro x hx
    obtain ⟨cx, hcx⟩ := (mem_lineThrough_iff (V := V)).mp hx
    refine ⟨cx - k, ?_⟩
    have hxp : (x -ᵥ p : V) = (x -ᵥ a : V) - z := by
      rw [hz_def, vsub_sub_vsub_cancel_right]
    rw [hxp, hcx, hAeq, sub_smul]
    abel
  obtain ⟨ta, hta⟩ := hline a (left_mem_affineSpan_pair ℝ a b)
  obtain ⟨tb, htb⟩ := hline b (right_mem_affineSpan_pair ℝ a b)
  obtain ⟨tc, htc⟩ := hline c hcL
  -- the three parameters are distinct because the points are
  have hinj : ∀ {x y : P} {tx ty : ℝ}, (x -ᵥ p : V) = A + tx • e → (y -ᵥ p : V) = A + ty • e →
      x ≠ y → tx ≠ ty := by
    intro x y tx ty hx hy hxy htxy
    refine hxy (vsub_left_cancel (p := p) ?_)
    rw [hx, hy, htxy]
  have h_ab : ta ≠ tb := hinj hta htb hab
  have h_ac : ta ≠ tc := hinj hta htc (Ne.symm hca)
  have h_bc : tb ≠ tc := hinj htb htc (Ne.symm hcb)
  -- THE PIGEONHOLE PRINCIPLE
  obtain ⟨x, y, hx, hy, hxy, hy0, hs0, hs1⟩ := Pigeonhole.three h_ab h_ac h_bc
  have hpt : ∀ t : ℝ, (t = ta ∨ t = tb ∨ t = tc) →
      ∃ w ∈ S, (w -ᵥ p : V) = A + t • e := by
    rintro t (rfl | rfl | rfl)
    · exact ⟨a, haS, hta⟩
    · exact ⟨b, hbS, htb⟩
    · exact ⟨c, hcS, htc⟩
  obtain ⟨u, huS, hu⟩ := hpt x hx
  obtain ⟨v, hvS, hv⟩ := hpt y hy
  -- KELLY'S MOVE
  have hkelly : ‖perp (A + y • e) (A + (x / y * y) • e)‖ < ‖A‖ :=
    kelly hA he hy0 hAperp hs0 hs1
  rw [div_mul_cancel₀ _ hy0] at hkelly
  -- translation into `distToLine u p v`
  have hdist : distToLine (V := V) u p v = ‖perp (A + y • e) (A + x • e)‖ := by
    rw [distToLine, ← hu, ← hv]
  -- `p ≠ v`: otherwise `A + y•e = 0`, and projecting onto `A` would give `A = 0`
  have hpv : p ≠ v := by
    intro h
    have h0 : A + y • e = 0 := by rw [← hv, ← h, vsub_self]
    have hz0 : ⟪A, A + y • e⟫ = (0 : ℝ) := by rw [h0, inner_zero_right]
    rw [inner_add_right, real_inner_smul_right, hAperp, mul_zero, add_zero,
      real_inner_self_eq_norm_sq] at hz0
    have : ‖A‖ = 0 := by nlinarith [norm_nonneg A]
    exact hA (norm_eq_zero.mp this)
  -- `u` does not lie on the line `p v`: the new triple is legitimate
  have huv : u ∉ lineThrough (V := V) p v := by
    rw [mem_lineThrough_iff (V := V), hu, hv]
    exact not_mem_line hA he hAperp hxy
  have hnew : (u, p, v) ∈ T := ⟨huS, hpS, hvS, hpv, huv⟩
  -- but its distance is smaller than the minimum: contradiction
  have hle := hmin (u, p, v) hnew
  simp only at hle
  rw [hdist] at hle
  rw [hAnorm] at hkelly
  linarith

end SylvesterGallai

end chapter11

open scoped BigOperators
namespace chapter11
namespace Incidence
variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J]
/-- The real incidence coefficient of a point in a block. -/
def coeff (A : J → Finset X) (j : J) (x : X) : ℝ := if x ∈ A j then 1 else 0
/-- Number of blocks through a point. -/
def degree (A : J → Finset X) (x : X) : ℕ := (Finset.univ.filter fun j => x ∈ A j).card
/-- Each pair of distinct points belongs to exactly one indexed block. -/
def PairPartition (A : J → Finset X) : Prop :=
  ∀ x y : X, x ≠ y → ∃! j : J, x ∈ A j ∧ y ∈ A j
omit [Fintype X] [DecidableEq J] in
lemma gram (A : J → Finset X) (hpair : PairPartition A) (x y : X) :
    ∑ j, coeff A j x * coeff A j y = if x = y then (degree A x : ℝ) else 1 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [coeff, degree, Finset.sum_ite, Finset.filter_filter]
  · obtain ⟨j, hj, huniq⟩ := hpair x y hxy
    rw [ite_eq_right hxy, Finset.sum_eq_single j]
    · simp [coeff, hj.1, hj.2]
    · intro k hk hkj
      have : ¬ (x ∈ A k ∧ y ∈ A k) := fun h => hkj (huniq k h)
      simp only [coeff]
      split_ifs <;> simp_all
    · simp
lemma degree_ge_two (A : J → Finset X) (hpair : PairPartition A)
    (hproper : ∀ j, A j ≠ Finset.univ) (hn : 2 ≤ Fintype.card X) (x : X) :
    2 ≤ degree A x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : X, y ≠ x := by
    by_contra h
    push Not at h
    have hc : Fintype.card X ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (h a).trans (h b).symm)
    omega
  obtain ⟨j, hj, _⟩ := hpair x y hy.symm
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ A j := by
    by_contra h
    push Not at h
    exact hproper j (Finset.eq_univ_of_forall h)
  have hxz : x ≠ z := by rintro rfl; exact hz hj.1
  obtain ⟨k, hk, _⟩ := hpair x z hxz
  have hjk : j ≠ k := by rintro rfl; exact hz hk.2
  have hsub : ({j, k} : Finset J) ⊆ Finset.univ.filter (fun l => x ∈ A l) := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> simp [hj.1, hk.1]
  have := Finset.card_le_card hsub
  simpa [degree, hjk] using this
/-- The incidence linear map sends weights on points to their sums on blocks. -/
def incidenceMap (A : J → Finset X) : (X → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun f j := ∑ x, coeff A j x * f x
  map_add' f g := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext j; simp [Finset.mul_sum, mul_left_comm]
omit [DecidableEq J] in
lemma energy (A : J → Finset X) (hpair : PairPartition A) (f : X → ℝ) :
    ∑ j, (incidenceMap A f j)^2 =
      ∑ x, ((degree A x : ℝ) - 1) * (f x)^2 + (∑ x, f x)^2 := by
  classical
  have expand : ∀ j, (incidenceMap A f j)^2 =
      ∑ x, ∑ y, (coeff A j x * coeff A j y) * (f x * f y) := by
    intro j
    simp only [incidenceMap, LinearMap.coe_mk, AddHom.coe_mk, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := J)), ← Finset.sum_mul, gram A hpair]
  have inner : ∀ x, (∑ y, (if x = y then (degree A x : ℝ) else 1) * (f x * f y)) =
      ((degree A x : ℝ) - 1) * (f x)^2 + f x * (∑ y, f y) := by
    intro x
    have term : ∀ y, (if x = y then (degree A x : ℝ) else 1) * (f x * f y) =
        (if y = x then ((degree A x : ℝ) - 1) * (f x)^2 else 0) + f x * f y := by
      intro y
      by_cases h : y = x
      · subst y; simp; ring
      · simp [h, Ne.symm h]
    simp_rw [term]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [inner]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring
/-- Theorem 3, p.78: the de Bruijn–Erdős incidence inequality. Indexed blocks may include
singletons or empty sets, as permitted by the book; all blocks are proper. -/
theorem de_bruijn_erdos (A : J → Finset X) (hn : 3 ≤ Fintype.card X)
    (hproper : ∀ j, A j ≠ Finset.univ) (hpair : PairPartition A) :
    Fintype.card X ≤ Fintype.card J := by
  classical
  have hd : ∀ x, (0 : ℝ) < (degree A x : ℝ) - 1 := by
    intro x
    have := degree_ge_two A hpair hproper (by omega) x
    have hreal : (2 : ℝ) ≤ degree A x := by exact_mod_cast this
    linarith
  have hinj : Function.Injective (incidenceMap A) := by
    apply (incidenceMap A).ker_eq_bot.mp
    apply le_antisymm
    · intro f hf
      have hz : incidenceMap A f = 0 := hf
      have he := energy A hpair f
      rw [hz] at he
      simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at he
      have hnon : ∀ x ∈ Finset.univ, 0 ≤ ((degree A x : ℝ) - 1) * (f x)^2 :=
        fun x _ => mul_nonneg (hd x).le (sq_nonneg _)
      have hs : (∑ x, ((degree A x : ℝ) - 1) * (f x)^2) = 0 := by
        nlinarith [Finset.sum_nonneg hnon, sq_nonneg (∑ x, f x)]
      have hx := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hs
      have hf0 : f = 0 := by
        funext x
        have hh := hx x (Finset.mem_univ x)
        have : (f x)^2 = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hd x))
        simpa using this
      simp [hf0]
    · exact bot_le
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this
end Incidence
end chapter11
namespace chapter11
namespace SylvesterGallai
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
/-- All distinct lines determined by pairs of points in a finite configuration. -/
noncomputable def determinedLines (S : Finset P) : Finset (AffineSubspace ℝ P) := by
  classical
  exact ((S ×ˢ S).filter fun ab => ab.1 ≠ ab.2).image fun ab => lineThrough (V := V) ab.1 ab.2
lemma mem_determinedLines {S : Finset P} {l : AffineSubspace ℝ P} :
    l ∈ determinedLines (V := V) S ↔
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ lineThrough (V := V) a b = l := by
  classical
  simp only [determinedLines, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a,b⟩, ⟨⟨ha,hb⟩,hab⟩,hl⟩
    exact ⟨a,ha,b,hb,hab,hl⟩
  · rintro ⟨a,ha,b,hb,hab,hl⟩
    exact ⟨(a,b),⟨⟨ha,hb⟩,hab⟩,hl⟩
/-- Theorem 2, p.78: a noncollinear finite point set determines at least as many lines
as points. The proof applies Theorem 3 to its point–line incidence structure. -/
theorem number_of_lines (S : Finset P) (hncol : ¬ Collinear ℝ (S : Set P)) :
    S.card ≤ (determinedLines (V := V) S).card := by
  classical
  let X := {p // p ∈ S}
  let J := {l // l ∈ determinedLines (V := V) S}
  let A : J → Finset X := fun l => Finset.univ.filter fun p => p.val ∈ l.val
  have hpair : Incidence.PairPartition A := by
    intro x y hxy
    have hne : x.val ≠ y.val := fun hh => hxy (Subtype.ext hh)
    let l : J := ⟨lineThrough (V := V) x.val y.val,
      mem_determinedLines.mpr ⟨x.val,x.property,y.val,y.property,hne,rfl⟩⟩
    refine ⟨l, ?_, ?_⟩
    · simp [A, l, lineThrough, left_mem_affineSpan_pair, right_mem_affineSpan_pair]
    · intro k hk
      apply Subtype.ext
      have hx : x.val ∈ k.val := (Finset.mem_filter.mp hk.1).2
      have hy : y.val ∈ k.val := (Finset.mem_filter.mp hk.2).2
      obtain ⟨a,ha,b,hb,hab,hl⟩ := mem_determinedLines.mp k.property
      change k.val = lineThrough (V := V) x.val y.val
      rw [← hl] at hx hy ⊢
      exact (affineSpan_pair_eq_of_mem_of_mem_of_ne hx hy hne).symm
  have hproper : ∀ j, A j ≠ Finset.univ := by
    intro j hj
    obtain ⟨a,ha,b,hb,hab,hl⟩ := mem_determinedLines.mp j.property
    apply hncol
    apply collinear_of_subset_line (V := V) (a := a) (b := b)
    intro p hp
    have hmem : (⟨p,hp⟩ : X) ∈ A j := by rw [hj]; exact Finset.mem_univ _
    have h := (Finset.mem_filter.mp hmem).2
    rwa [← hl] at h
  have hn : 3 ≤ Fintype.card X := by
    obtain ⟨a,ha,b,hb,hab⟩ := exists_ne_of_not_collinear (V := V) hncol
    obtain ⟨c,hc,hcL⟩ : ∃ c ∈ (S : Set P), c ∉ lineThrough (V := V) a b := by
      by_contra h
      push Not at h
      exact hncol (collinear_of_subset_line (V := V) h)
    have hca : c ≠ a := by
      intro h
      apply hcL
      rw [h]
      exact left_mem_affineSpan_pair ℝ a b
    have hcb : c ≠ b := by
      intro h
      apply hcL
      rw [h]
      exact right_mem_affineSpan_pair ℝ a b
    have hsub : ({a,b,c} : Finset P) ⊆ S := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    have hh := Finset.card_le_card hsub
    have habc : ({a,b,c} : Finset P).card = 3 := by simp [hab,hca.symm,hcb.symm]
    rw [habc] at hh
    simpa [X] using hh
  have hh := Incidence.de_bruijn_erdos A hn hproper hpair
  simpa [X,J] using hh
end SylvesterGallai
end chapter11
namespace chapter11.Fano
/-- The seven lines in the Fano diagram, with the book's labels shifted down by one. -/
def blocks : Fin 7 → Finset (Fin 7)
  | 0 => {0,1,5}
  | 1 => {0,2,4}
  | 2 => {0,3,6}
  | 3 => {1,2,3}
  | 4 => {1,4,6}
  | 5 => {2,5,6}
  | 6 => {3,4,5}
/-- Each Fano line has three points. Finite verification uses kernel-reduced `decide`. -/
theorem block_card : ∀ j, (blocks j).card = 3 := by decide
/-- Any two distinct points determine exactly one of the seven lines. -/
theorem pair_partition : Incidence.PairPartition blocks := by
  unfold Incidence.PairPartition ExistsUnique
  decide +kernel
/-- Every pair has a third point on its Fano line. -/
theorem third : ∀ x y : Fin 7, x ≠ y →
    ∃ z : Fin 7, z ≠ x ∧ z ≠ y ∧ ∃ j, x ∈ blocks j ∧ y ∈ blocks j ∧ z ∈ blocks j := by
  decide +kernel
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
/-- The Fano incidence structure cannot be realized by seven distinct noncollinear
real points with every indicated triple collinear (p.77). Noncollinearity excludes the
degenerate drawing putting all seven points on one line. -/
theorem not_realizable (f : Fin 7 → P) (hinj : Function.Injective f)
    (hncol : ¬ Collinear ℝ (Set.range f))
    (hblocks : ∀ j, Collinear ℝ (f '' (blocks j : Set (Fin 7)))) : False := by
  obtain ⟨a,ha,b,hb,hab⟩ := SylvesterGallai.sylvester_gallai (V := V)
    (Set.range f) (Set.finite_range f) hncol
  obtain ⟨x,rfl⟩ := ha
  obtain ⟨y,rfl⟩ := hb
  have hxy : x ≠ y := fun h => hab.2.2.1 (congrArg f h)
  obtain ⟨z,hzx,hzy,j,hx,hy,hz⟩ := third x y hxy
  have hzL : f z ∈ SylvesterGallai.lineThrough (V := V) (f x) (f y) :=
    (hblocks j).mem_affineSpan_of_mem_of_ne ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩
      ⟨z,hz,rfl⟩ hab.2.2.1
  rcases hab.2.2.2 (f z) (Set.mem_range_self z) hzL with h | h
  · exact hzx (hinj h)
  · exact hzy (hinj h)
end chapter11.Fano


open scoped BigOperators
namespace chapter11
namespace GrahamPollak
variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J]
/-- Coefficient of membership in one side of a bipartite block. -/
def coeff (A : J → Finset X) (j : J) (x : X) : ℝ := if x ∈ A j then 1 else 0
/-- An edge belongs to a complete bipartite block in either orientation. -/
def Covers (L R : J → Finset X) (j : J) (x y : X) : Prop :=
  (x ∈ L j ∧ y ∈ R j) ∨ (x ∈ R j ∧ y ∈ L j)
/-- The vertex sides are disjoint and every unordered edge is covered exactly once. -/
def BipartitePartition (L R : J → Finset X) : Prop :=
  (∀ j, Disjoint (L j) (R j)) ∧
    ∀ x y : X, x ≠ y → ∃! j : J, Covers L R j x y
omit [Fintype X] [DecidableEq J] in
lemma coefficient (L R : J → Finset X) (h : BipartitePartition L R) (x y : X) :
    ∑ j, (coeff L j x * coeff R j y + coeff R j x * coeff L j y) =
      if x = y then 0 else 1 := by
  classical
  have term : ∀ j, coeff L j x * coeff R j y + coeff R j x * coeff L j y =
      if Covers L R j x y then 1 else 0 := by
    intro j
    have hd := Finset.disjoint_left.mp (h.1 j)
    simp only [coeff, Covers]
    split_ifs <;> simp_all
  simp_rw [term]
  by_cases hxy : x = y
  · subst y
    have hn : ∀ j, ¬ Covers L R j x x := by
      intro j hh
      rcases hh with hh | hh
      · exact Finset.disjoint_left.mp (h.1 j) hh.1 hh.2
      · exact Finset.disjoint_left.mp (h.1 j) hh.2 hh.1
    simp [hn]
  · obtain ⟨j, hj, huniq⟩ := h.2 x y hxy
    rw [ite_eq_right hxy, Finset.sum_eq_single j]
    · simp [hj]
    · intro k hk hkj
      have hn : ¬ Covers L R k x y := fun hh => hkj (huniq k hh)
      simp [hn]
    · simp
omit [DecidableEq J] in
/-- The quadratic identity (1), written over ordered pairs and including the diagonal.
This avoids an arbitrary ordering on the vertex type. -/
lemma quadratic_identity (L R : J → Finset X) (h : BipartitePartition L R) (f : X → ℝ) :
    (∑ x, f x)^2 = (∑ x, (f x)^2) +
      2 * ∑ j, (∑ x, coeff L j x * f x) * (∑ y, coeff R j y * f y) := by
  classical
  have hexpand : ∀ j,
      2 * ((∑ x, coeff L j x * f x) * (∑ y, coeff R j y * f y)) =
      ∑ x, ∑ y, (coeff L j x * coeff R j y + coeff R j x * coeff L j y) * (f x * f y) := by
    intro j
    have hswap : (∑ x, coeff R j x * f x) * (∑ y, coeff L j y * f y) =
        (∑ x, coeff L j x * f x) * (∑ y, coeff R j y * f y) := mul_comm _ _
    calc
      _ = (∑ x, coeff L j x * f x) * (∑ y, coeff R j y * f y) +
          (∑ x, coeff R j x * f x) * (∑ y, coeff L j y * f y) := by rw [hswap]; ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
  have he : 2 * ∑ j, (∑ x, coeff L j x * f x) * (∑ y, coeff R j y * f y) =
      ∑ x, ∑ y, (if x = y then (0 : ℝ) else 1) * (f x * f y) := by
    rw [Finset.mul_sum]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ (α := J)), ← Finset.sum_mul,
      coefficient L R h]
  rw [he]
  have ht : ∀ x y : X, f x * f y =
      (if y = x then (f x)^2 else 0) + (if x = y then (0 : ℝ) else 1) * (f x * f y) := by
    intro x y
    by_cases hxy : y = x
    · subst y; simp [pow_two]
    · simp [hxy, Ne.symm hxy]
  calc
    (∑ x, f x)^2 = ∑ x, ∑ y, f x * f y := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      calc
        _ = ∑ x, ∑ y, ((if y = x then (f x)^2 else 0) +
            (if x = y then (0 : ℝ) else 1) * (f x * f y)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.sum_congr rfl (fun y hy => ht x y)
        _ = _ := by simp [Finset.sum_add_distrib]
/-- The linear constraints in Tverberg's proof. -/
def constraintMap (L : J → Finset X) : (X → ℝ) →ₗ[ℝ] (ℝ × (J → ℝ)) where
  toFun f := (∑ x, f x, fun j => ∑ x, coeff L j x * f x)
  map_add' f g := by
    ext <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext <;> simp [Finset.mul_sum, mul_left_comm]
omit [DecidableEq J] in
/-- Theorem 4, pp.79–80: Graham–Pollak, with no assumption that n is positive.
The equivalent natural-number formulation is n ≤ m + 1. -/
theorem graham_pollak (L R : J → Finset X) (h : BipartitePartition L R) :
    Fintype.card X ≤ Fintype.card J + 1 := by
  classical
  have hinj : Function.Injective (constraintMap L) := by
    apply (constraintMap L).ker_eq_bot.mp
    apply le_antisymm
    · intro f hf
      have hz : constraintMap L f = 0 := hf
      have hs : (∑ x, f x) = 0 := congrArg Prod.fst hz
      have hl : ∀ j, (∑ x, coeff L j x * f x) = 0 := fun j =>
        congrFun (congrArg Prod.snd hz) j
      have he := quadratic_identity L R h f
      simp only [hs, hl, zero_pow (by decide : 2 ≠ 0), zero_mul,
        Finset.sum_const_zero, mul_zero, add_zero] at he
      have hf0 : f = 0 := by
        funext x
        have hx := (Finset.sum_eq_zero_iff_of_nonneg
          (fun y (_ : y ∈ Finset.univ) => sq_nonneg (f y))).mp he.symm x (Finset.mem_univ x)
        simpa using hx
      simp [hf0]
    · exact bot_le
  have hh := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Nat.add_comm] using hh
end GrahamPollak
end chapter11
namespace chapter11.GrahamPollak
/-- The j-th star has its centre at vertex j and its leaves at the later vertices.
There are n stars on n+1 vertices, including n=0. -/
def starLeft (n : ℕ) (j : Fin n) : Finset (Fin (n+1)) := {j.castSucc}
def starRight (n : ℕ) (j : Fin n) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun x => j.val < x.val
/-- The star construction on p.79 is an edge partition. -/
theorem star_partition (n : ℕ) : BipartitePartition (starLeft n) (starRight n) := by
  constructor
  · intro j
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [starLeft, Finset.mem_singleton] at hx
    subst x
    simp [starRight] at hy
  · intro x y hxy
    have hne : x.val ≠ y.val := fun hh => hxy (Fin.ext hh)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · let j : Fin n := ⟨x.val, by omega⟩
      refine ⟨j, Or.inl ?_, ?_⟩
      · simpa [starLeft, starRight, j] using hlt
      · intro k hk
        rcases hk with hk | hk
        · have hx : x = k.castSucc := by simpa [starLeft] using hk.1
          apply Fin.ext
          simpa [j] using congrArg Fin.val hx.symm
        · have hy : y = k.castSucc := by simpa [starLeft] using hk.2
          have hx : k.val < x.val := (Finset.mem_filter.mp hk.1).2
          have hyv := congrArg Fin.val hy
          simp only [Fin.val_castSucc] at hyv
          omega
    · let j : Fin n := ⟨y.val, by omega⟩
      refine ⟨j, Or.inr ?_, ?_⟩
      · simpa [starLeft, starRight, j] using hlt
      · intro k hk
        rcases hk with hk | hk
        · have hx : x = k.castSucc := by simpa [starLeft] using hk.1
          have hy : k.val < y.val := (Finset.mem_filter.mp hk.2).2
          have hxv := congrArg Fin.val hx
          simp only [Fin.val_castSucc] at hxv
          omega
        · have hy : y = k.castSucc := by simpa [starLeft] using hk.2
          apply Fin.ext
          simpa [j] using congrArg Fin.val hy.symm
/-- The n−1 bound is attained for every nonempty complete graph. -/
theorem sharp (n : ℕ) :
    ∃ L R : Fin n → Finset (Fin (n+1)), BipartitePartition L R :=
  ⟨starLeft n, starRight n, star_partition n⟩
end chapter11.GrahamPollak


namespace chapter11.GraphAppendix
/-- Complete graph on n vertices (p.80). -/
abbrev complete (n : ℕ) : SimpleGraph (Fin n) := ⊤
/-- Complete bipartite graph, with its two vertex classes kept disjoint (p.81). -/
abbrev completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) :=
  _root_.completeBipartiteGraph (Fin m) (Fin n)
/-- Path graph on n vertices (p.81). -/
abbrev path (n : ℕ) := SimpleGraph.pathGraph n
/-- Cycle graph on n vertices; the book's cycle examples start at n=3. -/
abbrev cycle (n : ℕ) := SimpleGraph.cycleGraph n
variable {X Y : Type*}
/-- Adjacency and incidence use Mathlib's unordered edges (`Sym2`). -/
abbrev Adjacent (G : SimpleGraph X) (x y : X) := G.Adj x y
/-- A vertex is incident to an edge if it is one of that unordered edge's endpoints. -/
def Incident (G : SimpleGraph X) (x : X) (e : G.edgeSet) : Prop := x ∈ e.val
/-- Simple graphs have no loops and store at most one edge for each unordered pair. -/
theorem no_loops (G : SimpleGraph X) (x : X) : ¬ G.Adj x x := G.irrefl
/-- The vertex bijection of a graph isomorphism determines the edge bijection. -/
abbrev Isomorphism (G : SimpleGraph X) (H : SimpleGraph Y) := G ≃g H
/-- A subgraph records its vertex subset and exactly its chosen edges. -/
abbrev Subgraph (G : SimpleGraph X) := G.Subgraph
/-- An induced graph retains every ambient edge between its chosen vertices. -/
abbrev induced (G : SimpleGraph X) (s : Set X) := G.induce s
abbrev Connected (G : SimpleGraph X) := G.Connected
abbrev Component (G : SimpleGraph X) := G.ConnectedComponent
abbrev Clique (G : SimpleGraph X) (s : Set X) := G.IsClique s
abbrev Independent (G : SimpleGraph X) (s : Set X) := G.IsIndepSet s
abbrev Forest (G : SimpleGraph X) := G.IsAcyclic
abbrev Tree (G : SimpleGraph X) := G.IsTree
abbrev Bipartite (G : SimpleGraph X) := G.IsBipartite
/-- Complete graphs have n choose 2 edges (p.80). -/
theorem complete_edge_count (n : ℕ) : (complete n).edgeFinset.card = n.choose 2 := by
  simpa [complete] using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
/-- Complete bipartite graphs have m+n vertices (p.81). -/
theorem completeBipartite_vertex_count (m n : ℕ) : Fintype.card (Fin m ⊕ Fin n) = m+n := by simp
/-- Complete bipartite graphs have mn edges (p.81), in the library's extended natural
cardinality. For these finite graphs this is the ordinary cardinality. -/
theorem completeBipartite_edge_count (m n : ℕ) :
    (completeBipartite m n).edgeSet.encard = (m : ℕ∞) * n := by
  simpa [completeBipartite] using
    (SimpleGraph.encard_edgeSet_completeBipartiteGraph (W₁ := Fin m) (W₂ := Fin n))
/-- Path adjacency is precisely adjacency of consecutive vertex labels. -/
theorem path_adjacency (n : ℕ) (x y : Fin n) :
    (path n).Adj x y ↔ x.val+1 = y.val ∨ y.val+1 = x.val := SimpleGraph.pathGraph_adj
/-- Paths with at least one vertex are connected. -/
theorem path_connected (n : ℕ) : (path (n+1)).Connected := SimpleGraph.pathGraph_connected n
/-- A clique induces a complete graph, as in the appendix. -/
theorem clique_iff_complete_induced (G : SimpleGraph X) (s : Set X) :
    Clique G s ↔ induced G s = ⊤ := G.induce_eq_top.symm
/-- The book's definition of tree agrees with Mathlib's tree structure. -/
theorem tree_iff (G : SimpleGraph X) : Tree G ↔ Connected G ∧ Forest G := by
  constructor
  · intro h; exact ⟨h.connected,h.isAcyclic⟩
  · rintro ⟨hc,hf⟩; exact ⟨hc,hf⟩
/-- Each connected component of a forest is a tree. -/
theorem component_of_forest_is_tree (G : SimpleGraph X) (h : Forest G) (c : Component G) :
    c.toSimpleGraph.IsTree := h.isTree_connectedComponent c
end chapter11.GraphAppendix
namespace chapter11.GraphAppendix
variable {X Y : Type*}
/-- The induced edge bijection required by the book's definition of isomorphism. -/
abbrev edgeBijection {G : SimpleGraph X} {H : SimpleGraph Y} (e : Isomorphism G H) :=
  e.mapEdgeSet
/-- An independent set induces the empty graph. -/
theorem independent_iff_empty_induced (G : SimpleGraph X) (s : Set X) :
    Independent G s ↔ induced G s = ⊥ := by
  constructor
  · intro h
    apply SimpleGraph.ext
    funext x y
    apply propext
    simp only [induced, SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    by_cases hxy : x.val = y.val
    · simp [hxy]
    · exact h x.property y.property hxy
  · intro h x hx y hy hxy hAdj
    have : (induced G s).Adj ⟨x,hx⟩ ⟨y,hy⟩ := hAdj
    simp [h] at this
/-- A graph is bipartite precisely when its vertices split into two independent sets.
The sets are disjoint and cover all vertices, including isolated ones. -/
theorem bipartite_iff_partition (G : SimpleGraph X) :
    Bipartite G ↔ ∃ s t : Set X, Disjoint s t ∧ s ∪ t = Set.univ ∧
      Independent G s ∧ Independent G t := by
  classical
  constructor
  · rintro ⟨c,hc⟩
    let s : Set X := {x | c x = 0}
    let t : Set X := {x | c x = 1}
    refine ⟨s,t,?_,?_,?_,?_⟩
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hx' : c x = 0 := hx
      have hy' : c x = 1 := hy
      have : (0 : Fin 2) = 1 := hx'.symm.trans hy'
      exact (by decide : (0 : Fin 2) ≠ 1) this
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      change c x = 0 ∨ c x = 1
      have hv := (c x).isLt
      simp only [Fin.ext_iff]
      omega
    · intro x hx y hy hxy hadj
      exact hc hadj ((show c x = 0 from hx).trans (show c y = 0 from hy).symm)
    · intro x hx y hy hxy hadj
      exact hc hadj ((show c x = 1 from hx).trans (show c y = 1 from hy).symm)
  · rintro ⟨s,t,hd,hcover,hs,ht⟩
    apply SimpleGraph.IsBipartiteWith.isBipartite (s := s) (t := t)
    refine ⟨hd,?_⟩
    intro x y hadj
    have hx : x ∈ s ∨ x ∈ t := by rw [← Set.mem_union,hcover]; trivial
    have hy : y ∈ s ∨ y ∈ t := by rw [← Set.mem_union,hcover]; trivial
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact False.elim (hs hx hy (G.ne_of_adj hadj) hadj)
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr ⟨hx,hy⟩
    · exact False.elim (ht hx hy (G.ne_of_adj hadj) hadj)
end chapter11.GraphAppendix


namespace chapter11.Incidence
variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J]
/-- The graph formulation of Theorem 3 (p.79): each edge of the complete graph
belongs to exactly one of the complete graphs induced on the vertex blocks. -/
def CliqueEdgePartition (A : J → Finset X) : Prop :=
  ∀ x y : X, (⊤ : SimpleGraph X).Adj x y → ∃! j, x ∈ A j ∧ y ∈ A j
omit [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J] in
/-- An unordered edge in K_n is exactly a pair of distinct vertices, so the incidence
and clique decomposition formulations are identical. -/
theorem clique_partition_iff (A : J → Finset X) :
    CliqueEdgePartition A ↔ PairPartition A := by
  simp only [CliqueEdgePartition, PairPartition, SimpleGraph.top_adj]
omit [Fintype X] [Fintype J] [DecidableEq X] [DecidableEq J] in
/-- Every induced vertex block is a clique of the complete graph. -/
theorem block_is_clique (A : J → Finset X) (j : J) :
    (⊤ : SimpleGraph X).IsClique (A j : Set X) := by
  intro x hx y hy hxy
  exact hxy
/-- Decomposing K_n into proper cliques requires at least n cliques (p.79). -/
theorem clique_decomposition_bound (A : J → Finset X) (hn : 3 ≤ Fintype.card X)
    (hproper : ∀ j, A j ≠ Finset.univ) (hpartition : CliqueEdgePartition A) :
    Fintype.card X ≤ Fintype.card J :=
  de_bruijn_erdos A hn hproper ((clique_partition_iff A).mp hpartition)
end chapter11.Incidence

namespace chapter11.GraphAppendix
variable {X : Type*}
/-- Every vertex belongs to its own connected component. -/
theorem components_cover (G : SimpleGraph X) (x : X) :
    ∃ c : G.ConnectedComponent, x ∈ c.supp := by
  exact ⟨G.connectedComponentMk x, by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩
/-- Distinct connected components have disjoint vertex sets. -/
theorem components_disjoint (G : SimpleGraph X) :
    Pairwise fun c c' : G.ConnectedComponent => Disjoint c.supp c'.supp :=
  G.pairwise_disjoint_supp_connectedComponent
end chapter11.GraphAppendix
