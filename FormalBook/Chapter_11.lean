/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Daniele Cappello
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

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

## TODO
  - Theorem 2.
    - proof
  Theorem 3.
    - proof
  Theorem 4.
    - proof
  Appendix: Basic graph concepts
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
  push_neg at h
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
  push_neg at hc
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
  push_neg at hcon
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
