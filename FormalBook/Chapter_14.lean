/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original skeleton author: Moritz Firsching.
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cauchy's rigidity theorem

Partial formalization of Chapter 14 of *Proofs from THE BOOK*, sixth edition.

The proved results cover the planar and spherical triangle cases of Cauchy's arm lemma,
including strict comparison and the equality criterion, and the metric calculation in
its final inductive branch. The polygon and polyhedron definitions state the remaining
arm and rigidity obligations as propositions; they do not prove those results.

The convex-polygon induction, spherical-link argument, and full rigidity proof remain
unfinished. Flexible polyhedra and Sabitov's volume theorem are not formalized here.

Arm-lemma reference: I. J. Schoenberg and S. K. Zaremba, *On Cauchy's lemma concerning
convex polygons*, Canadian J. Math. 19 (1967), 1062–1071,
[doi:10.4153/CJM-1967-096-4](https://doi.org/10.4153/CJM-1967-096-4).
-/

public section
noncomputable section

namespace Chapter14

open scoped RealInnerProductSpace EuclideanGeometry

/-! ## The planar triangle case (printed page 96) -/

/-- The planar cosine rule, in scalar form. -/
def PlanarCosineRule (a b c γ : ℝ) : Prop :=
  c * c = a * a + b * b - 2 * a * b * Real.cos γ

/-- Opening a triangle's included angle cannot decrease its opposite side. -/
theorem planar_triangle_le {a b c d γ δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ ≤ δ)
    (hcosc : PlanarCosineRule a b c γ)
    (hcosd : PlanarCosineRule a b d δ) : c ≤ d := by
  have ht := Real.cos_le_cos_of_nonneg_of_le_pi hγ hδ hγδ
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * a * b by positivity)
  dsimp [PlanarCosineRule] at hcosc hcosd
  nlinarith

/-- Strict opening strictly increases the opposite side when the fixed sides are positive. -/
theorem planar_triangle_lt {a b c d γ δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ < δ)
    (hcosc : PlanarCosineRule a b c γ)
    (hcosd : PlanarCosineRule a b d δ) : c < d := by
  have ht := Real.cos_lt_cos_of_nonneg_of_le_pi hγ hδ hγδ
  have hm := mul_lt_mul_of_pos_left ht (show 0 < 2 * a * b by positivity)
  dsimp [PlanarCosineRule] at hcosc hcosd
  nlinarith

/-- Equality holds exactly when the included angles agree. -/
theorem planar_triangle_eq_iff {a b c d γ δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ ≤ δ)
    (hcosc : PlanarCosineRule a b c γ)
    (hcosd : PlanarCosineRule a b d δ) : c = d ↔ γ = δ := by
  constructor
  · intro heq
    by_contra hne
    have hlt := planar_triangle_lt ha hb hc hd hγ hδ (lt_of_le_of_ne hγδ hne)
      hcosc hcosd
    exact (ne_of_lt hlt) heq
  · intro heq
    dsimp [PlanarCosineRule] at hcosc hcosd
    rw [heq] at hcosc
    nlinarith

section EuclideanTriangles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Actual Euclidean triangles satisfy the scalar cosine rule. -/
theorem planar_cosine_rule (p q r : V) :
    PlanarCosineRule (dist p q) (dist r q) (dist p r)
      (EuclideanGeometry.angle p q r) := by
  exact EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    p q r

/-- The n = 3 case of the planar arm lemma, using actual points and angles. -/
theorem planar_arm_three (p q r p' q' r' : V)
    (hpq : p ≠ q) (hrq : r ≠ q)
    (hleft : dist p q = dist p' q') (hright : dist r q = dist r' q')
    (hangle : EuclideanGeometry.angle p q r ≤ EuclideanGeometry.angle p' q' r') :
    dist p r ≤ dist p' r' ∧
      (dist p r = dist p' r' ↔
        EuclideanGeometry.angle p q r = EuclideanGeometry.angle p' q' r') := by
  have hc := planar_cosine_rule p q r
  have hd := planar_cosine_rule p' q' r'
  rw [← hleft, ← hright] at hd
  exact ⟨planar_triangle_le (dist_nonneg) (dist_nonneg) (dist_nonneg) (dist_nonneg)
    (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _) hangle hc hd,
    planar_triangle_eq_iff (dist_pos.mpr hpq) (dist_pos.mpr hrq)
      (dist_nonneg) (dist_nonneg) (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _) hangle hc hd⟩

/-- The strict form of the geometric planar triangle case. -/
theorem planar_arm_three_strict (p q r p' q' r' : V)
    (hpq : p ≠ q) (hrq : r ≠ q)
    (hleft : dist p q = dist p' q') (hright : dist r q = dist r' q')
    (hangle : EuclideanGeometry.angle p q r < EuclideanGeometry.angle p' q' r') :
    dist p r < dist p' r' := by
  have hd := planar_cosine_rule p' q' r'
  rw [← hleft, ← hright] at hd
  exact planar_triangle_lt (dist_pos.mpr hpq) (dist_pos.mpr hrq)
    (dist_nonneg) (dist_nonneg) (EuclideanGeometry.angle_nonneg _ _ _)
    (EuclideanGeometry.angle_le_pi _ _ _) hangle (planar_cosine_rule p q r) hd

end EuclideanTriangles

/-! ## Spherical triangles: minor great-circle arcs on the unit sphere -/

section SphericalTriangles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For unit vectors, the vector angle is the length of the minor great-circle arc. -/
def arcLength (p q : V) : ℝ := InnerProductGeometry.angle p q

/-- The projection of p onto the tangent plane to the unit sphere at q. -/
def tangent (q p : V) : V := p - inner ℝ p q • q

/-- The angle between the initial directions of the minor arcs q--p and q--r. -/
def sphericalAngle (p q r : V) : ℝ :=
  InnerProductGeometry.angle (tangent q p) (tangent q r)

/-- The norm of the tangent projection is the sine of the minor arc length. -/
theorem norm_tangent {p q : V} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (h0 : 0 < arcLength p q) (hpi : arcLength p q < Real.pi) :
    ‖tangent q p‖ = Real.sin (arcLength p q) := by
  have hpp : inner ℝ p p = 1 := by simp [hp]
  have hqq : inner ℝ q q = 1 := by simp [hq]
  have hqp : inner ℝ q p = inner ℝ p q := real_inner_comm p q
  have hcos : inner ℝ p q = Real.cos (arcLength p q) :=
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hp hq
  have hsquare : ‖tangent q p‖ * ‖tangent q p‖ =
      1 - Real.cos (arcLength p q) ^ 2 := by
    rw [← real_inner_self_eq_norm_mul_norm]
    simp only [tangent, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hpp, hqq, hqp, hcos]
    ring
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hid := Real.sin_sq_add_cos_sq (arcLength p q)
  nlinarith [norm_nonneg (tangent q p)]

/-- The spherical cosine rule, derived for actual unit-sphere points. -/
theorem spherical_cosine_rule {p q r : V}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (ha0 : 0 < arcLength p q) (hapi : arcLength p q < Real.pi)
    (hb0 : 0 < arcLength r q) (hbpi : arcLength r q < Real.pi) :
    Real.cos (arcLength p r) =
      Real.cos (arcLength p q) * Real.cos (arcLength r q) +
      Real.sin (arcLength p q) * Real.sin (arcLength r q) *
        Real.cos (sphericalAngle p q r) := by
  have hqq : inner ℝ q q = 1 := by simp [hq]
  have hqr : inner ℝ q r = inner ℝ r q := real_inner_comm r q
  have hinner : inner ℝ (tangent q p) (tangent q r) =
      inner ℝ p r - inner ℝ p q * inner ℝ r q := by
    simp only [tangent, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hqq, hqr]
    ring
  have hangle := InnerProductGeometry.cos_angle_mul_norm_mul_norm (tangent q p) (tangent q r)
  rw [norm_tangent hp hq ha0 hapi, norm_tangent hr hq hb0 hbpi] at hangle
  have hpr := InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hp hr
  have hpq := InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hp hq
  have hrq := InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hr hq
  change inner ℝ (tangent q p) (tangent q r) =
    inner ℝ p r - inner ℝ p q * inner ℝ r q at hinner
  change Real.cos (sphericalAngle p q r) *
    (Real.sin (arcLength p q) * Real.sin (arcLength r q)) =
      inner ℝ (tangent q p) (tangent q r) at hangle
  change inner ℝ p r = Real.cos (arcLength p r) at hpr
  change inner ℝ p q = Real.cos (arcLength p q) at hpq
  change inner ℝ r q = Real.cos (arcLength r q) at hrq
  rw [hpr, hpq, hrq] at hinner
  rw [← hangle] at hinner
  linear_combination -hinner

end SphericalTriangles

/-- Spherical cosine rule, in scalar form. -/
def SphericalCosineRule (a b c γ : ℝ) : Prop :=
  Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ

/-- Scalar weak opening comparison for minor-arc spherical triangles. -/
theorem spherical_triangle_le {a b c d γ δ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi) (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc : c ≤ Real.pi) (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ ≤ δ)
    (hcosc : SphericalCosineRule a b c γ)
    (hcosd : SphericalCosineRule a b d δ) : c ≤ d := by
  have hk : 0 < Real.sin a * Real.sin b :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi ha0 hapi)
      (Real.sin_pos_of_pos_of_lt_pi hb0 hbpi)
  have ht := Real.cos_le_cos_of_nonneg_of_le_pi hγ hδ hγδ
  have hm := mul_le_mul_of_nonneg_left ht hk.le
  dsimp [SphericalCosineRule] at hcosc hcosd
  by_contra hnot
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi hd hc (lt_of_not_ge hnot)
  nlinarith

/-- Scalar strict opening comparison for minor-arc spherical triangles. -/
theorem spherical_triangle_lt {a b c d γ δ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi) (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc : c ≤ Real.pi) (hd : 0 ≤ d)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ < δ)
    (hcosc : SphericalCosineRule a b c γ)
    (hcosd : SphericalCosineRule a b d δ) : c < d := by
  have hk : 0 < Real.sin a * Real.sin b :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi ha0 hapi)
      (Real.sin_pos_of_pos_of_lt_pi hb0 hbpi)
  have ht := Real.cos_lt_cos_of_nonneg_of_le_pi hγ hδ hγδ
  have hm := mul_lt_mul_of_pos_left ht hk
  dsimp [SphericalCosineRule] at hcosc hcosd
  by_contra hnot
  have hle := Real.cos_le_cos_of_nonneg_of_le_pi hd hc (le_of_not_gt hnot)
  nlinarith

/-- Equality in spherical triangle comparison occurs exactly for unchanged angles. -/
theorem spherical_triangle_eq_iff {a b c d γ δ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi) (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc0 : 0 ≤ c) (hcpi : c ≤ Real.pi) (hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi)
    (hγ : 0 ≤ γ) (hδ : δ ≤ Real.pi) (hγδ : γ ≤ δ)
    (hcosc : SphericalCosineRule a b c γ)
    (hcosd : SphericalCosineRule a b d δ) : c = d ↔ γ = δ := by
  constructor
  · intro heq
    by_contra hne
    have hlt := spherical_triangle_lt ha0 hapi hb0 hbpi hcpi hd0 hγ hδ
      (lt_of_le_of_ne hγδ hne) hcosc hcosd
    exact (ne_of_lt hlt) heq
  · intro heq
    apply Real.injOn_cos ⟨hc0, hcpi⟩ ⟨hd0, hdpi⟩
    dsimp [SphericalCosineRule] at hcosc hcosd
    rw [heq] at hcosc
    linarith

section SphericalTriangleComparison

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The n = 3 case of the spherical arm lemma for actual unit-sphere vertices.
Positive, non-antipodal fixed sides are necessary for the strict equality criterion. -/
theorem spherical_arm_three (p q r p' q' r' : V)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hp' : ‖p'‖ = 1) (hq' : ‖q'‖ = 1) (hr' : ‖r'‖ = 1)
    (ha0 : 0 < arcLength p q) (hapi : arcLength p q < Real.pi)
    (hb0 : 0 < arcLength r q) (hbpi : arcLength r q < Real.pi)
    (hleft : arcLength p q = arcLength p' q')
    (hright : arcLength r q = arcLength r' q')
    (hangle : sphericalAngle p q r ≤ sphericalAngle p' q' r') :
    arcLength p r ≤ arcLength p' r' ∧
      (arcLength p r = arcLength p' r' ↔
        sphericalAngle p q r = sphericalAngle p' q' r') := by
  have hc : SphericalCosineRule (arcLength p q) (arcLength r q)
      (arcLength p r) (sphericalAngle p q r) :=
    spherical_cosine_rule hp hq hr ha0 hapi hb0 hbpi
  have hd : SphericalCosineRule (arcLength p' q') (arcLength r' q')
      (arcLength p' r') (sphericalAngle p' q' r') :=
    spherical_cosine_rule hp' hq' hr' (by rwa [← hleft]) (by rwa [← hleft])
      (by rwa [← hright]) (by rwa [← hright])
  rw [← hleft, ← hright] at hd
  exact ⟨spherical_triangle_le ha0 hapi hb0 hbpi
    (InnerProductGeometry.angle_le_pi _ _) (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
    hangle hc hd,
    spherical_triangle_eq_iff ha0 hapi hb0 hbpi
      (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      hangle hc hd⟩

/-- Strict angle growth strictly increases the missing minor arc. -/
theorem spherical_arm_three_strict (p q r p' q' r' : V)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hp' : ‖p'‖ = 1) (hq' : ‖q'‖ = 1) (hr' : ‖r'‖ = 1)
    (ha0 : 0 < arcLength p q) (hapi : arcLength p q < Real.pi)
    (hb0 : 0 < arcLength r q) (hbpi : arcLength r q < Real.pi)
    (hleft : arcLength p q = arcLength p' q')
    (hright : arcLength r q = arcLength r' q')
    (hangle : sphericalAngle p q r < sphericalAngle p' q' r') :
    arcLength p r < arcLength p' r' := by
  have hcomparison := spherical_arm_three p q r p' q' r' hp hq hr hp' hq' hr'
    ha0 hapi hb0 hbpi hleft hright hangle.le
  apply lt_of_le_of_ne hcomparison.1
  intro heq
  exact (ne_of_lt hangle) (hcomparison.2.mp heq)

end SphericalTriangleComparison

/-! ## The final metric calculation in the induction (printed page 97) -/

/-- The four scalar relations in the last branch imply strict endpoint growth.
This verifies the calculation, not the geometric construction supplying its hypotheses. -/
theorem stuck_branch {old moved new first diagonal newDiagonal : ℝ}
    (hmove : old < moved) (hcollinear : first + moved = diagonal)
    (hinduction : diagonal ≤ newDiagonal)
    (htriangle : newDiagonal ≤ first + new) : old < new := by
  linarith

/-- The same calculation for actual points in any metric space. -/
theorem stuck_branch_metric {M : Type*} [PseudoMetricSpace M]
    (q₁ q₂ qn qnStar q₁' q₂' qn' : M)
    (hmove : dist q₁ qn < dist q₁ qnStar)
    (hcollinear : dist q₂ q₁ + dist q₁ qnStar = dist q₂ qnStar)
    (hinduction : dist q₂ qnStar ≤ dist q₂' qn')
    (hfirst : dist q₂ q₁ = dist q₂' q₁') : dist q₁ qn < dist q₁' qn' := by
  have htriangle := dist_triangle q₂' q₁' qn'
  rw [← hfirst] at htriangle
  exact stuck_branch hmove hcollinear hinduction htriangle

/-! ## Geometric statement obligations — NOT asserted as theorems

All polygon vertices are distinct, in boundary order; the polygons below are
strictly convex. Great-circle arcs on the sphere are minor arcs, and spherical
polygons lie in an open hemisphere. Degenerate intermediate polygons in the
book's induction still require a separate weak-convexity development.
-/

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Cyclic successor, with no global nonzero-size typeclass assumption. -/
def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Cyclic predecessor. -/
def previous {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Signed planar area, positive when r lies to the left of the directed line p--q. -/
def orient (p q r : Plane) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- A strictly convex planar n-gon, oriented counterclockwise. -/
structure PlanarPolygon (n : ℕ) where
  atLeastThree : 3 ≤ n
  point : Fin n → Plane
  injective : Function.Injective point
  leftOfEdges : ∀ i j, j ≠ i → j ≠ next i →
    0 < orient (point i) (point (next i)) (point j)

namespace PlanarPolygon

def first {n : ℕ} (P : PlanarPolygon n) : Fin n := ⟨0, by have := P.atLeastThree; omega⟩
def last {n : ℕ} (P : PlanarPolygon n) : Fin n := ⟨n - 1, by have := P.atLeastThree; omega⟩
def side {n : ℕ} (P : PlanarPolygon n) (i : Fin n) : ℝ :=
  dist (P.point i) (P.point (next i))
def angle {n : ℕ} (P : PlanarPolygon n) (i : Fin n) : ℝ :=
  EuclideanGeometry.angle (P.point (previous i)) (P.point i) (P.point (next i))
def closing {n : ℕ} (P : PlanarPolygon n) : ℝ :=
  dist (P.point P.first) (P.point P.last)

end PlanarPolygon

/-- The full planar arm lemma for strictly convex polygons: an UNPROVED obligation.
The fixed sides exclude the closing edge. Only the n-2 internal arm angles are compared. -/
def PlanarArmStatement : Prop :=
  ∀ (n : ℕ) (P Q : PlanarPolygon n),
    (∀ i : Fin n, i.val + 1 < n → P.side i = Q.side i) →
    (∀ i : Fin n, 0 < i.val → i.val + 1 < n → P.angle i ≤ Q.angle i) →
    P.closing ≤ Q.closing ∧
      (P.closing = Q.closing ↔
        ∀ i : Fin n, 0 < i.val → i.val + 1 < n → P.angle i = Q.angle i)

/-- Scalar triple product: its sign specifies a side of an oriented great circle. -/
def triple (p q r : Space) : ℝ :=
  p 0 * (q 1 * r 2 - q 2 * r 1) -
    p 1 * (q 0 * r 2 - q 2 * r 0) +
    p 2 * (q 0 * r 1 - q 1 * r 0)

/-- A strictly convex spherical n-gon in an open hemisphere, with minor arcs. -/
structure SphericalPolygon (n : ℕ) where
  atLeastThree : 3 ≤ n
  point : Fin n → Space
  injective : Function.Injective point
  unit : ∀ i, ‖point i‖ = 1
  hemisphere : ∃ h : Space, ∀ i, 0 < inner ℝ h (point i)
  leftOfEdges : ∀ i j, j ≠ i → j ≠ next i →
    0 < triple (point i) (point (next i)) (point j)

namespace SphericalPolygon

def first {n : ℕ} (P : SphericalPolygon n) : Fin n := ⟨0, by have := P.atLeastThree; omega⟩
def last {n : ℕ} (P : SphericalPolygon n) : Fin n := ⟨n - 1, by have := P.atLeastThree; omega⟩
def side {n : ℕ} (P : SphericalPolygon n) (i : Fin n) : ℝ :=
  arcLength (P.point i) (P.point (next i))
def angle {n : ℕ} (P : SphericalPolygon n) (i : Fin n) : ℝ :=
  sphericalAngle (P.point (previous i)) (P.point i) (P.point (next i))
def closing {n : ℕ} (P : SphericalPolygon n) : ℝ :=
  arcLength (P.point P.first) (P.point P.last)

end SphericalPolygon

/-- The full spherical arm lemma: an UNPROVED obligation, not a theorem. -/
def SphericalArmStatement : Prop :=
  ∀ (n : ℕ) (P Q : SphericalPolygon n),
    (∀ i : Fin n, i.val + 1 < n → P.side i = Q.side i) →
    (∀ i : Fin n, 0 < i.val → i.val + 1 < n → P.angle i ≤ Q.angle i) →
    P.closing ≤ Q.closing ∧
      (P.closing = Q.closing ↔
        ∀ i : Fin n, 0 < i.val → i.val + 1 < n → P.angle i = Q.angle i)

/-! ### Convex polyhedra and the rigidity statement

A polyhedron is the convex hull of its finite, distinctly labeled vertices,
with nonempty interior in Euclidean three-space. Faces are indexed by their
vertex sets. The correspondence is the identity on labels after relabeling
one polyhedron; no geometric conclusion is built into that correspondence.
-/

structure ConvexPolyhedron (n : ℕ) where
  vertex : Fin n → Space
  injective : Function.Injective vertex
  verticesExtreme : (convexHull ℝ (Set.range vertex)).extremePoints ℝ = Set.range vertex
  fullDimensional : (interior (convexHull ℝ (Set.range vertex))).Nonempty

namespace ConvexPolyhedron

/-- The actual solid, rather than an abstract graph. -/
def solid {n : ℕ} (P : ConvexPolyhedron n) : Set Space :=
  convexHull ℝ (Set.range P.vertex)

/-- A face is empty or the full maximizer set of a linear functional on the vertices.
The zero functional supplies the entire polyhedron's face. -/
def IsFace {n : ℕ} (P : ConvexPolyhedron n) (f : Finset (Fin n)) : Prop :=
  f = ∅ ∨ ∃ (l : Space →L[ℝ] ℝ) (c : ℝ),
    (∀ i, l (P.vertex i) ≤ c) ∧ ∀ i, i ∈ f ↔ l (P.vertex i) = c

/-- Facets are maximal proper nonempty faces. -/
def IsFacet {n : ℕ} (P : ConvexPolyhedron n) (f : Finset (Fin n)) : Prop :=
  P.IsFace f ∧ f.Nonempty ∧ f ≠ Finset.univ ∧
    ∀ g, P.IsFace g → f ⊆ g → g ≠ Finset.univ → g = f

/-- Equality of the labeled face lattices encodes the chosen combinatorial equivalence. -/
def Correspond {n : ℕ} (P Q : ConvexPolyhedron n) : Prop :=
  ∀ f, P.IsFace f ↔ Q.IsFace f

/-- Corresponding facets are congruent by Euclidean isometries respecting the vertex labels. -/
def FacetsCongruent {n : ℕ} (P Q : ConvexPolyhedron n) : Prop :=
  ∀ f, P.IsFacet f → ∃ e : Space ≃ᵢ Space, ∀ i ∈ f, e (P.vertex i) = Q.vertex i

/-- One global Euclidean isometry realizes the prescribed vertex correspondence. -/
def Congruent {n : ℕ} (P Q : ConvexPolyhedron n) : Prop :=
  ∃ e : Space ≃ᵢ Space, ∀ i, e (P.vertex i) = Q.vertex i

/-- Unit outward normal of a facet, specified without a choice operation. -/
def OutwardNormal {n : ℕ} (P : ConvexPolyhedron n)
    (f : Finset (Fin n)) (u : Space) : Prop :=
  ‖u‖ = 1 ∧ ∃ c : ℝ,
    (∀ i, inner ℝ u (P.vertex i) ≤ c) ∧
    (∀ i, i ∈ f ↔ inner ℝ u (P.vertex i) = c)

/-- Distinct facets sharing at least two vertices share an edge. -/
def AdjacentFacets {n : ℕ} (P : ConvexPolyhedron n)
    (f g : Finset (Fin n)) : Prop :=
  P.IsFacet f ∧ P.IsFacet g ∧ f ≠ g ∧ 2 ≤ (f ∩ g).card

end ConvexPolyhedron

/-- Cauchy's global congruence conclusion: an UNPROVED known-theorem obligation. -/
def CauchyRigidityStatement : Prop :=
  ∀ (n : ℕ) (P Q : ConvexPolyhedron n),
    P.Correspond Q → P.FacetsCongruent Q → P.Congruent Q

/-- The source's dihedral-angle conclusion: an UNPROVED known-theorem obligation.
For outward normals u and v, the interior dihedral angle is pi minus their vector angle. -/
def CauchyDihedralStatement : Prop :=
  ∀ (n : ℕ) (P Q : ConvexPolyhedron n),
    P.Correspond Q → P.FacetsCongruent Q →
    ∀ (f g : Finset (Fin n)), P.AdjacentFacets f g →
    ∀ (u v u' v' : Space),
      P.OutwardNormal f u → P.OutwardNormal g v →
      Q.OutwardNormal f u' → Q.OutwardNormal g v' →
      Real.pi - InnerProductGeometry.angle u v =
        Real.pi - InnerProductGeometry.angle u' v'

end Chapter14
