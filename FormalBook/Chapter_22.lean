/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib

/-!
# One square and an odd number of triangles

Formalization of the whole chapter "One square and an odd number of triangles" of
*Proofs from THE BOOK*, in a single file. The sections below are, in order:

* Definitions: triangles, their areas, the unit square and dissections.
* Valuations and coloring: properties (i)–(iv), `v (1/n) = 1` for odd `n`, the three-coloring
  of the plane, **Lemma 1** (`Chapter22.lemma1`) and the **Corollary**.
* The parity principle behind the counting argument of Lemma 2 (`Chapter22.sum_edgeSum_eq`).
* **Lemma 2** (`Chapter22.lemma2`, `Chapter22.exists_isRainbow`), with observations (A) and (B).
* Appendix: extending valuations (`Chapter22.isValuationRing_iff`, `Chapter22.zorns_lemma`,
  `Chapter22.maximal_subring_isValuationRing`, `Chapter22.exists_valuation_half_gt_one`).
* **Monsky's Theorem** (`Chapter22.monsky`, `Chapter22.monsky_fin`).
* The `p`-adic value examples.
* Areas as Lebesgue measure, and `Chapter22.monsky_equal_area`.
* The even case: dissections into an even number of triangles of equal area.
-/

@[expose] public section

/-!
# Triangles and dissections of the unit square

Basic definitions for Chapter 22: triangles in the plane `ℝ × ℝ`, their (signed) areas, and
dissections of the unit square into finitely many triangles.
-/


namespace Chapter22

/-- A triangle in the plane, given by its three vertices. -/
abbrev Triangle := Fin 3 → ℝ × ℝ

/-- The `2 × 2` determinant of two vectors in the plane. -/
def det2 (u w : ℝ × ℝ) : ℝ := u.1 * w.2 - u.2 * w.1

/-- Twice the signed area of a triangle. -/
def triDet (t : Triangle) : ℝ := det2 (t 1 - t 0) (t 2 - t 0)

/-- The area of a triangle (shoelace formula). -/
noncomputable def triArea (t : Triangle) : ℝ := |triDet t| / 2

/-- The closed triangular region spanned by a triangle. -/
def triRegion (t : Triangle) : Set (ℝ × ℝ) := convexHull ℝ (Set.range t)

/-- The unit square `S = [0, 1]²`. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1

/-- A dissection of the unit square into finitely many (non-degenerate) triangles: the triangles
cover the square and have pairwise disjoint interiors. -/
structure IsDissection {ι : Type*} [Fintype ι] (T : ι → Triangle) : Prop where
  nondegenerate : ∀ i, triDet (T i) ≠ 0
  iUnion_eq : ⋃ i, triRegion (T i) = unitSquare
  disjoint_interior : ∀ i j, i ≠ j → Disjoint (interior (triRegion (T i)))
    (interior (triRegion (T j)))

end Chapter22

/-!
# One square and an odd number of triangles: valuations and the three-coloring

This file formalizes the first part of Chapter 22 of *Proofs from THE BOOK*:

* elementary facts about non-Archimedean valuations (in Mathlib, `Valuation K Γ₀` with values
  in a linearly ordered commutative group with zero is exactly the book's notion of a
  non-Archimedean valuation with values in an ordered abelian group, see the appendix),
* the fact that a valuation with `v (1/2) > 1` satisfies `v (1/n) = 1` for odd `n`,
* the three-coloring of the plane,
* **Lemma 1** (the `v`-value of the determinant of a blue, a green and a red point is `≥ 1`),
* the **Corollary** (any line receives at most two colors, and the area of a rainbow triangle
  is neither `0` nor `1/n` for odd `n`).
-/


namespace Chapter22

open Matrix

section Valuations

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ### Elementary properties of non-Archimedean valuations -/

/-- `v(1) = 1`. -/
theorem valuation_one (v : Valuation K Γ₀) : v 1 = 1 := v.map_one

/-- `v(-1) = 1`. -/
theorem valuation_neg_one (v : Valuation K Γ₀) : v (-1) = 1 := by simp

/-- `v(-x) = v(x)`. -/
theorem valuation_neg (v : Valuation K Γ₀) (x : K) : v (-x) = v x := v.map_neg x

/-- `v(x⁻¹) = v(x)⁻¹`. -/
theorem valuation_inv (v : Valuation K Γ₀) (x : K) : v x⁻¹ = (v x)⁻¹ := v.map_inv x

/-- Property (iv): `v(x + y) = max {v(x), v(y)}` whenever `v(x) ≠ v(y)`. -/
theorem valuation_add_eq_max_of_ne (v : Valuation K Γ₀) {x y : K} (h : v x ≠ v y) :
    v (x + y) = max (v x) (v y) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [v.map_add_eq_of_lt_right h, max_eq_right h.le]
  · rw [v.map_add_eq_of_lt_left h, max_eq_left h.le]

/-- If `v(x) < 1` and `x ≠ 0` then `v(x⁻¹) = v(x)⁻¹ > 1`. -/
theorem one_lt_valuation_inv (v : Valuation K Γ₀) {x : K} (hx : x ≠ 0) (h : v x < 1) :
    1 < v x⁻¹ := by
  rw [v.map_inv]
  exact (one_lt_inv₀ (v.pos_iff.2 hx)).2 h

/-- The values of natural numbers are at most `1`. -/
theorem valuation_natCast_le_one (v : Valuation K Γ₀) (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

/-- `v(1/2) > 1` means that `v(2) < 1`. -/
theorem valuation_two_lt_one (v : Valuation K Γ₀) (hv : 1 < v (1 / 2)) : v (2 : K) < 1 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  rw [one_div, v.map_inv] at hv
  exact (one_lt_inv₀ (v.pos_iff.2 h2)).1 hv

/-- Any valuation with `v(1/2) > 1` satisfies `v(n) = 1` for odd integers `n`. -/
theorem valuation_odd_eq_one (v : Valuation K Γ₀) (hv : 1 < v (1 / 2)) {n : ℕ} (hn : Odd n) :
    v (n : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h2k : v (2 * (k : K)) < 1 := by
    rw [v.map_mul]
    calc v 2 * v (k : K) ≤ v 2 * 1 := mul_le_mul_right (valuation_natCast_le_one v k) _
      _ = v 2 := mul_one _
      _ < 1 := valuation_two_lt_one v hv
  push_cast
  rw [add_comm, v.map_add_eq_of_lt_left (by simpa using h2k), v.map_one]

/-- Any valuation with `v(1/2) > 1` satisfies `v(1/n) = 1` for odd integers `n`. -/
theorem valuation_one_div_odd_eq_one (v : Valuation K Γ₀) (hv : 1 < v (1 / 2)) {n : ℕ}
    (hn : Odd n) : v (1 / (n : K)) = 1 := by
  rw [one_div, v.map_inv, valuation_odd_eq_one v hv hn, inv_one]

end Valuations

/-! ### The coloring of the plane -/

/-- The three colors. -/
inductive Color
  | blue
  | green
  | red
  deriving DecidableEq

instance : Fintype Color where
  elems := {.blue, .green, .red}
  complete c := by cases c <;> simp

open Color

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation ℝ Γ₀)

/-- The coloring of the plane associated with a valuation `v`: the color of `(x, y)` records
the first coordinate of `(x, y, 1)` in which the maximal `v`-value occurs. -/
noncomputable def color (p : ℝ × ℝ) : Color :=
  if v p.2 ≤ v p.1 ∧ v 1 ≤ v p.1 then blue
  else if v p.1 < v p.2 ∧ v 1 ≤ v p.2 then green
  else red

theorem color_eq_blue_iff (p : ℝ × ℝ) :
    color v p = blue ↔ v p.2 ≤ v p.1 ∧ v 1 ≤ v p.1 := by
  unfold color; split_ifs with h1 h2 <;> simp_all

theorem color_eq_green_iff (p : ℝ × ℝ) :
    color v p = green ↔ v p.1 < v p.2 ∧ v 1 ≤ v p.2 := by
  unfold color; split_ifs with h1 h2 <;> simp_all

theorem color_eq_red_iff (p : ℝ × ℝ) :
    color v p = red ↔ v p.1 < v 1 ∧ v p.2 < v 1 := by
  unfold color
  split_ifs with h1 h2
  · simp only [false_iff, not_and, not_lt]; intro h; exact absurd h1.2 (not_le.2 h)
  · simp only [false_iff, not_and, not_lt]
    intro _; exact h2.2
  · simp only [true_iff]
    rcases le_or_gt (v 1) (v p.1) with hx | hx
    · have hxy : v p.1 < v p.2 := lt_of_not_ge fun h => h1 ⟨h, hx⟩
      exact absurd ⟨hxy, hx.trans hxy.le⟩ h2
    · refine ⟨hx, lt_of_not_ge fun hy => ?_⟩
      rcases lt_or_ge (v p.1) (v p.2) with hxy | hxy
      · exact h2 ⟨hxy, hy⟩
      · exact absurd (hy.trans hxy) (not_le.2 hx)

/-! ### Lemma 1 -/

/-- The determinant of Lemma 1, with rows `(x, y, 1)`. -/
noncomputable def det3 (pb pg pr : ℝ × ℝ) : ℝ :=
  Matrix.det !![pb.1, pb.2, 1; pg.1, pg.2, 1; pr.1, pr.2, 1]

theorem det3_eq (pb pg pr : ℝ × ℝ) : det3 pb pg pr =
    pb.1 * pg.2 - pb.1 * pr.2 - pb.2 * pg.1 + pb.2 * pr.1 + pg.1 * pr.2 - pg.2 * pr.1 := by
  simp [det3, Matrix.det_fin_three]

/-- **Lemma 1** (precise form): for a blue point `pb`, a green point `pg` and a red point `pr`,
the `v`-value of the determinant is the `v`-value of the main diagonal term `xb * yg`, which is
at least `1`. -/
theorem valuation_det3_eq (pb pg pr : ℝ × ℝ) (hb : color v pb = blue)
    (hg : color v pg = green) (hr : color v pr = red) :
    v (det3 pb pg pr) = v (pb.1 * pg.2) ∧ 1 ≤ v (pb.1 * pg.2) := by
  rw [color_eq_blue_iff, v.map_one] at hb
  rw [color_eq_green_iff, v.map_one] at hg
  rw [color_eq_red_iff, v.map_one] at hr
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hr1, hr2⟩ := hr
  have hxb : 0 < v pb.1 := lt_of_lt_of_le zero_lt_one hb2
  have hyg : 0 < v pg.2 := lt_of_lt_of_le zero_lt_one hg2
  have hm : 1 ≤ v (pb.1 * pg.2) := by rw [v.map_mul]; exact one_le_mul hb2 hg2
  have hyg_le : v pg.2 ≤ v pb.1 * v pg.2 := by
    calc v pg.2 = 1 * v pg.2 := (one_mul _).symm
      _ ≤ v pb.1 * v pg.2 := mul_le_mul_left hb2 _
  have hxb_le : v pb.1 ≤ v pb.1 * v pg.2 := by
    calc v pb.1 = v pb.1 * 1 := (mul_one _).symm
      _ ≤ v pb.1 * v pg.2 := mul_le_mul_right hg2 _
  -- the five other terms have strictly smaller value
  have t1 : v (pb.1 * pr.2) < v (pb.1 * pg.2) := by
    rw [v.map_mul, v.map_mul]
    calc v pb.1 * v pr.2 < v pb.1 * 1 := mul_lt_mul_of_pos_left hr2 hxb
      _ = v pb.1 := mul_one _
      _ ≤ _ := hxb_le
  have t2 : v (pb.2 * pg.1) < v (pb.1 * pg.2) := by
    rw [v.map_mul, v.map_mul]
    calc v pb.2 * v pg.1 ≤ v pb.1 * v pg.1 := mul_le_mul_left hb1 _
      _ < v pb.1 * v pg.2 := mul_lt_mul_of_pos_left hg1 hxb
  have t3 : v (pb.2 * pr.1) < v (pb.1 * pg.2) := by
    rw [v.map_mul, v.map_mul]
    calc v pb.2 * v pr.1 ≤ v pb.1 * v pr.1 := mul_le_mul_left hb1 _
      _ < v pb.1 * 1 := mul_lt_mul_of_pos_left hr1 hxb
      _ = v pb.1 := mul_one _
      _ ≤ _ := hxb_le
  have t4 : v (pg.1 * pr.2) < v (pb.1 * pg.2) := by
    rw [v.map_mul, v.map_mul]
    calc v pg.1 * v pr.2 ≤ v pg.1 * 1 := mul_le_mul_right hr2.le _
      _ = v pg.1 := mul_one _
      _ < v pg.2 := hg1
      _ ≤ _ := hyg_le
  have t5 : v (pg.2 * pr.1) < v (pb.1 * pg.2) := by
    rw [v.map_mul, v.map_mul]
    calc v pg.2 * v pr.1 < v pg.2 * 1 := mul_lt_mul_of_pos_left hr1 hyg
      _ = v pg.2 := mul_one _
      _ ≤ _ := hyg_le
  have hrest : v (-(pb.1 * pr.2) - pb.2 * pg.1 + pb.2 * pr.1 + pg.1 * pr.2 - pg.2 * pr.1)
      < v (pb.1 * pg.2) := by
    simp only [sub_eq_add_neg]
    refine v.map_add_lt (v.map_add_lt (v.map_add_lt (v.map_add_lt ?_ ?_) ?_) ?_) ?_ <;>
      simpa only [Valuation.map_neg]
  refine ⟨?_, hm⟩
  have : det3 pb pg pr = pb.1 * pg.2 +
      (-(pb.1 * pr.2) - pb.2 * pg.1 + pb.2 * pr.1 + pg.1 * pr.2 - pg.2 * pr.1) := by
    rw [det3_eq]; ring
  rw [this, v.map_add_eq_of_lt_left hrest]

/-- **Lemma 1.** For any blue point `pb`, green point `pg` and red point `pr`, the `v`-value of
the determinant `det ((xb, yb, 1), (xg, yg, 1), (xr, yr, 1))` is at least `1`. -/
theorem lemma1 (pb pg pr : ℝ × ℝ) (hb : color v pb = blue)
    (hg : color v pg = green) (hr : color v pr = red) :
    1 ≤ v (Matrix.det !![pb.1, pb.2, 1; pg.1, pg.2, 1; pr.1, pr.2, 1]) := by
  have := valuation_det3_eq v pb pg pr hb hg hr
  rw [← det3, this.1]; exact this.2

/-! ### The Corollary -/

theorem det3_eq_zero_of_collinear {a b c : ℝ × ℝ} (h : Collinear ℝ {a, b, c}) :
    det3 a b c = 0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, w, hw⟩ := h
  obtain ⟨r₁, rfl⟩ := hw a (by simp)
  obtain ⟨r₂, rfl⟩ := hw b (by simp)
  obtain ⟨r₃, rfl⟩ := hw c (by simp)
  simp only [det3_eq, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- The determinant of Lemma 1 of three points of different colors is nonzero. -/
theorem det3_ne_zero (pb pg pr : ℝ × ℝ) (hb : color v pb = blue)
    (hg : color v pg = green) (hr : color v pr = red) : det3 pb pg pr ≠ 0 := by
  intro h
  have := (valuation_det3_eq v pb pg pr hb hg hr)
  rw [← this.1, h, v.map_zero] at this
  exact absurd this.2 (not_le.2 zero_lt_one)

/-- **Corollary**, part 1: any line of the plane receives at most two different colors.
We state it for arbitrary collinear sets of points: they never receive all three colors. -/
theorem collinear_color_image_ne_univ {s : Set (ℝ × ℝ)} (hs : Collinear ℝ s) :
    color v '' s ≠ Set.univ := by
  intro h
  have hmem : ∀ c : Color, ∃ p ∈ s, color v p = c := fun c => by
    have : c ∈ color v '' s := h ▸ Set.mem_univ c
    simpa using this
  obtain ⟨pb, hpb, hb⟩ := hmem blue
  obtain ⟨pg, hpg, hg⟩ := hmem green
  obtain ⟨pr, hpr, hr⟩ := hmem red
  have hcol : Collinear ℝ {pb, pg, pr} :=
    hs.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
  exact det3_ne_zero v pb pg pr hb hg hr (det3_eq_zero_of_collinear hcol)

/-- **Corollary**, part 1 (cardinality form): a collinear set of points receives at most two
different colors. -/
theorem collinear_ncard_color_image_le_two {s : Set (ℝ × ℝ)} (hs : Collinear ℝ s) :
    (color v '' s).ncard ≤ 2 := by
  have hne := collinear_color_image_ne_univ v hs
  have hlt : (color v '' s).ncard < (Set.univ : Set Color).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_univ_iff.2 hne)
  have : (Set.univ : Set Color).ncard = 3 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]; rfl
  omega

/-- Three collinear points never have three different colors. -/
theorem not_injective_color_of_collinear {t : Triangle} (h : Collinear ℝ (Set.range t)) :
    ¬ Function.Injective (fun i => color v (t i)) := by
  intro hinj
  apply collinear_color_image_ne_univ v h
  have hsurj : Function.Surjective (fun i => color v (t i)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, rfl⟩ |>.2
  ext c
  simp only [Set.mem_univ, iff_true]
  obtain ⟨i, hi⟩ := hsurj c
  exact ⟨t i, ⟨i, rfl⟩, hi⟩

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-- A triangle is a *rainbow triangle* if its three vertices have three different colors. -/
def IsRainbow (t : Triangle) : Prop := Function.Injective (fun i => color v (t i))

theorem triDet_eq_det3 (t : Triangle) : triDet t = det3 (t 0) (t 1) (t 2) := by
  simp only [triDet, det2, det3_eq, Prod.fst_sub, Prod.snd_sub]; ring

/-- The `v`-value of (twice the signed area of) a rainbow triangle is at least `1`. -/
theorem one_le_valuation_triDet {t : Triangle} (ht : IsRainbow v t) : 1 ≤ v (triDet t) := by
  have hsurj : Function.Surjective (fun i => color v (t i)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨ht, rfl⟩ |>.2
  obtain ⟨ib, hb⟩ := hsurj blue
  obtain ⟨ig, hg⟩ := hsurj green
  obtain ⟨ir, hr⟩ := hsurj red
  simp only at hb hg hr
  have key := (valuation_det3_eq v _ _ _ hb hg hr)
  rw [← key.1] at key
  have hdet : det3 (t ib) (t ig) (t ir) = triDet t ∨ det3 (t ib) (t ig) (t ir) = -triDet t := by
    have hbg : ib ≠ ig := fun h => by rw [h, hg] at hb; exact absurd hb (by decide)
    have hbr : ib ≠ ir := fun h => by rw [h, hr] at hb; exact absurd hb (by decide)
    have hgr : ig ≠ ir := fun h => by rw [h, hr] at hg; exact absurd hg (by decide)
    clear key hb hg hr hsurj
    rw [triDet_eq_det3]
    rcases fin3_cases ib with rfl | rfl | rfl <;> rcases fin3_cases ig with rfl | rfl | rfl <;>
      rcases fin3_cases ir with rfl | rfl | rfl <;> simp only [det3_eq] <;>
      first
      | exact absurd rfl hbg
      | exact absurd rfl hbr
      | exact absurd rfl hgr
      | (left; trivial)
      | (left; ring1)
      | (right; ring1)
  rcases hdet with h | h
  · rw [← h]; exact key.2
  · rw [← neg_neg (triDet t), Valuation.map_neg, ← h]; exact key.2

/-- **Corollary**, part 2: the area of a rainbow triangle cannot be `0`. -/
theorem triArea_ne_zero_of_isRainbow {t : Triangle} (ht : IsRainbow v t) : triArea t ≠ 0 := by
  have h := one_le_valuation_triDet v ht
  intro h0
  have : triDet t = 0 := by
    unfold triArea at h0; simpa using h0
  rw [this, v.map_zero] at h
  exact absurd h (not_le.2 zero_lt_one)

/-- **Corollary**, part 3: if `v(1/2) > 1`, the area of a rainbow triangle cannot be `1/n` for
odd `n`. -/
theorem triArea_ne_one_div_odd_of_isRainbow (hv : 1 < v (1 / 2)) {t : Triangle}
    (ht : IsRainbow v t) {n : ℕ} (hn : Odd n) : triArea t ≠ 1 / n := by
  have h := one_le_valuation_triDet v ht
  intro harea
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.pos.ne'
  have habs : |triDet t| = 2 * (1 / n) := by
    unfold triArea at harea; linarith
  have hval : v (triDet t) = v (2 * (1 / (n : ℝ))) := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ 2 * (1 / n)) |>.1 habs with h' | h'
    · rw [h']
    · rw [h', Valuation.map_neg]
  rw [hval, v.map_mul, valuation_one_div_odd_eq_one v hv hn, mul_one] at h
  exact absurd h (not_le.2 (valuation_two_lt_one v hv))

end Chapter22

/-!
# A parity principle for families of triangles

This file contains the geometric heart of the counting argument in the proof of Lemma 2 of
Chapter 22 ("Every dissection of the unit square into finitely many triangles contains an odd
number of rainbow triangles").

The book counts "red-blue segments" between neighboring vertices of the dissection. We
formalize this counting argument in the following general form: let `F` be a `ZMod 2`-valued
function on pairs of points which is *additive along lines*, i.e. `F a c = F a b + F b c`
whenever `a, b, c` are collinear. (The red-blue indicator is such a function, precisely because
every line receives at most two colors.) For a triangle `T` let `∂F(T)` be the sum of `F` over
the three sides of `T`. If two finite families of non-degenerate triangles `A` and `B` cover
every generic point of the plane equally often modulo `2`, then
`∑_{T ∈ A} ∂F(T) = ∑_{T ∈ B} ∂F(T)`.

The proof decomposes `F` along each line into point contributions, and then compares, for every
vertex `x` and every line through `x`, the number of triangle sides on that line ending at `x`,
by looking at four generic points close to `x` on both sides of the line.
-/


namespace Chapter22

open Filter Topology

/-! ### Barycentric coordinates -/

/-- The `k`-th barycentric coordinate of `z` with respect to the triangle `t`. -/
noncomputable def bary (t : Triangle) (k : Fin 3) (z : ℝ × ℝ) : ℝ :=
  det2 (t (k + 1) - z) (t (k + 2) - z) / triDet t

/-- The linear part of the `k`-th barycentric coordinate. -/
noncomputable def baryLin (t : Triangle) (k : Fin 3) (w : ℝ × ℝ) : ℝ :=
  det2 w (t (k + 1) - t (k + 2)) / triDet t

theorem bary_add (t : Triangle) (k : Fin 3) (x w : ℝ × ℝ) :
    bary t k (x + w) = bary t k x + baryLin t k w := by
  simp only [bary, baryLin, det2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  ring

theorem baryLin_add (t : Triangle) (k : Fin 3) (w w' : ℝ × ℝ) :
    baryLin t k (w + w') = baryLin t k w + baryLin t k w' := by
  simp only [baryLin, det2, Prod.fst_add, Prod.snd_add]
  ring

theorem baryLin_smul (t : Triangle) (k : Fin 3) (c : ℝ) (w : ℝ × ℝ) :
    baryLin t k (c • w) = c * baryLin t k w := by
  simp only [baryLin, det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem sum_bary {t : Triangle} (ht : triDet t ≠ 0) (z : ℝ × ℝ) : ∑ k, bary t k z = 1 := by
  simp only [Fin.sum_univ_three, bary]
  rw [← add_div, ← add_div, div_eq_one_iff_eq ht]
  simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
  ring

theorem sum_baryLin (t : Triangle) (w : ℝ × ℝ) : ∑ k, baryLin t k w = 0 := by
  simp only [Fin.sum_univ_three, baryLin]
  rw [← add_div, ← add_div]
  simp only [det2, Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
  ring

theorem sum_bary_smul {t : Triangle} (ht : triDet t ≠ 0) (z : ℝ × ℝ) :
    ∑ k, bary t k z • t k = z := by
  ext
  · simp only [Fin.sum_univ_three, bary, Prod.fst_add, Prod.smul_fst, smul_eq_mul, det2,
      Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
    field_simp
    simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub]
    ring
  · simp only [Fin.sum_univ_three, bary, Prod.snd_add, Prod.smul_snd, smul_eq_mul, det2,
      Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
    field_simp
    simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub]
    ring

theorem sum_baryLin_smul {t : Triangle} (ht : triDet t ≠ 0) (w : ℝ × ℝ) :
    ∑ k, baryLin t k w • t k = w := by
  ext
  · simp only [Fin.sum_univ_three, baryLin, Prod.fst_add, Prod.smul_fst, smul_eq_mul, det2,
      Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
    field_simp
    simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub]
    ring
  · simp only [Fin.sum_univ_three, baryLin, Prod.snd_add, Prod.smul_snd, smul_eq_mul, det2,
      Prod.fst_sub, Prod.snd_sub, Fin.isValue, Fin.reduceAdd]
    field_simp
    simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub]
    ring

theorem bary_vertex {t : Triangle} (ht : triDet t ≠ 0) (k j : Fin 3) :
    bary t k (t j) = if k = j then 1 else 0 := by
  fin_cases k <;> fin_cases j <;> simp [bary, det2] <;> rw [div_eq_one_iff_eq ht] <;>
    simp only [triDet, det2, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem continuous_bary (t : Triangle) (k : Fin 3) : Continuous (bary t k) := by
  unfold bary det2
  fun_prop

theorem mem_triRegion_iff {t : Triangle} (ht : triDet t ≠ 0) (z : ℝ × ℝ) :
    z ∈ triRegion t ↔ ∀ k, 0 ≤ bary t k z := by
  constructor
  · intro hz
    have key : convexHull ℝ (Set.range t) ⊆ {z | ∀ k, 0 ≤ bary t k z} := convexHull_min ?_ ?_
    · exact key hz
    · rintro _ ⟨j, rfl⟩ k
      rw [bary_vertex ht]
      split_ifs <;> norm_num
    · intro x hx y hy a b ha hb hab k
      have hb' : b = 1 - a := by linarith
      subst hb'
      have : bary t k (a • x + (1 - a) • y) = a * bary t k x + (1 - a) * bary t k y := by
        simp only [bary, det2, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [this]
      exact add_nonneg (mul_nonneg ha (hx k)) (mul_nonneg hb (hy k))
  · intro h
    rw [← sum_bary_smul ht z]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => h k) (by rw [sum_bary ht])
      (fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩)

theorem mem_interior_triRegion {t : Triangle} (ht : triDet t ≠ 0) {z : ℝ × ℝ}
    (h : ∀ k, 0 < bary t k z) : z ∈ interior (triRegion t) := by
  have hopen : IsOpen {z | ∀ k, 0 < bary t k z} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_bary t k)
  refine interior_maximal (fun w hw => ?_) hopen h
  exact (mem_triRegion_iff ht w).2 fun k => (hw k).le

theorem eq_vertex_iff {t : Triangle} (ht : triDet t ≠ 0) (i : Fin 3) (x : ℝ × ℝ) :
    t i = x ↔ ∀ k, k ≠ i → bary t k x = 0 := by
  constructor
  · rintro rfl k hk
    simp [bary_vertex ht, hk]
  · intro h
    have hi : bary t i x = 1 := by
      rw [← sum_bary ht x, Finset.sum_eq_single i (fun k _ hk => h k hk) (by simp)]
    rw [← sum_bary_smul ht x, Finset.sum_eq_single i (fun k _ hk => by rw [h k hk, zero_smul])
      (by simp), hi, one_smul]

theorem sum_fin3_eq {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) {i j k : Fin 3}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) : ∑ m, f m = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl hij
    | exact absurd rfl hki
    | exact absurd rfl hkj
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> abel)

theorem vertex_ne {t : Triangle} (ht : triDet t ≠ 0) {a b : Fin 3} (hab : a ≠ b) : t a ≠ t b := by
  intro h
  have := bary_vertex ht a b
  simp [← h, bary_vertex ht, hab] at this

theorem mem_line_iff {t : Triangle} (ht : triDet t ≠ 0) {d : ℝ × ℝ} (hd : d ≠ 0)
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    t j ∈ line[ℝ, t i, t i + d] ↔ baryLin t k d = 0 := by
  constructor
  · intro h
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h
    obtain ⟨r, hr⟩ := h
    rw [AffineMap.lineMap_apply] at hr
    simp only [vsub_eq_sub, add_sub_cancel_left, vadd_eq_add] at hr
    have h1 := congrArg (bary t k) hr
    rw [add_comm, bary_add, baryLin_smul, bary_vertex ht, bary_vertex ht] at h1
    simp only [hki, hkj, ite_false, zero_add] at h1
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hr
      exact vertex_ne ht hij hr
    exact (mul_eq_zero.1 h1).resolve_left hr0
  · intro h
    have hsum := sum_baryLin_smul ht d
    have hs0 := sum_baryLin t d
    rw [sum_fin3_eq _ hij hki hkj] at hsum hs0
    rw [h, zero_smul, add_zero] at hsum
    rw [h, add_zero] at hs0
    have ha : baryLin t i d = -baryLin t j d := by linarith
    rw [ha] at hsum
    obtain ⟨c, hcdef⟩ : ∃ c, baryLin t j d = c := ⟨_, rfl⟩
    rw [hcdef] at hsum
    have hc : c ≠ 0 := by
      intro hc; apply hd; rw [← hsum, hc]; simp
    have : t j = AffineMap.lineMap (t i) (t i + d) c⁻¹ := by
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, add_sub_cancel_left, vadd_eq_add]
      rw [← hsum, smul_add, smul_smul, smul_smul, mul_neg, inv_mul_cancel₀ hc, neg_smul,
        one_smul, one_smul]
      abel
    rw [this]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-! ### Signs and lexicographic positivity -/

/-- Signs of real numbers. -/
inductive Sg
  | neg
  | zero
  | pos
  deriving DecidableEq

instance : Fintype Sg where
  elems := {.neg, .zero, .pos}
  complete s := by cases s <;> simp

/-- The sign of a real number. -/
noncomputable def sg (x : ℝ) : Sg := if x < 0 then .neg else if x = 0 then .zero else .pos

/-- Negating a sign. -/
def Sg.flip : Sg → Sg
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

/-- Lexicographic positivity of a sign vector. -/
def lexS (a b c : Sg) : Bool := a = .pos || (a = .zero && (b = .pos || (b = .zero && c = .pos)))

/-- Lexicographic positivity of a triple of reals. -/
def LexPos (a b c : ℝ) : Prop := 0 < a ∨ (a = 0 ∧ (0 < b ∨ (b = 0 ∧ 0 < c)))

theorem sg_eq_zero_iff (x : ℝ) : sg x = .zero ↔ x = 0 := by
  unfold sg
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [not_lt.2 h.le, h.ne']

theorem sg_eq_pos_iff (x : ℝ) : sg x = .pos ↔ 0 < x := by
  unfold sg
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, not_lt.2 h.le]
  · simp
  · simp [not_lt.2 h.le, h.ne', h]

theorem sg_eq_neg_iff (x : ℝ) : sg x = .neg ↔ x < 0 := by
  unfold sg
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h]
  · simp
  · simp [not_lt.2 h.le, h.ne']

theorem sg_neg (x : ℝ) : sg (-x) = (sg x).flip := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [(sg_eq_neg_iff x).2 h, (sg_eq_pos_iff _).2 (neg_pos.2 h)]; rfl
  · rw [neg_zero, (sg_eq_zero_iff 0).2 rfl]; rfl
  · rw [(sg_eq_pos_iff x).2 h, (sg_eq_neg_iff _).2 (neg_lt_zero.2 h)]; rfl

theorem lexPos_iff (a b c : ℝ) : LexPos a b c ↔ lexS (sg a) (sg b) (sg c) = true := by
  simp only [LexPos, lexS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, sg_eq_pos_iff,
    sg_eq_zero_iff]

theorem eventually_sign_of_tendsto {α : Type*} {l : Filter α} {g : α → ℝ} {L : ℝ} (hL : L ≠ 0)
    (h : Tendsto g l (𝓝 L)) : ∀ᶠ x in l, (0 < g x ↔ 0 < L) ∧ g x ≠ 0 := by
  rcases lt_or_gt_of_ne hL with hL | hL
  · filter_upwards [h.eventually (eventually_lt_nhds hL)] with x hx
    exact ⟨⟨fun h' => absurd h' (not_lt.2 hx.le), fun h' => absurd h' (not_lt.2 hL.le)⟩, hx.ne⟩
  · filter_upwards [h.eventually (eventually_gt_nhds hL)] with x hx
    exact ⟨⟨fun _ => hL, fun _ => hx⟩, hx.ne'⟩

/-- The sign of `a + ε b + δ c` for `0 < δ ≪ ε ≪ 1` is the lexicographic sign of `(a, b, c)`. -/
theorem eventually_sign (a b c : ℝ) (hc : c ≠ 0) :
    ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)),
      (0 ≤ a + e.1 * b + e.2 * c ↔ LexPos a b c) ∧ a + e.1 * b + e.2 * c ≠ 0 := by
  suffices h : ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)),
      (0 < a + e.1 * b + e.2 * c ↔ LexPos a b c) ∧ a + e.1 * b + e.2 * c ≠ 0 by
    filter_upwards [h] with e he
    refine ⟨?_, he.2⟩
    rw [← he.1]
    exact ⟨fun h0 => lt_of_le_of_ne h0 (Ne.symm he.2), le_of_lt⟩
  rcases eq_or_ne a 0 with rfl | ha
  · rw [eventually_curry_iff]
    filter_upwards [self_mem_nhdsWithin] with e₁ (he₁ : 0 < e₁)
    rcases eq_or_ne b 0 with rfl | hb
    · filter_upwards [self_mem_nhdsWithin] with e₂ (he₂ : 0 < e₂)
      simp only [zero_add, mul_zero, LexPos, lt_self_iff_false, true_and, false_or]
      exact ⟨mul_pos_iff_of_pos_left he₂, mul_ne_zero he₂.ne' hc⟩
    · have hT : Tendsto (fun e₂ : ℝ => 0 + e₁ * b + e₂ * c) (𝓝[>] 0) (𝓝 (e₁ * b)) := by
        have : Tendsto (fun e₂ : ℝ => 0 + e₁ * b + e₂ * c) (𝓝 0) (𝓝 (0 + e₁ * b + 0 * c)) :=
          (Continuous.tendsto (by fun_prop) 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      filter_upwards [eventually_sign_of_tendsto (mul_ne_zero he₁.ne' hb) hT] with e₂ he₂
      refine ⟨?_, he₂.2⟩
      rw [he₂.1, mul_pos_iff_of_pos_left he₁]
      simp only [LexPos, lt_self_iff_false, true_and, false_or]
      exact ⟨Or.inl, fun h => h.resolve_right fun h' => hb h'.1⟩
  · have hT : Tendsto (fun e : ℝ × ℝ => a + e.1 * b + e.2 * c)
        ((𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ))) (𝓝 a) := by
      have : Tendsto (fun e : ℝ × ℝ => a + e.1 * b + e.2 * c) (𝓝 (0, 0))
          (𝓝 (a + (0 : ℝ × ℝ).1 * b + (0 : ℝ × ℝ).2 * c)) :=
        (Continuous.tendsto (by fun_prop) _)
      simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at this
      refine this.mono_left (curry_le_prod.trans ?_)
      rw [nhds_prod_eq]
      exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
    filter_upwards [eventually_sign_of_tendsto ha hT] with e he
    refine ⟨?_, he.2⟩
    rw [he.1]
    simp only [LexPos, ha, false_and, or_false]

/-- `0/1`-valued indicator. -/
def b2n (b : Bool) : ℕ := if b then 1 else 0

/-- The purely combinatorial core of the local counting argument, checked by enumeration. -/
def combB (p0 p1 p2 q0 q1 q2 r0 r1 r2 : Sg) : Bool :=
  r0 = .zero || r1 = .zero || r2 = .zero || !(p0 = .pos || p1 = .pos || p2 = .pos) ||
  !(q0 = .pos || q1 = .pos || q2 = .pos) || !(q0 = .neg || q1 = .neg || q2 = .neg) ||
  ((b2n (lexS p0 q0 r0 && lexS p1 q1 r1 && lexS p2 q2 r2) +
    b2n (lexS p0 q0 r0.flip && lexS p1 q1 r1.flip && lexS p2 q2 r2.flip) +
    b2n (lexS p0 q0.flip r0 && lexS p1 q1.flip r1 && lexS p2 q2.flip r2) +
    b2n (lexS p0 q0.flip r0.flip && lexS p1 q1.flip r1.flip && lexS p2 q2.flip r2.flip)) % 2 ==
   (b2n (p1 = .zero && p2 = .zero) * (b2n (q1 = .zero) + b2n (q2 = .zero)) +
    b2n (p0 = .zero && p2 = .zero) * (b2n (q0 = .zero) + b2n (q2 = .zero)) +
    b2n (p0 = .zero && p1 = .zero) * (b2n (q0 = .zero) + b2n (q1 = .zero))) % 2)

theorem combB_true : ∀ p0 p1 p2 q0 q1 q2 r0 r1 r2 : Sg,
    combB p0 p1 p2 q0 q1 q2 r0 r1 r2 = true := by
  decide

/-! ### The local count at a vertex -/

open Classical in
/-- The number of ordered pairs `(i, j)` of distinct vertices of `t` such that `t i = x` and
`t j` lies on the line through `x` in direction `d`, i.e. the number of sides of `t` lying on
this line and ending at `x`, counted with multiplicity two... -/
noncomputable def vertexLineCount (t : Triangle) (x d : ℝ × ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
    (fun ij => ij.1 ≠ ij.2 ∧ t ij.1 = x ∧ t ij.2 ∈ line[ℝ, x, x + d])).card

open Classical in
/-- Indicator of a triangular region, with values in `ZMod 2`. -/
noncomputable def inRegion (t : Triangle) (z : ℝ × ℝ) : ZMod 2 :=
  if z ∈ triRegion t then 1 else 0

/-- A point near `x`: `x + (s ε) d + (u δ) n`. -/
def qpt (x d n : ℝ × ℝ) (s u : ℝ) (e : ℝ × ℝ) : ℝ × ℝ := x + (s * e.1) • d + (u * e.2) • n

/-- Sum over the four sign choices. -/
def quadSum (f : ℝ → ℝ → ZMod 2) : ZMod 2 := f 1 1 + f 1 (-1) + f (-1) 1 + f (-1) (-1)

theorem bary_qpt (t : Triangle) (k : Fin 3) (x d n : ℝ × ℝ) (s u : ℝ) (e : ℝ × ℝ) :
    bary t k (qpt x d n s u e) =
      bary t k x + e.1 * (s * baryLin t k d) + e.2 * (u * baryLin t k n) := by
  simp only [qpt, bary_add, baryLin_smul]
  ring

/-- Near `x`, the points `qpt` avoid all side lines of `t`. -/
theorem eventually_bary_qpt_ne_zero (t : Triangle) (x d n : ℝ × ℝ)
    (hn : ∀ k, baryLin t k n ≠ 0) (s u : ℝ) (hu : u ≠ 0) :
    ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)), ∀ k, bary t k (qpt x d n s u e) ≠ 0 := by
  refine Filter.eventually_all.2 fun k => ?_
  filter_upwards [eventually_sign (bary t k x) (s * baryLin t k d) (u * baryLin t k n)
    (mul_ne_zero hu (hn k))] with e he
  rw [bary_qpt]
  exact he.2

theorem eventually_mem_iff (t : Triangle) (ht : triDet t ≠ 0) (x d n : ℝ × ℝ)
    (hn : ∀ k, baryLin t k n ≠ 0) (s u : ℝ) (hu : u ≠ 0) :
    ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)), (qpt x d n s u e ∈ triRegion t ↔
      ∀ k, LexPos (bary t k x) (s * baryLin t k d) (u * baryLin t k n)) := by
  have := Filter.eventually_all.2 fun k => eventually_sign (bary t k x) (s * baryLin t k d)
    (u * baryLin t k n) (mul_ne_zero hu (hn k))
  filter_upwards [this] with e he
  rw [mem_triRegion_iff ht]
  exact forall_congr' fun k => by rw [bary_qpt]; exact (he k).1

theorem ite_eq_b2n {P : Prop} {_ : Decidable P} {B : Bool} (h : P ↔ B = true) :
    (if P then (1 : ZMod 2) else 0) = ((b2n B : ℕ) : ZMod 2) := by
  cases B <;> simp_all [b2n]

theorem forall_lexPos_iff (p q r : Fin 3 → ℝ) : (∀ k, LexPos (p k) (q k) (r k)) ↔
    (lexS (sg (p 0)) (sg (q 0)) (sg (r 0)) && lexS (sg (p 1)) (sg (q 1)) (sg (r 1)) &&
      lexS (sg (p 2)) (sg (q 2)) (sg (r 2))) = true := by
  simp only [Bool.and_eq_true, ← lexPos_iff]
  constructor
  · intro h; exact ⟨⟨h 0, h 1⟩, h 2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ k
    fin_cases k <;> assumption

theorem quad_bridge (P0 P1 P2 Q0 Q1 Q2 R0 R1 R2 : Sg) (hr0 : R0 ≠ .zero) (hr1 : R1 ≠ .zero)
    (hr2 : R2 ≠ .zero) (hp : (P0 = .pos || P1 = .pos || P2 = .pos) = true)
    (hq : (Q0 = .pos || Q1 = .pos || Q2 = .pos) = true)
    (hq' : (Q0 = .neg || Q1 = .neg || Q2 = .neg) = true) :
    ((b2n (lexS P0 Q0 R0 && lexS P1 Q1 R1 && lexS P2 Q2 R2) : ℕ) : ZMod 2) +
      ((b2n (lexS P0 Q0 R0.flip && lexS P1 Q1 R1.flip && lexS P2 Q2 R2.flip) : ℕ) : ZMod 2) +
      ((b2n (lexS P0 Q0.flip R0 && lexS P1 Q1.flip R1 && lexS P2 Q2.flip R2) : ℕ) : ZMod 2) +
      ((b2n (lexS P0 Q0.flip R0.flip && lexS P1 Q1.flip R1.flip && lexS P2 Q2.flip R2.flip) :
        ℕ) : ZMod 2) =
    (((b2n (P1 = .zero && P2 = .zero) * (b2n (Q1 = .zero) + b2n (Q2 = .zero)) +
      b2n (P0 = .zero && P2 = .zero) * (b2n (Q0 = .zero) + b2n (Q2 = .zero)) +
      b2n (P0 = .zero && P1 = .zero) * (b2n (Q0 = .zero) + b2n (Q1 = .zero))) : ℕ) : ZMod 2) := by
  have h := combB_true P0 P1 P2 Q0 Q1 Q2 R0 R1 R2
  simp only [combB, hp, hq, hq', hr0, hr1, hr2, decide_false, Bool.not_true, Bool.or_false,
    Bool.false_or, beq_iff_eq] at h
  have := (ZMod.natCast_eq_natCast_iff' _ _ 2).2 h
  exact_mod_cast this

theorem fin3_other : ∀ i j k m : Fin 3, i ≠ j → k ≠ i → k ≠ j → m ≠ i → m = j ∨ m = k := by
  decide

theorem vertex_line_pair_iff {t : Triangle} (ht : triDet t ≠ 0) {x d : ℝ × ℝ} (hd : d ≠ 0)
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (i ≠ j ∧ t i = x ∧ t j ∈ line[ℝ, x, x + d]) ↔
      (bary t j x = 0 ∧ bary t k x = 0) ∧ baryLin t k d = 0 := by
  constructor
  · rintro ⟨-, rfl, hl⟩
    exact ⟨⟨by simp [bary_vertex ht, Ne.symm hij], by simp [bary_vertex ht, hki]⟩,
      (mem_line_iff ht hd hij hki hkj).1 hl⟩
  · rintro ⟨⟨hj, hk⟩, hl⟩
    have hx : t i = x := (eq_vertex_iff ht i x).2 fun m hm => by
      rcases fin3_other i j k m hij hki hkj hm with rfl | rfl
      · exact hj
      · exact hk
    subst hx
    exact ⟨hij, rfl, (mem_line_iff ht hd hij hki hkj).2 hl⟩

theorem vertexLineCount_eq {t : Triangle} (ht : triDet t ≠ 0) {d : ℝ × ℝ} (hd : d ≠ 0)
    (x : ℝ × ℝ) : vertexLineCount t x d =
    b2n (sg (bary t 1 x) = .zero && sg (bary t 2 x) = .zero) *
        (b2n (sg (baryLin t 1 d) = .zero) + b2n (sg (baryLin t 2 d) = .zero)) +
      b2n (sg (bary t 0 x) = .zero && sg (bary t 2 x) = .zero) *
        (b2n (sg (baryLin t 0 d) = .zero) + b2n (sg (baryLin t 2 d) = .zero)) +
      b2n (sg (bary t 0 x) = .zero && sg (bary t 1 x) = .zero) *
        (b2n (sg (baryLin t 0 d) = .zero) + b2n (sg (baryLin t 1 d) = .zero)) := by
  classical
  unfold vertexLineCount
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  rw [if_congr (vertex_line_pair_iff ht hd (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide)) rfl rfl,
    if_congr (vertex_line_pair_iff ht hd (i := 0) (j := 2) (k := 1) (by decide) (by decide)
      (by decide)) rfl rfl,
    if_congr (vertex_line_pair_iff ht hd (i := 1) (j := 0) (k := 2) (by decide) (by decide)
      (by decide)) rfl rfl,
    if_congr (vertex_line_pair_iff ht hd (i := 1) (j := 2) (k := 0) (by decide) (by decide)
      (by decide)) rfl rfl,
    if_congr (vertex_line_pair_iff ht hd (i := 2) (j := 0) (k := 1) (by decide) (by decide)
      (by decide)) rfl rfl,
    if_congr (vertex_line_pair_iff ht hd (i := 2) (j := 1) (k := 0) (by decide) (by decide)
      (by decide)) rfl rfl]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, sg_eq_zero_iff, b2n,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases h0 : bary t 0 x = 0 <;> by_cases h1 : bary t 1 x = 0 <;>
    by_cases h2 : bary t 2 x = 0 <;> by_cases g0 : baryLin t 0 d = 0 <;>
    by_cases g1 : baryLin t 1 d = 0 <;> by_cases g2 : baryLin t 2 d = 0 <;> simp [*]

/-- The local count: modulo `2`, the number of the four points near `x` which lie in `t`
equals `vertexLineCount t x d`. -/
theorem eventually_quadSum_eq (t : Triangle) (ht : triDet t ≠ 0) (x d n : ℝ × ℝ)
    (hd : d ≠ 0) (hn : ∀ k, baryLin t k n ≠ 0) :
    ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)),
      quadSum (fun s u => inRegion t (qpt x d n s u e)) = (vertexLineCount t x d : ZMod 2) := by
  filter_upwards [eventually_mem_iff t ht x d n hn 1 1 one_ne_zero,
    eventually_mem_iff t ht x d n hn 1 (-1) (by norm_num),
    eventually_mem_iff t ht x d n hn (-1) 1 one_ne_zero,
    eventually_mem_iff t ht x d n hn (-1) (-1) (by norm_num)] with e h1 h2 h3 h4
  simp only [quadSum, inRegion]
  rw [ite_eq_b2n (h1.trans (forall_lexPos_iff _ _ _)), ite_eq_b2n (h2.trans (forall_lexPos_iff _ _ _)),
    ite_eq_b2n (h3.trans (forall_lexPos_iff _ _ _)), ite_eq_b2n (h4.trans (forall_lexPos_iff _ _ _)),
    vertexLineCount_eq ht hd]
  simp only [one_mul, neg_one_mul, sg_neg]
  have hr : ∀ k, sg (baryLin t k n) ≠ .zero := fun k h => hn k ((sg_eq_zero_iff _).1 h)
  have hsum := sum_bary ht x
  have hqsum := sum_baryLin t d
  have hqsmul := sum_baryLin_smul ht d
  rw [Fin.sum_univ_three] at hsum hqsum hqsmul
  apply quad_bridge _ _ _ _ _ _ _ _ _ (hr 0) (hr 1) (hr 2)
  · simp only [Bool.or_eq_true, decide_eq_true_eq, sg_eq_pos_iff]
    by_contra h
    push Not at h
    linarith [h.1.1, h.1.2, h.2]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, sg_eq_pos_iff]
    by_contra h
    push Not at h
    apply hd
    have e0 : baryLin t 0 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    have e1 : baryLin t 1 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    have e2 : baryLin t 2 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    rw [← hqsmul, e0, e1, e2]
    simp
  · simp only [Bool.or_eq_true, decide_eq_true_eq, sg_eq_neg_iff]
    by_contra h
    push Not at h
    apply hd
    have e0 : baryLin t 0 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    have e1 : baryLin t 1 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    have e2 : baryLin t 2 d = 0 := by linarith [h.1.1, h.1.2, h.2]
    rw [← hqsmul, e0, e1, e2]
    simp

/-- A direction not parallel to any of finitely many nonzero vectors. -/
theorem exists_generic_dir {ι : Type*} [Fintype ι] (w : ι → ℝ × ℝ) (hw : ∀ i, w i ≠ 0) :
    ∃ n : ℝ × ℝ, ∀ i, det2 n (w i) ≠ 0 := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image fun i => (w i).2 / (w i).1)
  refine ⟨(1, c), fun i h => ?_⟩
  simp only [det2, one_mul] at h
  by_cases h1 : (w i).1 = 0
  · rw [h1, mul_zero, sub_zero] at h
    exact hw i (Prod.ext h1 h)
  · apply hc
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    field_simp
    linarith

theorem exists_generic_dir_triangles {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Triangle) (B : κ → Triangle)
    (hA : ∀ a, triDet (A a) ≠ 0) (hB : ∀ b, triDet (B b) ≠ 0) :
    ∃ n : ℝ × ℝ, (∀ a k, baryLin (A a) k n ≠ 0) ∧ (∀ b k, baryLin (B b) k n ≠ 0) := by
  have hne : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  obtain ⟨n, hn⟩ := exists_generic_dir
    (fun m : (ι × Fin 3) ⊕ (κ × Fin 3) => match m with
      | .inl ak => A ak.1 (ak.2 + 1) - A ak.1 (ak.2 + 2)
      | .inr bk => B bk.1 (bk.2 + 1) - B bk.1 (bk.2 + 2))
    (by
      rintro (⟨a, k⟩ | ⟨b, k⟩)
      · exact sub_ne_zero.2 (vertex_ne (hA a) (hne k))
      · exact sub_ne_zero.2 (vertex_ne (hB b) (hne k)))
  refine ⟨n, fun a k => div_ne_zero (hn (.inl (a, k))) (hA a),
    fun b k => div_ne_zero (hn (.inr (b, k))) (hB b)⟩

/-- Two families of triangles covering generic points equally often modulo `2`. -/
def SameCoverMod2 {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → Triangle) (B : κ → Triangle) :
    Prop :=
  ∀ z, (∀ a k, bary (A a) k z ≠ 0) → (∀ b k, bary (B b) k z ≠ 0) →
    ∑ a, inRegion (A a) z = ∑ b, inRegion (B b) z

theorem sum_vertexLineCount_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Triangle) (B : κ → Triangle)
    (hA : ∀ a, triDet (A a) ≠ 0) (hB : ∀ b, triDet (B b) ≠ 0) (hcov : SameCoverMod2 A B)
    (x d : ℝ × ℝ) (hd : d ≠ 0) :
    ∑ a, (vertexLineCount (A a) x d : ZMod 2) = ∑ b, (vertexLineCount (B b) x d : ZMod 2) := by
  obtain ⟨n, hnA, hnB⟩ := exists_generic_dir_triangles A B hA hB
  have hgen : ∀ s u : ℝ, u ≠ 0 → ∀ᶠ e in (𝓝[>] (0 : ℝ)).curry (𝓝[>] (0 : ℝ)),
      (∀ a k, bary (A a) k (qpt x d n s u e) ≠ 0) ∧ (∀ b k, bary (B b) k (qpt x d n s u e) ≠ 0) :=
    fun s u hu => (Filter.eventually_all.2 fun a =>
      eventually_bary_qpt_ne_zero (A a) x d n (hnA a) s u hu).and
      (Filter.eventually_all.2 fun b => eventually_bary_qpt_ne_zero (B b) x d n (hnB b) s u hu)
  have hAq := Filter.eventually_all.2 fun a => eventually_quadSum_eq (A a) (hA a) x d n hd (hnA a)
  have hBq := Filter.eventually_all.2 fun b => eventually_quadSum_eq (B b) (hB b) x d n hd (hnB b)
  have hall := (((((hgen 1 1 one_ne_zero).and (hgen 1 (-1) (by norm_num))).and
    (hgen (-1) 1 one_ne_zero)).and (hgen (-1) (-1) (by norm_num))).and hAq).and hBq
  rw [eventually_curry_iff] at hall
  obtain ⟨e₁, he₁⟩ := hall.exists
  obtain ⟨e₂, ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, hA'⟩, hB'⟩⟩ := he₁.exists
  simp only [← hA', ← hB', quadSum, Finset.sum_add_distrib]
  rw [hcov _ g1.1 g1.2, hcov _ g2.1 g2.2, hcov _ g3.1 g3.2, hcov _ g4.1 g4.2]

/-! ### Functions additive along lines -/

/-- A `ZMod 2`-valued function on pairs of points which is additive along lines. -/
def LineAdditive (F : ℝ × ℝ → ℝ × ℝ → ZMod 2) : Prop :=
  ∀ a b c, Collinear ℝ {a, b, c} → F a c = F a b + F b c

/-- The sum of `F` over the three sides of a triangle. -/
def edgeSum (F : ℝ × ℝ → ℝ × ℝ → ZMod 2) (t : Triangle) : ZMod 2 :=
  F (t 0) (t 1) + F (t 1) (t 2) + F (t 2) (t 0)

theorem LineAdditive.self {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F) (a : ℝ × ℝ) :
    F a a = 0 := by
  have h := hF a a a (by simp [collinear_singleton])
  rw [CharTwo.add_self_eq_zero] at h
  exact h

theorem LineAdditive.symm {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F) (a b : ℝ × ℝ) :
    F a b = F b a := by
  have hs : ({a, b, a} : Set (ℝ × ℝ)) = {a, b} := by ext; simp; tauto
  have h := hF a b a (by rw [hs]; exact collinear_pair ℝ a b)
  rw [hF.self] at h
  rw [eq_neg_of_add_eq_zero_left h.symm, ZMod.neg_eq_self_mod_two]

open Classical in
/-- A chosen point on an affine subspace (if nonempty). -/
noncomputable def basePt (L : AffineSubspace ℝ (ℝ × ℝ)) : ℝ × ℝ :=
  if h : (L : Set (ℝ × ℝ)).Nonempty then h.some else 0

/-- The contribution of the point `x` on the line `L`. -/
noncomputable def lineContrib (F : ℝ × ℝ → ℝ × ℝ → ZMod 2) (x : ℝ × ℝ)
    (L : AffineSubspace ℝ (ℝ × ℝ)) : ZMod 2 :=
  F x (basePt L)

theorem LineAdditive.eq_lineContrib {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F)
    (a b : ℝ × ℝ) : F a b = lineContrib F a line[ℝ, a, b] + lineContrib F b line[ℝ, b, a] := by
  have hne : ((line[ℝ, a, b] : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)).Nonempty :=
    ⟨a, left_mem_affineSpan_pair ℝ a b⟩
  have hb0 : basePt line[ℝ, a, b] ∈ line[ℝ, a, b] := by
    simpa [basePt, hne] using hne.some_mem
  have hcol : Collinear ℝ {a, basePt line[ℝ, a, b], b} :=
    (collinear_insert_insert_of_mem_affineSpan_pair hb0 hb0).subset
      (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  rw [hF a _ b hcol, hF.symm (basePt _) b]
  unfold lineContrib
  rw [Set.pair_comm b a]

open Classical in
theorem edgeSum_eq_sum_pairs {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F)
    (t : Triangle) :
    edgeSum F t = ∑ ij : Fin 3 × Fin 3,
      if ij.1 ≠ ij.2 then lineContrib F (t ij.1) line[ℝ, t ij.1, t ij.2] else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, ne_eq, not_true_eq_false, ite_false, Fin.isValue,
    Fin.reduceEq, not_false_eq_true, ite_true, add_zero, zero_add]
  unfold edgeSum
  rw [hF.eq_lineContrib (t 0) (t 1), hF.eq_lineContrib (t 1) (t 2), hF.eq_lineContrib (t 2) (t 0)]
  abel

theorem line_eq_iff {x y d : ℝ × ℝ} (hxy : y ≠ x) :
    line[ℝ, x, y] = line[ℝ, x, x + d] ↔ y ∈ line[ℝ, x, x + d] := by
  constructor
  · intro h; rw [← h]; exact right_mem_affineSpan_pair ℝ x y
  · intro hy
    apply le_antisymm (affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair ℝ _ _) hy)
    apply affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair ℝ _ _)
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hy ⊢
    obtain ⟨r, hr⟩ := hy
    rw [AffineMap.lineMap_apply] at hr
    simp only [vsub_eq_sub, add_sub_cancel_left, vadd_eq_add] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [zero_smul, zero_add] at hr; exact hxy hr.symm
    refine ⟨r⁻¹, ?_⟩
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    rw [← hr, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr0, one_smul, add_comm]

open Classical in
theorem card_key_eq {T : Triangle} (hT : triDet T ≠ 0) (x d : ℝ × ℝ) :
    ((Finset.univ.filter fun ij : Fin 3 × Fin 3 => ij.1 ≠ ij.2).filter
      (fun ij => (T ij.1, line[ℝ, T ij.1, T ij.2]) = (x, line[ℝ, x, x + d]))).card =
    vertexLineCount T x d := by
  unfold vertexLineCount
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, rfl, hL⟩
    exact ⟨hij, rfl, (line_eq_iff (vertex_ne hT (Ne.symm hij))).1 hL⟩
  · rintro ⟨hij, rfl, hL⟩
    exact ⟨hij, rfl, (line_eq_iff (vertex_ne hT (Ne.symm hij))).2 hL⟩

/-- **Parity principle.** If two families of non-degenerate triangles cover generic points
equally often modulo `2`, then for every function `F` additive along lines the sums of `F`
over the sides of the triangles agree. -/
theorem sum_edgeSum_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Triangle) (B : κ → Triangle)
    (hA : ∀ a, triDet (A a) ≠ 0) (hB : ∀ b, triDet (B b) ≠ 0) (hcov : SameCoverMod2 A B)
    {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F) :
    ∑ a, edgeSum F (A a) = ∑ b, edgeSum F (B b) := by
  classical
  let key : Triangle → Fin 3 × Fin 3 → (ℝ × ℝ) × AffineSubspace ℝ (ℝ × ℝ) :=
    fun T ij => (T ij.1, line[ℝ, T ij.1, T ij.2])
  let off : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun ij => ij.1 ≠ ij.2)
  let K := (Finset.univ.biUnion fun a => off.image (key (A a))) ∪
    (Finset.univ.biUnion fun b => off.image (key (B b)))
  let G : (ℝ × ℝ) × AffineSubspace ℝ (ℝ × ℝ) → ZMod 2 := fun κ => lineContrib F κ.1 κ.2
  have hreg : ∀ T : Triangle, (∀ ij ∈ off, key T ij ∈ K) →
      edgeSum F T = ∑ κ ∈ K, ((off.filter fun ij => key T ij = κ).card : ZMod 2) * G κ := by
    intro T hT
    rw [edgeSum_eq_sum_pairs hF, ← Finset.sum_filter, ← Finset.sum_fiberwise_of_maps_to hT]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G κ) (fun ij hij => by
      rw [← (Finset.mem_filter.1 hij).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hKA : ∀ a, ∀ ij ∈ off, key (A a) ij ∈ K := fun a ij hij =>
    Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hij⟩)
  have hKB : ∀ b, ∀ ij ∈ off, key (B b) ij ∈ K := fun b ij hij =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hij⟩)
  rw [Finset.sum_congr rfl fun a _ => hreg (A a) (hKA a),
    Finset.sum_congr rfl fun b _ => hreg (B b) (hKB b)]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  -- every key is of the form `(x, line[x, x + d])` with `d ≠ 0`
  have hform : ∃ x d : ℝ × ℝ, d ≠ 0 ∧ κ = (x, line[ℝ, x, x + d]) := by
    have aux : ∀ T : Triangle, triDet T ≠ 0 → ∀ ij ∈ off, key T ij = κ →
        ∃ x d : ℝ × ℝ, d ≠ 0 ∧ κ = (x, line[ℝ, x, x + d]) := by
      intro T hT ij hij hk
      refine ⟨T ij.1, T ij.2 - T ij.1, sub_ne_zero.2
        (vertex_ne hT (Ne.symm (Finset.mem_filter.1 hij).2)), ?_⟩
      rw [← hk, add_sub_cancel]
    rcases Finset.mem_union.1 hκ with h | h
    · obtain ⟨a, -, h⟩ := Finset.mem_biUnion.1 h
      obtain ⟨ij, hij, hk⟩ := Finset.mem_image.1 h
      exact aux _ (hA a) ij hij hk
    · obtain ⟨b, -, h⟩ := Finset.mem_biUnion.1 h
      obtain ⟨ij, hij, hk⟩ := Finset.mem_image.1 h
      exact aux _ (hB b) ij hij hk
  obtain ⟨x, d, hd, rfl⟩ := hform
  simp only [off, key]
  refine (Finset.sum_congr rfl fun a _ => by rw [card_key_eq (hA a) x d]).trans
    ((sum_vertexLineCount_eq A B hA hB hcov x d hd).trans
      (Finset.sum_congr rfl fun b _ => by rw [card_key_eq (hB b) x d]))

end Chapter22

/-!
# Lemma 2: every dissection of the unit square contains an odd number of rainbow triangles

We apply the parity principle of `Chapter_22.Parity` to the "red-blue" indicator function
(which is additive along lines because every line receives at most two colors, by the
Corollary), comparing an arbitrary dissection of the unit square with the dissection of the
square into two triangles along a diagonal.
-/


namespace Chapter22

open Color

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation ℝ Γ₀)

/-! ### Splitting the square along the diagonal -/

/-- The lower-right half of the unit square. -/
def sqTri0 : Triangle := ![(0, 0), (1, 0), (1, 1)]

/-- The upper-left half of the unit square. -/
def sqTri1 : Triangle := ![(0, 0), (1, 1), (0, 1)]

/-- The unit square split into two triangles. -/
def sqTris : Fin 2 → Triangle := ![sqTri0, sqTri1]

theorem triDet_sqTri0 : triDet sqTri0 = 1 := by
  simp [triDet, sqTri0, det2]

theorem triDet_sqTri1 : triDet sqTri1 = 1 := by
  simp [triDet, sqTri1, det2]

theorem sqTris_nondegenerate : ∀ b, triDet (sqTris b) ≠ 0 := by
  intro b
  fin_cases b <;> simp [sqTris, triDet_sqTri0, triDet_sqTri1]

theorem forall_fin3_iff (P : Fin 3 → Prop) : (∀ k, P k) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h k => by fin_cases k <;> simp [h.1, h.2.1, h.2.2]⟩

theorem bary_sqTri0 (z : ℝ × ℝ) :
    bary sqTri0 0 z = 1 - z.1 ∧ bary sqTri0 1 z = z.1 - z.2 ∧ bary sqTri0 2 z = z.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [bary, sqTri0, triDet, det2] <;> ring

theorem bary_sqTri1 (z : ℝ × ℝ) :
    bary sqTri1 0 z = 1 - z.2 ∧ bary sqTri1 1 z = z.1 ∧ bary sqTri1 2 z = z.2 - z.1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [bary, sqTri1, triDet, det2] <;> ring

theorem mem_sqTri0_iff (z : ℝ × ℝ) :
    z ∈ triRegion sqTri0 ↔ 0 ≤ 1 - z.1 ∧ 0 ≤ z.1 - z.2 ∧ 0 ≤ z.2 := by
  rw [mem_triRegion_iff (by rw [triDet_sqTri0]; norm_num), forall_fin3_iff, (bary_sqTri0 z).1,
    (bary_sqTri0 z).2.1, (bary_sqTri0 z).2.2]

theorem mem_sqTri1_iff (z : ℝ × ℝ) :
    z ∈ triRegion sqTri1 ↔ 0 ≤ 1 - z.2 ∧ 0 ≤ z.1 ∧ 0 ≤ z.2 - z.1 := by
  rw [mem_triRegion_iff (by rw [triDet_sqTri1]; norm_num), forall_fin3_iff, (bary_sqTri1 z).1,
    (bary_sqTri1 z).2.1, (bary_sqTri1 z).2.2]

theorem bary_sqTri0_one (z : ℝ × ℝ) : bary sqTri0 1 z = z.1 - z.2 := (bary_sqTri0 z).2.1

theorem mem_unitSquare_iff (z : ℝ × ℝ) :
    z ∈ unitSquare ↔ (0 ≤ z.1 ∧ z.1 ≤ 1) ∧ (0 ≤ z.2 ∧ z.2 ≤ 1) := by
  simp only [unitSquare, Set.mem_prod, Set.mem_Icc]

open Classical in
theorem sum_inRegion_sqTris (z : ℝ × ℝ) (hz : z.1 - z.2 ≠ 0) :
    ∑ b, inRegion (sqTris b) z = if z ∈ unitSquare then 1 else 0 := by
  rw [Fin.sum_univ_two]
  change inRegion sqTri0 z + inRegion sqTri1 z =
    if z ∈ unitSquare then 1 else 0
  unfold inRegion
  rcases lt_or_gt_of_ne hz with h | h
  · have hnot : z ∉ triRegion sqTri0 := by
      rw [mem_sqTri0_iff]; intro h'; linarith [h'.2.1]
    simp only [hnot, ite_false, zero_add]
    refine if_congr ?_ rfl rfl
    rw [mem_sqTri1_iff, mem_unitSquare_iff]
    constructor
    · rintro ⟨h0, h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · have hnot : z ∉ triRegion sqTri1 := by
      rw [mem_sqTri1_iff]; intro h'; linarith [h'.2.2]
    simp only [hnot, ite_false, add_zero]
    refine if_congr ?_ rfl rfl
    rw [mem_sqTri0_iff, mem_unitSquare_iff]
    constructor
    · rintro ⟨h0, h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith

open Classical in
/-- In a dissection, a generic point lies in exactly one triangle if it lies in the square,
and in none otherwise. -/
theorem IsDissection.sum_inRegion {ι : Type*} [Fintype ι] {T : ι → Triangle}
    (hT : IsDissection T) (z : ℝ × ℝ) (hz : ∀ a k, bary (T a) k z ≠ 0) :
    ∑ a, inRegion (T a) z = if z ∈ unitSquare then 1 else 0 := by
  have hpos : ∀ a, z ∈ triRegion (T a) → z ∈ interior (triRegion (T a)) := fun a ha =>
    mem_interior_triRegion (hT.nondegenerate a) fun k =>
      lt_of_le_of_ne ((mem_triRegion_iff (hT.nondegenerate a) z).1 ha k) (Ne.symm (hz a k))
  by_cases hS : z ∈ unitSquare
  · simp only [hS, ite_true]
    rw [← hT.iUnion_eq, Set.mem_iUnion] at hS
    obtain ⟨i, hi⟩ := hS
    rw [Finset.sum_eq_single i]
    · simp [inRegion, hi]
    · intro j _ hji
      simp only [inRegion]
      have hnot : z ∉ triRegion (T j) := fun hj =>
        Set.disjoint_left.1 (hT.disjoint_interior j i hji) (hpos j hj) (hpos i hi)
      simp [hnot]
    · simp
  · simp only [hS, ite_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [inRegion]
    have hnot : z ∉ triRegion (T i) := by
      intro hi
      apply hS
      rw [← hT.iUnion_eq]
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    simp [hnot]

theorem IsDissection.sameCoverMod2 {ι : Type*} [Fintype ι] {T : ι → Triangle}
    (hT : IsDissection T) : SameCoverMod2 T sqTris := by
  intro z hzT hzB
  rw [hT.sum_inRegion z hzT, sum_inRegion_sqTris z]
  have := hzB 0 1
  simpa [sqTris, bary_sqTri0_one] using this

/-! ### The red-blue indicator -/

/-- Indicator of the color combination red-blue. -/
def rbInd : Color → Color → ZMod 2
  | red, blue => 1
  | blue, red => 1
  | _, _ => 0

/-- The red-blue indicator on pairs of points: `1` for a red-blue segment, `0` otherwise. -/
noncomputable def redBlue (p q : ℝ × ℝ) : ZMod 2 := rbInd (color v p) (color v q)

theorem rbInd_add : ∀ c₁ c₂ c₃ : Color, (c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃) →
    rbInd c₁ c₃ = rbInd c₁ c₂ + rbInd c₂ c₃ := by
  decide

theorem rbInd_edgeSum : ∀ c₀ c₁ c₂ : Color,
    rbInd c₀ c₁ + rbInd c₁ c₂ + rbInd c₂ c₀ = if c₀ ≠ c₁ ∧ c₁ ≠ c₂ ∧ c₀ ≠ c₂ then 1 else 0 := by
  decide

theorem isRainbow_iff (t : Triangle) : IsRainbow v t ↔
    color v (t 0) ≠ color v (t 1) ∧ color v (t 1) ≠ color v (t 2) ∧
      color v (t 0) ≠ color v (t 2) := by
  constructor
  · intro h
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · exact absurd (h h') (by decide)
    · exact absurd (h h') (by decide)
    · exact absurd (h h') (by decide)
  · rintro ⟨h01, h12, h02⟩ i j hij
    simp only at hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The red-blue indicator is additive along lines (because every line receives at most two
colors). -/
theorem lineAdditive_redBlue : LineAdditive (redBlue v) := by
  intro a b c hcol
  have hr : Set.range ![a, b, c] = {a, b, c} := by ext p; simp; tauto
  have hni := not_injective_color_of_collinear v (t := ![a, b, c]) (hr ▸ hcol)
  apply rbInd_add
  by_contra hne
  push Not at hne
  apply hni
  have := (isRainbow_iff v ![a, b, c]).2 (by simpa using ⟨hne.1, hne.2.2, hne.2.1⟩)
  exact this

open Classical in
/-- Observation **(B)**: the number of red-blue sides of a triangle is odd if and only if the
triangle is a rainbow triangle. (Together with additivity along lines, this is the statement that
a rainbow triangle has an odd number of red-blue segments on its boundary, any other triangle an
even number.) -/
theorem edgeSum_redBlue (t : Triangle) :
    edgeSum (redBlue v) t = if IsRainbow v t then 1 else 0 := by
  simp only [edgeSum, redBlue]
  rw [rbInd_edgeSum]
  exact if_congr (isRainbow_iff v t).symm rfl rfl

theorem color_zero_zero : color v (0, 0) = red := (color_eq_red_iff v _).2 (by simp)
theorem color_one_zero : color v (1, 0) = blue := (color_eq_blue_iff v _).2 (by simp)
theorem color_one_one : color v (1, 1) = blue := (color_eq_blue_iff v _).2 (by simp)
theorem color_zero_one : color v (0, 1) = green := (color_eq_green_iff v _).2 (by simp)

/-- Telescoping along a line: for a function additive along lines, the sum over consecutive
segments of a subdivided segment equals the value on the whole segment. -/
theorem LineAdditive.sum_range {F : ℝ × ℝ → ℝ × ℝ → ZMod 2} (hF : LineAdditive F)
    (p : ℕ → ℝ × ℝ) (hp : ∀ i j k, Collinear ℝ {p i, p j, p k}) (m : ℕ) :
    ∑ i ∈ Finset.range m, F (p i) (p (i + 1)) = F (p 0) (p m) := by
  induction m with
  | zero => simp [hF.self]
  | succ m ih => rw [Finset.sum_range_succ, ih, ← hF _ _ _ (hp 0 m (m + 1))]

theorem collinear_horizontal (y a b c : ℝ) : Collinear ℝ {(a, y), (b, y), (c, y)} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0, y), (1, 0), ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> [exact ⟨a, by ext <;> simp⟩; exact ⟨b, by ext <;> simp⟩;
    exact ⟨c, by ext <;> simp⟩]

/-- Observation **(A)**, first part: if the bottom side of the square is subdivided by points
`0 = x₀, x₁, …, x_m = 1`, then the number of red-blue segments `[(xᵢ, 0), (xᵢ₊₁, 0)]` is odd. -/
theorem observationA_bottom (x : ℕ → ℝ) (m : ℕ) (h0 : x 0 = 0) (hm : x m = 1) :
    ∑ i ∈ Finset.range m, redBlue v (x i, 0) (x (i + 1), 0) = 1 := by
  rw [(lineAdditive_redBlue v).sum_range (fun i => (x i, 0))
    (fun i j k => collinear_horizontal 0 _ _ _) m]
  simp only [h0, hm, redBlue, color_zero_zero, color_one_zero]
  rfl

/-- Observation **(A)**, second part: the other boundary lines of the square contain no red-blue
segments. -/
theorem observationA_other_sides :
    (∀ y y' : ℝ, redBlue v (0, y) (0, y') = 0) ∧ (∀ x x' : ℝ, redBlue v (x, 1) (x', 1) = 0) ∧
      (∀ y y' : ℝ, redBlue v (1, y) (1, y') = 0) := by
  have nb : ∀ y : ℝ, color v (0, y) ≠ blue := fun y h => by
    rw [color_eq_blue_iff] at h; simpa using h.2
  have nr1 : ∀ x : ℝ, color v (x, 1) ≠ red := fun x h => by
    rw [color_eq_red_iff] at h; simpa using h.2
  have nr2 : ∀ y : ℝ, color v (1, y) ≠ red := fun y h => by
    rw [color_eq_red_iff] at h; simpa using h.1
  have key : ∀ c c' : Color, (c ≠ blue ∧ c' ≠ blue) ∨ (c ≠ red ∧ c' ≠ red) → rbInd c c' = 0 := by
    decide
  refine ⟨fun y y' => key _ _ (Or.inl ⟨nb y, nb y'⟩), fun x x' => key _ _ (Or.inr ⟨nr1 x, nr1 x'⟩),
    fun y y' => key _ _ (Or.inr ⟨nr2 y, nr2 y'⟩)⟩

theorem sum_edgeSum_sqTris : ∑ b, edgeSum (redBlue v) (sqTris b) = 1 := by
  rw [Fin.sum_univ_two]
  have h0 : edgeSum (redBlue v) (sqTris 0) =
      redBlue v (0, 0) (1, 0) + redBlue v (1, 0) (1, 1) + redBlue v (1, 1) (0, 0) := rfl
  have h1 : edgeSum (redBlue v) (sqTris 1) =
      redBlue v (0, 0) (1, 1) + redBlue v (1, 1) (0, 1) + redBlue v (0, 1) (0, 0) := rfl
  rw [h0, h1]
  simp only [redBlue, color_zero_zero, color_one_zero, color_one_one, color_zero_one]
  decide

open Classical in
/-- **Lemma 2.** Every dissection of the unit square `S = [0, 1]²` into finitely many triangles
contains an odd number of rainbow triangles. (This holds for the coloring associated with any
non-Archimedean valuation `v` of `ℝ`.) -/
theorem lemma2 {ι : Type*} [Fintype ι] {T : ι → Triangle} (hT : IsDissection T) :
    Odd (Finset.univ.filter fun i => IsRainbow v (T i)).card := by
  classical
  have key := sum_edgeSum_eq T sqTris hT.nondegenerate sqTris_nondegenerate hT.sameCoverMod2
    (lineAdditive_redBlue v)
  rw [sum_edgeSum_sqTris] at key
  simp only [edgeSum_redBlue] at key
  rw [Finset.sum_boole] at key
  exact ZMod.natCast_eq_one_iff_odd.1 (by convert key)

/-- **Lemma 2** (second part): every dissection of the unit square into finitely many triangles
contains at least one rainbow triangle. -/
theorem exists_isRainbow {ι : Type*} [Fintype ι] {T : ι → Triangle} (hT : IsDissection T) :
    ∃ i, IsRainbow v (T i) := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (lemma2 v hT).pos
  exact ⟨i, (Finset.mem_filter.1 hi).2⟩

end Chapter22

/-!
# Appendix: Extending valuations

We formalize the appendix of Chapter 22:

* **Definition.** A non-Archimedean valuation `v : K → {0} ∪ G` with values in an ordered abelian
  group `G` is, in Mathlib, a `Valuation K Γ₀` where `Γ₀` is a `LinearOrderedCommGroupWithZero`
  (playing the role of `{0} ∪ G`). We show that such valuations satisfy (i)–(iv), and conversely
  that any map satisfying (i), (ii), (iii') is such a valuation (`valuationOfAxioms`).
* The valuation ring `R = {x | v x ≤ 1}` and its units `U = {x | v x = 1}`, and `K = R ∪ R⁻¹`.
* **Lemma.** A subring `R ⊆ K` is the valuation ring of some valuation into some ordered group
  if and only if `K = R ∪ R⁻¹`.
* **Zorn's Lemma** and the existence of an inclusion-maximal subring `B ⊆ ℝ` with `1/2 ∉ B`.
* **Claim.** Any inclusion-maximal subring `B ⊆ ℝ` with `1/2 ∉ B` is a valuation ring.
* **Theorem.** The field `ℝ` has a non-Archimedean valuation `v` into an ordered abelian group
  with `v (1/2) > 1`.
-/


namespace Chapter22

universe u

section Definition

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Definition** (properties (i)–(iv)): a Mathlib valuation with values in a linearly ordered
commutative group with zero satisfies the four defining properties of the book. -/
theorem valuation_properties (v : Valuation K Γ₀) :
    (∀ x, v x = 0 ↔ x = 0) ∧ (∀ x y, v (x * y) = v x * v y) ∧
    (∀ x y, v (x + y) ≤ max (v x) (v y)) ∧
    (∀ x y, v x ≠ v y → v (x + y) = max (v x) (v y)) := by
  refine ⟨fun x => v.zero_iff, v.map_mul, v.map_add, fun x y h => ?_⟩
  rcases lt_or_gt_of_ne h with h | h
  · rw [v.map_add_eq_of_lt_right h, max_eq_right h.le]
  · rw [v.map_add_eq_of_lt_left h, max_eq_left h.le]

/-- Conversely, a map satisfying (i), (ii) and (iii') is a valuation (property (iv) is implied
by the first three). -/
def valuationOfAxioms (v : K → Γ₀) (h0 : ∀ x, v x = 0 ↔ x = 0)
    (hmul : ∀ x y, v (x * y) = v x * v y) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y)) :
    Valuation K Γ₀ where
  toFun := v
  map_zero' := (h0 0).2 rfl
  map_one' := by
    have h1 : v 1 ≠ 0 := fun h => one_ne_zero ((h0 1).1 h)
    have := hmul 1 1
    rw [one_mul] at this
    exact (mul_eq_left₀ h1).1 this.symm
  map_mul' := hmul
  map_add_le_max' := hadd

theorem valuationOfAxioms_apply (v : K → Γ₀) (h0 : ∀ x, v x = 0 ↔ x = 0)
    (hmul : ∀ x y, v (x * y) = v x * v y) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y)) (x : K) :
    valuationOfAxioms v h0 hmul hadd x = v x := rfl

/-! ### The valuation ring of a valuation -/

/-- The valuation ring `R = {x ∈ K | v x ≤ 1}` is a subring of `K` (in Mathlib: `v.integer`). -/
theorem mem_valuationRing_iff (v : Valuation K Γ₀) (x : K) : x ∈ v.integer ↔ v x ≤ 1 :=
  Iff.rfl

/-- The units of the valuation ring are the elements of value `1`. -/
theorem isUnit_valuationRing_iff (v : Valuation K Γ₀) (x : v.integer) :
    IsUnit x ↔ v (x : K) = 1 :=
  (Valuation.integer.integers v).isUnit_iff_valuation_eq_one

/-- `v(x) = 1` if and only if `v(x⁻¹) = 1`. -/
theorem valuation_eq_one_iff_inv (v : Valuation K Γ₀) (x : K) : v x = 1 ↔ v x⁻¹ = 1 := by
  rw [v.map_inv, inv_eq_one]

/-- `K = R ∪ R⁻¹`. -/
theorem mem_or_inv_mem_valuationRing (v : Valuation K Γ₀) (x : K) :
    x ∈ v.integer ∨ x⁻¹ ∈ v.integer := by
  simp only [mem_valuationRing_iff, v.map_inv]
  rcases le_total (v x) 1 with h | h
  · exact Or.inl h
  · exact Or.inr (inv_le_one_of_one_le₀ h)

/-- **Lemma.** A subring `R ⊆ K` is the valuation ring with respect to some valuation `v` into
some ordered group if and only if `K = R ∪ R⁻¹`. -/
theorem isValuationRing_iff {K : Type u} [Field K] (R : Subring K) :
    (∃ (Γ : Type u) (_ : LinearOrderedCommGroupWithZero Γ) (v : Valuation K Γ),
      ∀ x, x ∈ R ↔ v x ≤ 1) ↔ ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R := by
  constructor
  · rintro ⟨Γ, _, v, hv⟩ x
    rw [hv, hv]
    exact mem_or_inv_mem_valuationRing v x
  · intro h
    let A : ValuationSubring K := { R with mem_or_inv_mem' := h }
    exact ⟨A.ValueGroup, inferInstance, A.valuation, fun x => (A.valuation_le_one_iff x).symm⟩

end Definition

/-! ### Zorn's Lemma and maximal subrings not containing `1/2` -/

/-- **Zorn's Lemma.** A nonempty partially ordered set in which every chain has an upper bound
has a maximal element. -/
theorem zorns_lemma {P : Type*} [PartialOrder P]
    (h : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ b, ∀ a ∈ c, a ≤ b) :
    ∃ M : P, ∀ c, ¬ M < c := by
  obtain ⟨M, hM⟩ := zorn_le (fun c hc => h c hc)
  exact ⟨M, fun c hc => hM.not_lt hc⟩

theorem half_not_mem_bot : (1 / 2 : ℝ) ∉ (⊥ : Subring ℝ) := by
  rw [Subring.mem_bot]
  rintro ⟨n, hn⟩
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; rw [hn]; norm_num
  have : 2 * n = 1 := by exact_mod_cast h2
  omega

/-- There is an inclusion-maximal subring `B ⊆ ℝ` with `1/2 ∉ B`. -/
theorem exists_maximal_subring_half_not_mem :
    ∃ B : Subring ℝ, (1 / 2 : ℝ) ∉ B ∧ ∀ B' : Subring ℝ, B ≤ B' → (1 / 2 : ℝ) ∉ B' → B' = B := by
  obtain ⟨B, -, hB⟩ := zorn_le_nonempty₀ {B : Subring ℝ | (1 / 2 : ℝ) ∉ B} (by
    intro c hcs hc y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hdir : Directed (· ≤ ·) (Subtype.val : c → Subring ℝ) :=
      (hc.directedOn).directed_val
    refine ⟨⨆ B : c, B.1, ?_, fun z hz => le_iSup (fun B : c => B.1) ⟨z, hz⟩⟩
    intro hmem
    obtain ⟨B, hB⟩ := (Subring.mem_iSup_of_directed hdir).1 hmem
    exact hcs B.2 hB) ⊥ half_not_mem_bot
  exact ⟨B, hB.prop, fun B' hle hB' => le_antisymm (hB.2 hB' hle) hle⟩

/-! ### The Claim -/

/-- **Claim.** Any inclusion-maximal subring `B ⊆ ℝ` with the property `1/2 ∉ B` is a valuation
ring, i.e. `ℝ = B ∪ B⁻¹`. -/
theorem maximal_subring_isValuationRing (B : Subring ℝ) (hB : (1 / 2 : ℝ) ∉ B)
    (hmax : ∀ B' : Subring ℝ, B ≤ B' → (1 / 2 : ℝ) ∉ B' → B' = B) :
    ∀ x : ℝ, x ∈ B ∨ x⁻¹ ∈ B := by
  let two : B := ⟨2, by exact_mod_cast natCast_mem B 2⟩
  have hI : Ideal.span {two} ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ Ideal.span {two} := htop ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h1
    apply hB
    have : (b : ℝ) * 2 = 1 := by simpa [two] using congrArg Subtype.val hb
    have hb' : (b : ℝ) = 1 / 2 := by linarith
    exact hb' ▸ b.2
  obtain ⟨V, hBV, hnon⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  have h2 : (2 : ℝ) ∈ V.nonunits := hnon ⟨two, Ideal.subset_span rfl, rfl⟩
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have hV : (1 / 2 : ℝ) ∉ V := by
    rw [← ValuationSubring.valuation_le_one_iff, one_div, Valuation.map_inv, not_le]
    exact (one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm ((V.valuation.ne_zero_iff).2
      two_ne_zero)))).2 h2
  have hEq : V.toSubring = B := hmax V.toSubring hBV hV
  intro x
  rw [← hEq]
  exact V.mem_or_inv_mem x

/-! ### The Theorem -/

/-- **Theorem.** The field of real numbers `ℝ` has a non-Archimedean valuation `v` with values
in an ordered abelian group (with zero adjoined) such that `v (1/2) > 1`. -/
theorem exists_valuation_half_gt_one :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (v : Valuation ℝ Γ), 1 < v (1 / 2) := by
  obtain ⟨B, hB, hmax⟩ := exists_maximal_subring_half_not_mem
  obtain ⟨Γ, inst, v, hv⟩ :=
    (isValuationRing_iff B).2 (maximal_subring_isValuationRing B hB hmax)
  exact ⟨Γ, inst, v, lt_of_not_ge fun h => hB ((hv _).2 h)⟩

end Chapter22

/-!
# Monsky's Theorem

It is not possible to dissect a square into an odd number of triangles of equal area.

By scaling we restrict to the unit square `[0, 1]²`; the triangles of a dissection into `n`
triangles of equal area then all have area `1/n`.
-/


namespace Chapter22

/-- **Monsky's Theorem.** There is no dissection of the unit square into an odd number `n` of
triangles all of which have area `1/n`. -/
theorem monsky {ι : Type*} [Fintype ι] {T : ι → Triangle} (hT : IsDissection T)
    (hodd : Odd (Fintype.card ι)) : ¬ ∀ i, triArea (T i) = 1 / Fintype.card ι := by
  intro harea
  obtain ⟨Γ, _, v, hv⟩ := exists_valuation_half_gt_one
  obtain ⟨i, hi⟩ := exists_isRainbow v hT
  exact triArea_ne_one_div_odd_of_isRainbow v hv hi hodd (harea i)

/-- **Monsky's Theorem** (formulation with `n` triangles indexed by `Fin n`): it is not possible
to dissect the unit square into an odd number `n` of triangles of area `1/n` each. -/
theorem monsky_fin : ¬ ∃ (n : ℕ) (T : Fin n → Triangle),
    Odd n ∧ IsDissection T ∧ ∀ i, triArea (T i) = 1 / n := by
  rintro ⟨n, T, hodd, hT, harea⟩
  exact monsky hT (by simpa using hodd) (by simpa using harea)

end Chapter22

/-!
# p-adic values

The introductory part of Chapter 22: for a prime `p`, the `p`-adic value `|r|_p = p^(-k)` of
`r = p^k a/b` (Mathlib's `padicNorm p`) satisfies (i), (ii) and the non-Archimedean property
(iii'), and also (iv). We verify the book's examples
`|3/4|₂ = 4`, `|6/7|₂ = |2|₂ = 1/2` and `|3/4 + 6/7|₂ = |45/28|₂ = 4 = max {|3/4|₂, |6/7|₂}`.
-/


namespace Chapter22

/-- The `p`-adic value satisfies (i), (ii), (iii') and (iv). -/
theorem padicNorm_properties (p : ℕ) [Fact p.Prime] :
    (∀ x : ℚ, padicNorm p x = 0 ↔ x = 0) ∧
    (∀ x y : ℚ, padicNorm p (x * y) = padicNorm p x * padicNorm p y) ∧
    (∀ x y : ℚ, padicNorm p (x + y) ≤ max (padicNorm p x) (padicNorm p y)) ∧
    (∀ x y : ℚ, padicNorm p x ≠ padicNorm p y →
      padicNorm p (x + y) = max (padicNorm p x) (padicNorm p y)) :=
  ⟨fun _ => ⟨padicNorm.zero_of_padicNorm_eq_zero, fun h => by rw [h, padicNorm.zero]⟩,
    fun _ _ => padicNorm.mul _ _, fun _ _ => padicNorm.nonarchimedean,
    fun _ _ h => padicNorm.add_eq_max_of_ne h⟩

theorem padicNorm_two_of_odd (m : ℕ) (h : ¬ 2 ∣ m) : padicNorm 2 (m : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff m).2 h

theorem padicNorm_two_two : padicNorm 2 (2 : ℚ) = 1 / 2 := by
  have := padicNorm.padicNorm_p_of_prime (p := 2); simpa using this

/-- `|3/4|₂ = 4`. -/
theorem padicNorm_two_three_quarters : padicNorm 2 (3 / 4) = 4 := by
  rw [padicNorm.div, show (4 : ℚ) = 2 * 2 by norm_num, padicNorm.mul, padicNorm_two_two,
    show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicNorm_two_of_odd 3 (by norm_num)]
  norm_num

/-- `|6/7|₂ = 1/2`. -/
theorem padicNorm_two_six_sevenths : padicNorm 2 (6 / 7) = 1 / 2 := by
  rw [padicNorm.div, show (6 : ℚ) = 2 * ((3 : ℕ) : ℚ) by norm_num, padicNorm.mul,
    padicNorm_two_two, show (7 : ℚ) = ((7 : ℕ) : ℚ) by norm_num,
    padicNorm_two_of_odd 3 (by norm_num), padicNorm_two_of_odd 7 (by norm_num)]
  norm_num

/-- `|3/4 + 6/7|₂ = |45/28|₂ = 4 = max {|3/4|₂, |6/7|₂}`. -/
theorem padicNorm_two_sum_example :
    padicNorm 2 (3 / 4 + 6 / 7) = 4 ∧
      padicNorm 2 (3 / 4 + 6 / 7) = max (padicNorm 2 (3 / 4)) (padicNorm 2 (6 / 7)) := by
  have h : padicNorm 2 (3 / 4 + 6 / 7) = 4 := by
    rw [show (3 / 4 + 6 / 7 : ℚ) = ((45 : ℕ) : ℚ) / (2 * 2 * ((7 : ℕ) : ℚ)) by norm_num,
      padicNorm.div, padicNorm.mul, padicNorm.mul, padicNorm_two_two,
      padicNorm_two_of_odd 45 (by norm_num), padicNorm_two_of_odd 7 (by norm_num)]
    norm_num
  refine ⟨h, ?_⟩
  rw [h, padicNorm_two_three_quarters, padicNorm_two_six_sevenths]
  norm_num

end Chapter22

/-!
# Areas of triangles and the equal-area form of Monsky's theorem

We connect the shoelace formula `triArea` with Lebesgue measure: the area (two-dimensional
Lebesgue measure) of the closed triangular region of a non-degenerate triangle `t` is
`triArea t`. Consequently the areas of the triangles of a dissection of the unit square add up
to `1`, and Monsky's theorem can be stated literally: the unit square cannot be dissected into an
odd number of triangles of equal area.

We also check that the dissection of the square along a diagonal is a dissection in our sense.
-/


namespace Chapter22

open MeasureTheory Filter Topology

/-! ### The dissection of the square along a diagonal -/

theorem not_isOpen_subset_diagonal {U : Set (ℝ × ℝ)} (hU : IsOpen U) {z : ℝ × ℝ} (hz : z ∈ U)
    (hsub : U ⊆ {p | p.1 = p.2}) : False := by
  have hT : Tendsto (fun ε : ℝ => z + (ε, 0)) (𝓝 0) (𝓝 z) := by
    have : Tendsto (fun ε : ℝ => z + (ε, 0)) (𝓝 0) (𝓝 (z + (0, 0))) :=
      (Continuous.tendsto (by fun_prop) 0)
    simpa [Prod.mk_zero_zero] using this
  have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), z + (ε, 0) ∈ U :=
    (hT.eventually (hU.mem_nhds hz)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hne⟩ := (h1.and self_mem_nhdsWithin).exists
  have h2 := hsub hε
  have h3 := hsub hz
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, add_zero] at h2 h3
  apply hne
  rw [Set.mem_singleton_iff]
  linarith

/-- The two halves of the square form a dissection of the unit square. -/
theorem isDissection_sqTris : IsDissection sqTris := by
  refine ⟨sqTris_nondegenerate, ?_, ?_⟩
  · ext z
    simp only [Set.mem_iUnion, Fin.exists_fin_two, sqTris, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mem_sqTri0_iff, mem_sqTri1_iff,
      mem_unitSquare_iff]
    constructor
    · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
      · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      rcases le_total z.2 z.1 with h | h
      · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith, by linarith⟩
  · have key : Disjoint (interior (triRegion sqTri0)) (interior (triRegion sqTri1)) := by
      rw [Set.disjoint_left]
      intro z hz0 hz1
      refine not_isOpen_subset_diagonal (isOpen_interior.inter isOpen_interior) ⟨hz0, hz1⟩ ?_
      rintro p ⟨hp0, hp1⟩
      have a := (mem_sqTri0_iff p).1 (interior_subset hp0)
      have b := (mem_sqTri1_iff p).1 (interior_subset hp1)
      show p.1 = p.2
      linarith [a.2.1, b.2.2]
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key
    · exact key.symm
    · exact absurd rfl hij

/-! ### Volume of a triangle -/

/-- The linear map `(a, b) ↦ a • u + b • w`. -/
noncomputable def linT (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

theorem linT_apply (u w z : ℝ × ℝ) : linT u w z = z.1 • u + z.2 • w := rfl

theorem det_linT (u w : ℝ × ℝ) : LinearMap.det (linT u w) = det2 u w := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, linT, det2]
  ring

/-- The standard triangle with vertices `(0,0), (1,0), (0,1)`. -/
def stdTri : Triangle := ![(0, 0), (1, 0), (0, 1)]

theorem triRegion_eq_image (t : Triangle) :
    triRegion t = (fun z => t 0 + z) '' (linT (t 1 - t 0) (t 2 - t 0) '' triRegion stdTri) := by
  let φ : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
    (linT (t 1 - t 0) (t 2 - t 0)).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) (t 0)
  have hφ : ∀ z, φ z = t 0 + linT (t 1 - t 0) (t 2 - t 0) z := fun z => by
    simp [φ, add_comm]
  have himg : (fun z => t 0 + z) '' (linT (t 1 - t 0) (t 2 - t 0) '' triRegion stdTri) =
      φ '' triRegion stdTri := by
    rw [Set.image_image]
    exact Set.image_congr fun z _ => (hφ z).symm
  rw [himg, triRegion, triRegion, AffineMap.image_convexHull]
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    rw [hφ]
    fin_cases i <;> simp [stdTri, linT_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    rw [hφ]
    fin_cases i <;> simp [stdTri, linT_apply]

theorem volume_image_add_left (a : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    volume ((fun z => a + z) '' A) = volume A := by
  rw [Set.image_add_left]
  exact measure_preimage_add _ _ _

theorem volume_triRegion_eq_mul (t : Triangle) :
    volume (triRegion t) = ENNReal.ofReal |triDet t| * volume (triRegion stdTri) := by
  rw [triRegion_eq_image, volume_image_add_left, Measure.addHaar_image_linearMap, det_linT]
  rfl

theorem isClosed_triRegion (t : Triangle) : IsClosed (triRegion t) :=
  (Set.finite_range t).isCompact_convexHull ℝ |>.isClosed

/-- Additivity of area for triangles with pairwise disjoint interiors. -/
theorem volume_iUnion_triRegion {ι : Type*} [Fintype ι] (T : ι → Triangle)
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (triRegion (T i))) (interior (triRegion (T j)))) :
    volume (⋃ i, triRegion (T i)) = ∑ i, volume (triRegion (T i)) := by
  rw [measure_iUnion₀ _ (fun i => (isClosed_triRegion (T i)).measurableSet.nullMeasurableSet),
    tsum_fintype]
  intro i j hij
  show volume (triRegion (T i) ∩ triRegion (T j)) = 0
  refine measure_mono_null (t := frontier (triRegion (T i)) ∪ frontier (triRegion (T j)))
    ?_ (measure_union_null (Convex.addHaar_frontier _ (convex_convexHull ℝ _))
      (Convex.addHaar_frontier _ (convex_convexHull ℝ _)))
  rintro z ⟨hzi, hzj⟩
  by_cases h : z ∈ interior (triRegion (T i))
  · right
    refine ⟨subset_closure hzj, fun h' => ?_⟩
    exact Set.disjoint_left.1 (hdisj i j hij) h h'
  · left
    exact ⟨subset_closure hzi, h⟩

theorem volume_unitSquare : volume unitSquare = 1 := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

theorem volume_stdTri : volume (triRegion stdTri) = 1 / 2 := by
  have h := volume_iUnion_triRegion sqTris isDissection_sqTris.disjoint_interior
  rw [isDissection_sqTris.iUnion_eq, volume_unitSquare, Fin.sum_univ_two,
    volume_triRegion_eq_mul (sqTris 0), volume_triRegion_eq_mul (sqTris 1)] at h
  simp only [sqTris, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    triDet_sqTri0, triDet_sqTri1, abs_one, ENNReal.ofReal_one, one_mul] at h
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), two_mul]
  exact h.symm

/-- The two-dimensional Lebesgue measure of the region of a triangle is given by the shoelace
formula `triArea`. -/
theorem volume_triRegion (t : Triangle) : volume (triRegion t) = ENNReal.ofReal (triArea t) := by
  rw [volume_triRegion_eq_mul, volume_stdTri, triArea, ENNReal.ofReal_div_of_pos two_pos,
    ENNReal.ofReal_ofNat, mul_one_div]

/-- The areas of the triangles of a dissection of the unit square add up to `1`. -/
theorem IsDissection.sum_triArea {ι : Type*} [Fintype ι] {T : ι → Triangle}
    (hT : IsDissection T) : ∑ i, triArea (T i) = 1 := by
  have h := volume_iUnion_triRegion T hT.disjoint_interior
  rw [hT.iUnion_eq, volume_unitSquare] at h
  simp only [volume_triRegion] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by unfold triArea; positivity)] at h
  exact (ENNReal.ofReal_eq_one.1 h.symm)

/-- **Monsky's Theorem** (equal-area form): it is not possible to dissect the unit square into
an odd number of triangles of equal area. -/
theorem monsky_equal_area {ι : Type*} [Fintype ι] {T : ι → Triangle} (hT : IsDissection T)
    (hodd : Odd (Fintype.card ι)) : ¬ ∀ i j, triArea (T i) = triArea (T j) := by
  intro heq
  have hne : Nonempty ι := Fintype.card_pos_iff.1 hodd.pos
  obtain ⟨i₀⟩ := hne
  apply monsky hT hodd
  intro i
  have hsum := hT.sum_triArea
  rw [Finset.sum_congr rfl fun j _ => heq j i₀, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  rw [heq i i₀, eq_div_iff hc]
  linarith

/-- **Monsky's Theorem** (equal-area form, `Fin n` version). -/
theorem monsky_equal_area_fin : ¬ ∃ (n : ℕ) (T : Fin n → Triangle),
    Odd n ∧ IsDissection T ∧ ∀ i j, triArea (T i) = triArea (T j) := by
  rintro ⟨n, T, hodd, hT, harea⟩
  exact monsky_equal_area hT (by simpa using hodd) harea

end Chapter22

/-!
# Dissections into an even number of triangles of equal area

"Suppose we want to dissect a square into `n` triangles of equal area. When `n` is even, this is
easily accomplished. For example, you could divide the horizontal sides into `n/2` segments of
equal length and draw a diagonal in each of the `n/2` rectangles."

We formalize this construction.
-/


namespace Chapter22

open Filter Topology

/-- Points in the interior of a triangle have positive barycentric coordinates. -/
theorem bary_pos_of_mem_interior {t : Triangle} (ht : triDet t ≠ 0) {z : ℝ × ℝ}
    (hz : z ∈ interior (triRegion t)) (k : Fin 3) : 0 < bary t k z := by
  have h0 : 0 ≤ bary t k z := (mem_triRegion_iff ht z).1 (interior_subset hz) k
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  set w := t (k + 1) - t k with hw
  have hlin : baryLin t k w = -1 := by
    have := bary_add t k (t k) w
    have hk : k ≠ k + 1 := by fin_cases k <;> decide
    simp [hw, bary_vertex ht, hk] at this
    linarith
  have hT : Tendsto (fun ε : ℝ => z + ε • w) (𝓝 0) (𝓝 z) := by
    have : Tendsto (fun ε : ℝ => z + ε • w) (𝓝 0) (𝓝 (z + (0 : ℝ) • w)) :=
      (Continuous.tendsto (by fun_prop) 0)
    simpa using this
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), z + ε • w ∈ interior (triRegion t) :=
    (hT.eventually (isOpen_interior.mem_nhds hz)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε, hpos⟩ := (h1.and self_mem_nhdsWithin).exists
  have h2 := (mem_triRegion_iff ht _).1 (interior_subset hε) k
  rw [bary_add, baryLin_smul, hlin, ← h] at h2
  have : (0 : ℝ) < ε := hpos
  linarith

/-- The interior of a non-degenerate triangle consists of the points with positive barycentric
coordinates. -/
theorem mem_interior_triRegion_iff {t : Triangle} (ht : triDet t ≠ 0) (z : ℝ × ℝ) :
    z ∈ interior (triRegion t) ↔ ∀ k, 0 < bary t k z :=
  ⟨fun h k => bary_pos_of_mem_interior ht h k, mem_interior_triRegion ht⟩

/-- Reindexing a dissection along a bijection gives a dissection. -/
theorem IsDissection.comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ι → Triangle}
    (hT : IsDissection T) (e : κ ≃ ι) : IsDissection (T ∘ e) := by
  refine ⟨fun j => hT.nondegenerate (e j), ?_, fun i j hij =>
    hT.disjoint_interior (e i) (e j) (e.injective.ne hij)⟩
  rw [← hT.iUnion_eq]
  exact e.surjective.iUnion_comp (fun i => triRegion (T i))

/-! ### The strips -/

/-- The lower-right triangle in the `k`-th of `m` vertical strips. -/
noncomputable def lowTri (m : ℕ) (k : ℕ) : Triangle :=
  ![((k : ℝ) / m, 0), ((k + 1 : ℝ) / m, 0), ((k + 1 : ℝ) / m, 1)]

/-- The upper-left triangle in the `k`-th of `m` vertical strips. -/
noncomputable def upTri (m : ℕ) (k : ℕ) : Triangle :=
  ![((k : ℝ) / m, 0), ((k + 1 : ℝ) / m, 1), ((k : ℝ) / m, 1)]

theorem triDet_lowTri (m k : ℕ) : triDet (lowTri m k) = 1 / m := by
  simp [triDet, lowTri, det2]
  ring

theorem triDet_upTri (m k : ℕ) : triDet (upTri m k) = 1 / m := by
  simp [triDet, upTri, det2]
  ring

theorem bary_lowTri {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    bary (lowTri m k) 0 z = (k + 1) - m * z.1 ∧
      bary (lowTri m k) 1 z = (m * z.1 - k) - z.2 ∧ bary (lowTri m k) 2 z = z.2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_, ?_, ?_⟩ <;> simp [bary, lowTri, triDet, det2] <;> field_simp <;> ring

theorem bary_upTri {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    bary (upTri m k) 0 z = 1 - z.2 ∧
      bary (upTri m k) 1 z = m * z.1 - k ∧ bary (upTri m k) 2 z = z.2 - (m * z.1 - k) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_, ?_, ?_⟩ <;> simp [bary, upTri, triDet, det2] <;> field_simp <;> ring

theorem mem_lowTri_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    z ∈ triRegion (lowTri m k) ↔ m * z.1 - k ≤ 1 ∧ z.2 ≤ m * z.1 - k ∧ 0 ≤ z.2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_triRegion_iff (by rw [triDet_lowTri]; simpa using hm'), forall_fin3_iff,
    (bary_lowTri hm k z).1, (bary_lowTri hm k z).2.1, (bary_lowTri hm k z).2.2]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_upTri_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    z ∈ triRegion (upTri m k) ↔ z.2 ≤ 1 ∧ 0 ≤ m * z.1 - k ∧ m * z.1 - k ≤ z.2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_triRegion_iff (by rw [triDet_upTri]; simpa using hm'), forall_fin3_iff,
    (bary_upTri hm k z).1, (bary_upTri hm k z).2.1, (bary_upTri hm k z).2.2]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_interior_lowTri_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    z ∈ interior (triRegion (lowTri m k)) ↔ m * z.1 - k < 1 ∧ z.2 < m * z.1 - k ∧ 0 < z.2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_interior_triRegion_iff (by rw [triDet_lowTri]; simpa using hm'), forall_fin3_iff,
    (bary_lowTri hm k z).1, (bary_lowTri hm k z).2.1, (bary_lowTri hm k z).2.2]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_interior_upTri_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (z : ℝ × ℝ) :
    z ∈ interior (triRegion (upTri m k)) ↔ z.2 < 1 ∧ 0 < m * z.1 - k ∧ m * z.1 - k < z.2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_interior_triRegion_iff (by rw [triDet_upTri]; simpa using hm'), forall_fin3_iff,
    (bary_upTri hm k z).1, (bary_upTri hm k z).2.1, (bary_upTri hm k z).2.2]
  constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The `2m` triangles obtained by dividing the square into `m` vertical strips and drawing a
diagonal in each strip. -/
noncomputable def stripTris (m : ℕ) (p : Fin m × Fin 2) : Triangle :=
  if p.2 = 0 then lowTri m p.1 else upTri m p.1

theorem mem_stripTris_iff {m : ℕ} (hm : 0 < m) (p : Fin m × Fin 2) (z : ℝ × ℝ) :
    z ∈ triRegion (stripTris m p) ↔
      if p.2 = 0 then m * z.1 - p.1 ≤ 1 ∧ z.2 ≤ m * z.1 - p.1 ∧ 0 ≤ z.2
      else z.2 ≤ 1 ∧ 0 ≤ m * z.1 - p.1 ∧ m * z.1 - p.1 ≤ z.2 := by
  unfold stripTris
  split_ifs
  · exact mem_lowTri_iff hm _ z
  · exact mem_upTri_iff hm _ z

theorem mem_interior_stripTris_iff {m : ℕ} (hm : 0 < m) (p : Fin m × Fin 2) (z : ℝ × ℝ) :
    z ∈ interior (triRegion (stripTris m p)) ↔
      if p.2 = 0 then m * z.1 - p.1 < 1 ∧ z.2 < m * z.1 - p.1 ∧ 0 < z.2
      else z.2 < 1 ∧ 0 < m * z.1 - p.1 ∧ m * z.1 - p.1 < z.2 := by
  unfold stripTris
  split_ifs
  · exact mem_interior_lowTri_iff hm _ z
  · exact mem_interior_upTri_iff hm _ z

theorem isDissection_stripTris {m : ℕ} (hm : 0 < m) : IsDissection (stripTris m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun p => ?_, ?_, ?_⟩
  · unfold stripTris
    split_ifs
    · rw [triDet_lowTri]; positivity
    · rw [triDet_upTri]; positivity
  · ext z
    simp only [Set.mem_iUnion, mem_stripTris_iff hm, mem_unitSquare_iff]
    constructor
    · rintro ⟨⟨k, c⟩, hz⟩
      have hk : (k : ℝ) + 1 ≤ m := by exact_mod_cast k.2
      have hk0 : (0 : ℝ) ≤ k := by positivity
      split_ifs at hz with hc
      · obtain ⟨h0, h1, h2⟩ := hz
        refine ⟨⟨?_, ?_⟩, h2, ?_⟩
        · nlinarith
        · rw [← mul_le_mul_iff_of_pos_left hm']; linarith
        · linarith
      · obtain ⟨h0, h1, h2⟩ := hz
        refine ⟨⟨?_, ?_⟩, by linarith, h0⟩
        · nlinarith
        · rw [← mul_le_mul_iff_of_pos_left hm']; linarith
    · rintro ⟨⟨hx0, hx1⟩, hy0, hy1⟩
      -- choose the strip containing `z.1`
      set k := min ⌊(m : ℝ) * z.1⌋₊ (m - 1) with hkdef
      have hkm : k < m := by omega
      have hmx : 0 ≤ (m : ℝ) * z.1 := by positivity
      have hs0 : (k : ℝ) ≤ m * z.1 :=
        le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le hmx)
      have hs1 : (m : ℝ) * z.1 - k ≤ 1 := by
        rcases le_total ⌊(m : ℝ) * z.1⌋₊ (m - 1) with h | h
        · have : k = ⌊(m : ℝ) * z.1⌋₊ := min_eq_left h
          rw [this]
          linarith [Nat.lt_floor_add_one ((m : ℝ) * z.1)]
        · have : k = m - 1 := min_eq_right h
          rw [this, Nat.cast_sub (by omega)]
          push_cast
          nlinarith
      by_cases hy : z.2 ≤ m * z.1 - k
      · exact ⟨(⟨k, hkm⟩, 0), by simp only [ite_true]; exact ⟨hs1, hy, hy0⟩⟩
      · refine ⟨(⟨k, hkm⟩, 1), ?_⟩
        simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
        exact ⟨hy1, by linarith, by linarith⟩
  · rintro ⟨k, c⟩ ⟨k', c'⟩ hne
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [mem_interior_stripTris_iff hm] at hz hz'
    simp only at hz hz'
    rcases lt_trichotomy (k : ℕ) k' with hlt | heq | hgt
    · have hkk : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
      split_ifs at hz hz' <;> linarith [hz.1, hz.2.1, hz.2.2, hz'.1, hz'.2.1, hz'.2.2]
    · have hk : k = k' := Fin.ext heq
      subst hk
      have hc : c ≠ c' := fun h => hne (by rw [h])
      split_ifs at hz hz' with h1 h2 h2
      · exact hc (h1.trans h2.symm)
      · linarith [hz.1, hz.2.1, hz.2.2, hz'.1, hz'.2.1, hz'.2.2]
      · linarith [hz.1, hz.2.1, hz.2.2, hz'.1, hz'.2.1, hz'.2.2]
      · exact hc (by omega)
    · have hkk : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hgt
      split_ifs at hz hz' <;> linarith [hz.1, hz.2.1, hz.2.2, hz'.1, hz'.2.1, hz'.2.2]

theorem triArea_stripTris (m : ℕ) (p : Fin m × Fin 2) :
    triArea (stripTris m p) = 1 / (2 * m) := by
  unfold stripTris triArea
  split_ifs
  · rw [triDet_lowTri, abs_of_nonneg (by positivity)]; ring
  · rw [triDet_upTri, abs_of_nonneg (by positivity)]; ring

/-- **Even case.** For every even `n > 0` the unit square can be dissected into `n` triangles of
equal area `1/n`. -/
theorem exists_dissection_even {n : ℕ} (hn : Even n) (hpos : 0 < n) :
    ∃ T : Fin n → Triangle, IsDissection T ∧ ∀ i, triArea (T i) = 1 / n := by
  obtain ⟨m, rfl⟩ := hn
  have hm : 0 < m := by omega
  let e : Fin (m + m) ≃ Fin m × Fin 2 :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨stripTris m ∘ e, (isDissection_stripTris hm).comp_equiv e, fun i => ?_⟩
  rw [Function.comp_apply, triArea_stripTris]
  push_cast
  ring

end Chapter22
