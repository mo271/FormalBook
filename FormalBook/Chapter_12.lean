/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the supplied chapter stub: Moritz Firsching, AItoBit
-/
module

import Mathlib

/-!
# Chapter 12 — The slope problem
Source: Aigner and Ziegler, *Proofs from THE BOOK*, supplied 2018 chapter,
printed pages 83–87. This is an INCOMPLETE, kernel-checked development.
The general Ungar bound is not asserted here.
Directions include the vertical direction (`none`), which must not be lost
by using real division alone. Finsets ensure that the points are distinct.
-/

namespace Chapter12

abbrev Point := ℝ × ℝ

/-- Printed p. 83: an unoriented slope, including vertical lines. Only
pairs of distinct points are counted in `directions`. -/
noncomputable def direction (p q : Point) : Option ℝ :=
  if q.1 = p.1 then none else some ((q.2 - p.2) / (q.1 - p.1))

/-- Twice the signed area of the triangle `p,q,r`. -/
def area (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- A coordinate description of noncollinearity; related to Mathlib below. -/
def Noncollinear (S : Finset Point) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, area p q r ≠ 0

/-- Printed p. 83: all slopes determined by a finite point configuration. -/
noncomputable def directions (S : Finset Point) : Finset (Option ℝ) := by
  classical
  exact ((S ×ˢ S).filter fun pq => pq.1 ≠ pq.2).image fun pq => direction pq.1 pq.2

noncomputable def slopeCount (S : Finset Point) : ℕ := (directions S).card

@[simp] theorem direction_comm (p q : Point) : direction p q = direction q p := by
  unfold direction
  by_cases h : q.1 = p.1
  · simp [h]
  · have h' : p.1 ≠ q.1 := Ne.symm h
    simp only [h, h', ↓reduceIte, Option.some.injEq]
    rw [← neg_sub p.2 q.2, ← neg_sub p.1 q.1, neg_div_neg_eq]

@[simp] theorem area_self_left (p r : Point) : area p p r = 0 := by simp [area]
@[simp] theorem area_self_right (p q : Point) : area p q p = 0 := by simp [area]
@[simp] theorem area_self_last (p q : Point) : area p q q = 0 := by unfold area; ring

theorem area_swap (p q r : Point) : area q p r = -area p q r := by unfold area; ring
theorem area_rotate (p q r : Point) : area q r p = area p q r := by unfold area; ring

/-- Two segments from the same base point with the same direction have zero area. -/
theorem area_eq_zero_of_direction_eq {p q r : Point} (h : direction p q = direction p r) :
    area p q r = 0 := by
  unfold direction at h
  by_cases hq : q.1 = p.1 <;> by_cases hr : r.1 = p.1
  · simp [area, hq, hr]
  · simp [hq, hr] at h
  · simp [hq, hr] at h
  · simp only [hq, hr, ↓reduceIte, Option.some.injEq] at h
    have hh := (div_eq_div_iff (sub_ne_zero.mpr hq) (sub_ne_zero.mpr hr)).mp h
    unfold area
    nlinarith [hh]

theorem direction_ne_of_area_ne {p q r : Point} (h : area p q r ≠ 0) :
    direction p q ≠ direction p r := fun he => h (area_eq_zero_of_direction_eq he)

@[simp] theorem mem_directions {S : Finset Point} {d : Option ℝ} :
    d ∈ directions S ↔ ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ direction p q = d := by
  classical
  simp only [directions, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨p,q⟩, ⟨⟨hp,hq⟩,hne⟩,hd⟩
    exact ⟨p,hp,q,hq,hne,hd⟩
  · rintro ⟨p,hp,q,hq,hne,hd⟩
    exact ⟨(p,q), ⟨⟨hp,hq⟩,hne⟩,hd⟩

theorem directions_mono {S T : Finset Point} (h : S ⊆ T) : directions S ⊆ directions T := by
  intro d hd
  rcases mem_directions.mp hd with ⟨p,hp,q,hq,hne,he⟩
  exact mem_directions.mpr ⟨p,h hp,q,h hq,hne,he⟩

theorem slopeCount_mono {S T : Finset Point} (h : S ⊆ T) : slopeCount S ≤ slopeCount T :=
  Finset.card_le_card (directions_mono h)

/-- Printed p. 84, step (1): three noncollinear points give three distinct slopes.
This also supplies a lower bound for any configuration containing them. -/
theorem three_le_slopeCount {S : Finset Point} (h : Noncollinear S) : 3 ≤ slopeCount S := by
  classical
  rcases h with ⟨p,hp,q,hq,r,hr,ha⟩
  have hpq : p ≠ q := by intro he; subst q; simp at ha
  have hpr : p ≠ r := by intro he; subst r; simp at ha
  have hqr : q ≠ r := by intro he; subst r; simp at ha
  have hd₁ := direction_ne_of_area_ne ha
  have har : area q p r ≠ 0 := by rw [area_swap]; exact neg_ne_zero.mpr ha
  have hd₂ : direction p q ≠ direction q r := by
    rw [direction_comm p q]; exact direction_ne_of_area_ne har
  have hd₃ : direction p r ≠ direction q r := by
    rw [direction_comm p r, direction_comm q r]
    apply direction_ne_of_area_ne
    rw [← area_rotate r p q]
    exact ha
  have hs : {direction p q, direction p r, direction q r} ⊆ directions S := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact mem_directions.mpr ⟨p,hp,q,hq,hpq,rfl⟩
    · exact mem_directions.mpr ⟨p,hp,r,hr,hpr,rfl⟩
    · exact mem_directions.mpr ⟨q,hq,r,hr,hqr,rfl⟩
  have hc : ({direction p q, direction p r, direction q r} : Finset _).card = 3 := by
    simp [hd₁,hd₂,hd₃]
  simpa [slopeCount,hc] using Finset.card_le_card hs

/-- Nonzero triangle area implies noncollinearity in Mathlib's affine-space sense. -/
theorem not_collinear_of_area_ne {p q r : Point} (ha : area p q r ≠ 0) :
    ¬ Collinear ℝ ({p,q,r} : Set Point) := by
  intro hc
  rcases (collinear_iff_of_mem (by simp : p ∈ ({p,q,r} : Set Point))).mp hc with ⟨v,hv⟩
  obtain ⟨a,haq⟩ := hv q (by simp)
  obtain ⟨b,har⟩ := hv r (by simp)
  have hq₁ := congrArg Prod.fst haq
  have hq₂ := congrArg Prod.snd haq
  have hr₁ := congrArg Prod.fst har
  have hr₂ := congrArg Prod.snd har
  simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hq₁ hq₂ hr₁ hr₂
  apply ha
  unfold area
  rw [hq₁,hq₂,hr₁,hr₂]
  ring

theorem Noncollinear.not_collinear {S : Finset Point} (h : Noncollinear S) :
    ¬ Collinear ℝ (S : Set Point) := by
  rcases h with ⟨p,hp,q,hq,r,hr,ha⟩
  intro hc
  apply not_collinear_of_area_ne ha
  apply hc.subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- Coordinate form of lying on the line through two distinct points. -/
theorem exists_smul_of_area_eq_zero {p q r : Point} (hpq : p ≠ q)
    (ha : area p q r = 0) : ∃ a : ℝ, r = a • (q - p) + p := by
  by_cases hx : q.1 = p.1
  · have hy : q.2 - p.2 ≠ 0 := by
      intro he
      apply hpq
      apply Prod.ext hx.symm
      exact (sub_eq_zero.mp he).symm
    have hrx : r.1 = p.1 := by
      have hz : (q.2 - p.2) * (r.1 - p.1) = 0 := by simpa [area,hx] using ha
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hy)
    refine ⟨(r.2 - p.2) / (q.2 - p.2), ?_⟩
    apply Prod.ext
    · simp [hx,hrx]
    · simp only [Prod.smul_snd, Prod.snd_sub, Prod.snd_add, smul_eq_mul]
      rw [div_mul_cancel₀ _ hy]
      ring
  · refine ⟨(r.1 - p.1) / (q.1 - p.1), ?_⟩
    have hxn : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr hx
    apply Prod.ext
    · simp only [Prod.smul_fst,Prod.fst_sub,Prod.fst_add,smul_eq_mul]
      rw [div_mul_cancel₀ _ hxn]
      ring
    · simp only [Prod.smul_snd,Prod.snd_sub,Prod.snd_add,smul_eq_mul]
      have he : (r.2 - p.2) * (q.1 - p.1) = (r.1 - p.1) * (q.2 - p.2) := by
        unfold area at ha
        nlinarith [ha]
      field_simp
      nlinarith [he]

/-- The coordinate witness definition has exactly Mathlib's meaning. -/
theorem noncollinear_iff_not_collinear (S : Finset Point) :
    Noncollinear S ↔ ¬ Collinear ℝ (S : Set Point) := by
  classical
  refine ⟨Noncollinear.not_collinear, ?_⟩
  intro hnc
  by_contra hn
  have hz : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, area p q r = 0 := by
    simpa [Noncollinear] using hn
  obtain ⟨p,hp⟩ : S.Nonempty := by
    by_contra he
    have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst S
    exact hnc (by simpa using collinear_empty ℝ Point)
  by_cases he : ∃ q ∈ S, p ≠ q
  · obtain ⟨q,hq,hpq⟩ := he
    apply hnc
    apply (collinear_iff_of_mem hp).mpr
    refine ⟨q-p, ?_⟩
    intro r hr
    obtain ⟨a,ha⟩ := exists_smul_of_area_eq_zero hpq (hz p hp q hq r hr)
    exact ⟨a,ha⟩
  · apply hnc
    apply (collinear_singleton ℝ p).subset
    intro q hq
    have heq : q = p := by
      by_contra hqp
      exact he ⟨q,hq,Ne.symm hqp⟩
    exact Set.mem_singleton_iff.mpr heq

/-- Printed p. 84, step (1): deleting a point outside a noncollinear
triangle preserves noncollinearity and removes exactly one point. -/
theorem exists_erase_noncollinear {S : Finset Point} (hn : 4 ≤ S.card)
    (h : Noncollinear S) :
    ∃ x ∈ S, Noncollinear (S.erase x) ∧ (S.erase x).card = S.card - 1 := by
  classical
  rcases h with ⟨p,hp,q,hq,r,hr,ha⟩
  have ht : ({p,q,r} : Finset Point).card ≤ 3 := by
    exact le_trans (Finset.card_insert_le _ _) (by
      have := Finset.card_insert_le q ({r} : Finset Point)
      simp only [Finset.card_singleton] at this
      omega)
  have hx : ∃ x ∈ S, x ∉ ({p,q,r} : Finset Point) := by
    by_contra he
    have hs : S ⊆ {p,q,r} := by
      intro x hx
      by_contra hout
      exact he ⟨x,hx,hout⟩
    have := Finset.card_le_card hs
    omega
  rcases hx with ⟨x,hx,hout⟩
  have hxne : x ≠ p ∧ x ≠ q ∧ x ≠ r := by simpa using hout
  refine ⟨x,hx,?_,Finset.card_erase_of_mem hx⟩
  exact ⟨p,Finset.mem_erase.mpr ⟨hxne.1.symm,hp⟩,
    q,Finset.mem_erase.mpr ⟨hxne.2.1.symm,hq⟩,
    r,Finset.mem_erase.mpr ⟨hxne.2.2.symm,hr⟩,ha⟩

private theorem product_insert_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (s : Finset α) (t : Finset β) :
    (insert a s) ×ˢ t = ({a} ×ˢ t) ∪ (s ×ˢ t) := by
  ext x
  simp only [Finset.mem_product,Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
  tauto
private theorem product_insert_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (b : β) (t : Finset β) :
    s ×ˢ (insert b t) = (s ×ˢ {b}) ∪ (s ×ˢ t) := by
  ext x
  simp only [Finset.mem_product,Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
  tauto

/-- Coordinates for the lower sequence in the figure on printed p. 83.
These rational representatives preserve the directions in that drawing. -/
noncomputable def example3 : Finset Point := {(0,1),(-1,0),(0,-1)}
noncomputable def example4 : Finset Point := {(0,1),(-1,0),(1,0),(0,-1)}
noncomputable def example5 : Finset Point := {(0,1),(-1,0),(0,0),(1,0),(0,-1)}
noncomputable def example6 : Finset Point := {(0,1),(-1,0),(0,0),(1,0),(2,0),(0,-1)}
noncomputable def example7 : Finset Point := {(0,1),(-2,0),(-1,0),(0,0),(1,0),(2,0),(0,-1)}

theorem example3_card : example3.card = 3 := by
  classical
  norm_num [example3]
theorem example4_card : example4.card = 4 := by
  classical
  norm_num [example4]
theorem example5_card : example5.card = 5 := by
  classical
  norm_num [example5]
theorem example6_card : example6.card = 6 := by
  classical
  norm_num [example6]
theorem example7_card : example7.card = 7 := by
  classical
  norm_num [example7]

theorem example3_slopes : slopeCount example3 = 3 := by
  classical
  norm_num [slopeCount,directions,example3,product_insert_left,product_insert_right,Finset.singleton_product_singleton,
    Finset.filter_union,Finset.filter_insert,Finset.filter_singleton,direction]
theorem example4_slopes : slopeCount example4 = 4 := by
  classical
  norm_num [slopeCount,directions,example4,product_insert_left,product_insert_right,Finset.singleton_product_singleton,
    Finset.filter_union,Finset.filter_insert,Finset.filter_singleton,direction]
theorem example5_slopes : slopeCount example5 = 4 := by
  classical
  norm_num [slopeCount,directions,example5,product_insert_left,product_insert_right,Finset.singleton_product_singleton,
    Finset.filter_union,Finset.filter_insert,Finset.filter_singleton,direction]
theorem example6_slopes : slopeCount example6 = 6 := by
  classical
  norm_num [slopeCount,directions,example6,product_insert_left,product_insert_right,Finset.singleton_product_singleton,
    Finset.filter_union,Finset.filter_insert,Finset.filter_singleton,direction]
theorem example7_slopes : slopeCount example7 = 6 := by
  classical
  norm_num [slopeCount,directions,example7,product_insert_left,product_insert_right,Finset.singleton_product_singleton,
    Finset.filter_union,Finset.filter_insert,Finset.filter_singleton,direction]


/-- Printed p. 84, step (1), formal reduction to the even case. This proves
an equivalence between statements, NOT the unproved even-case theorem.
The right side includes the equality restriction in the boxed theorem. -/
theorem even_case_iff_full_statement :
    (∀ S : Finset Point, 3 ≤ S.card → Noncollinear S →
      Even S.card → S.card ≤ slopeCount S) ↔
    (∀ S : Finset Point, 3 ≤ S.card → Noncollinear S →
      S.card - 1 ≤ slopeCount S ∧
      (slopeCount S = S.card - 1 → Odd S.card ∧ 5 ≤ S.card)) := by
  constructor
  · intro he S hn hnc
    by_cases hp : Even S.card
    · have hb := he S hn hnc hp
      constructor
      · omega
      · intro hx
        omega
    · have hod : Odd S.card := Nat.not_even_iff_odd.mp hp
      have hmod := Nat.odd_iff.mp hod
      have hb : S.card - 1 ≤ slopeCount S := by
        by_cases hthree : S.card = 3
        · have hsmall := three_le_slopeCount hnc
          omega
        · have hfive : 5 ≤ S.card := by omega
          obtain ⟨x,hx,hdel,hcard⟩ := exists_erase_noncollinear (by omega) hnc
          have hdEven : Even (S.erase x).card := by
            rw [hcard,Nat.even_iff]
            omega
          have hd := he (S.erase x) (by omega) hdel hdEven
          have hm := slopeCount_mono (Finset.erase_subset x S)
          omega
      refine ⟨hb,fun hx => ⟨hod,?_⟩⟩
      have hsmall := three_le_slopeCount hnc
      omega
  · intro hf S hn hnc he
    obtain ⟨hb,heq⟩ := hf S hn hnc
    have hmod := Nat.even_iff.mp he
    by_contra hlt
    have hx : slopeCount S = S.card - 1 := by omega
    have hod := Nat.odd_iff.mp (heq hx).1
    omega

theorem example3_noncollinear : Noncollinear example3 := by
  classical
  refine ⟨(0,1),?_,(-1,0),?_,(0,-1),?_,?_⟩ <;> norm_num [example3,area]
theorem example4_noncollinear : Noncollinear example4 := by
  classical
  refine ⟨(0,1),?_,(-1,0),?_,(0,-1),?_,?_⟩ <;> norm_num [example4,area]
theorem example5_noncollinear : Noncollinear example5 := by
  classical
  refine ⟨(0,1),?_,(-1,0),?_,(0,-1),?_,?_⟩ <;> norm_num [example5,area]
theorem example6_noncollinear : Noncollinear example6 := by
  classical
  refine ⟨(0,1),?_,(-1,0),?_,(0,-1),?_,?_⟩ <;> norm_num [example6,area]
theorem example7_noncollinear : Noncollinear example7 := by
  classical
  refine ⟨(0,1),?_,(-1,0),?_,(0,-1),?_,?_⟩ <;> norm_num [example7,area]

open scoped symmDiff

/-- Printed p. 86, step (3): a letter's side changes are the symmetric
difference of the sets of letters on the left of the barrier. -/
def crossingLetters {α : Type*} [DecidableEq α] (A B : Finset α) : Finset α := A ∆ B

/-- Printed p. 85: equally sized left halves exchange `d` letters in each
direction, so a crossing of order `d` moves exactly `2*d` letters. -/
theorem crossingLetters_card {α : Type*} [DecidableEq α] (A B : Finset α)
    (h : A.card = B.card) : (crossingLetters A B).card = 2 * (A \ B).card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [crossingLetters,Finset.symmDiff_def,Finset.card_union_of_disjoint hd,
    ← Finset.card_sdiff_comm h]
  omega

/-- Discrete triangle inequality: every letter whose initial and final
sides differ must be counted in at least one intervening move. -/
theorem endpoint_crossings_le_sum {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (t : ℕ) :
    (crossingLetters (A 0) (A t)).card ≤
      ∑ i ∈ Finset.range t, (crossingLetters (A i) (A (i+1))).card := by
  induction t with
  | zero => simp [crossingLetters]
  | succ t ih =>
    have ht : A 0 ∆ A (t+1) ⊆ (A 0 ∆ A t) ∪ (A t ∆ A (t+1)) :=
      symmDiff_triangle _ _ _
    calc
      (crossingLetters (A 0) (A (t+1))).card ≤
          ((A 0 ∆ A t) ∪ (A t ∆ A (t+1))).card := Finset.card_le_card ht
      _ ≤ (crossingLetters (A 0) (A t)).card +
          (crossingLetters (A t) (A (t+1))).card := Finset.card_union_le _ _
      _ ≤ (∑ i ∈ Finset.range t, (crossingLetters (A i) (A (i+1))).card) +
          (crossingLetters (A t) (A (t+1))).card := Nat.add_le_add_right ih _
      _ = ∑ i ∈ Finset.range (t+1), (crossingLetters (A i) (A (i+1))).card := by
        rw [Finset.sum_range_succ]

/-- Printed p. 86, step (3): reversal changes every letter's half, hence
the total number of letter-crossings is at least the number of letters.
The endpoint hypothesis expresses reversal; it does not assume the bound. -/
theorem all_letters_cross {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℕ → Finset α) (t : ℕ) (hend : A t = Finset.univ \ A 0) :
    Fintype.card α ≤ ∑ i ∈ Finset.range t,
      (crossingLetters (A i) (A (i+1))).card := by
  have he : crossingLetters (A 0) (A t) = Finset.univ := by
    ext x
    simp only [crossingLetters,hend,Finset.mem_symmDiff,Finset.mem_sdiff,
      Finset.mem_univ,true_and]
    tauto
  have hh := endpoint_crossings_le_sum A t
  simpa only [he,Finset.card_univ] using hh

/-- The displayed inequality `sum 2*d_i ≥ n` in step (3), with the
crossing orders calculated as the number of letters leaving the left half. -/
theorem twice_orders_ge_number_of_letters {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℕ → Finset α) (t : ℕ) (hend : A t = Finset.univ \ A 0)
    (hsize : ∀ i < t, (A i).card = (A (i+1)).card) :
    Fintype.card α ≤ ∑ i ∈ Finset.range t, 2 * (A i \ A (i+1)).card := by
  have hh := all_letters_cross A t hend
  have he : (∑ i ∈ Finset.range t, (crossingLetters (A i) (A (i+1))).card) =
      ∑ i ∈ Finset.range t, 2 * (A i \ A (i+1)).card := by
    apply Finset.sum_congr rfl
    intro i hi
    exact crossingLetters_card _ _ (hsize i (Finset.mem_range.mp hi))
  rwa [he] at hh

end Chapter12
