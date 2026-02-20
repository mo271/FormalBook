/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Tiling rectangles

## TODO
  - Second and third proofs of the first statement.
-/


noncomputable section

open MeasureTheory

/-- We model a rectangle in `R^2` as the coordinated `(x,y)` of its bottom right corner, together
  with its width `w` and height `h`, which must be positive. -/
@[ext]
structure Rectangle where
  /-- The `x` coordinate of the bottom left corner of the triangle. -/
  x : ℝ
  /-- The `y` coordinate of the bottom left corner of the triangle. -/
  y : ℝ
  /-- The width of the rectangle. -/
  w : ℝ
  /-- The height of the rectangle. -/
  h : ℝ
  w_pos : 0 < w
  h_pos : 0 < h
  deriving DecidableEq

/-- The part of the plane occupied by a rectangle, as a subset of `R × R`. -/
def Rectangle.toSet (r : Rectangle) : Set (ℝ × ℝ) :=
  Set.Icc r.x (r.x + r.w) ×ˢ Set.Icc r.y (r.y + r.h)

/-- The interior of a rectangle, as a subset of `R × R`. -/
def Rectangle.interior (r : Rectangle) : Set (ℝ × ℝ) :=
  Set.Ioo r.x (r.x + r.w) ×ˢ Set.Ioo r.y (r.y + r.h)

/-- A list `Ts` of rectangles is a tiling of the rectangle `R` if the elements of `Ts` have pairwise
  disjoint interiors and their union is equal to `R`. -/
def is_tiling (R : Rectangle) (Ts : List Rectangle) : Prop :=
  (∀ i j : Fin Ts.length, i ≠ j → (Ts.get i).interior ∩ (Ts.get j).interior = ∅) ∧
  (⋃ t ∈ Ts, t.toSet) = R.toSet

/-- The auxiliary function `f(x,y) =  e^(2πix)e^(2πiy)` that appears in the proof. -/
noncomputable def f (p : ℝ × ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * p.1 * Complex.I) * Complex.exp (2 * Real.pi * p.2 * Complex.I)


/-- The integral of the function `f(x, y) = e^(2πix)e^(2πiy)` over a rectangle is zero if and only
  if at least one side of the rectangle is an integer. -/
lemma integral_f_eq_zero_iff_int_side (r : Rectangle) :
  ∫ p in r.interior, f p = 0 ↔ (∃ k : ℤ, r.w = k) ∨ (∃ k : ℤ, r.h = k) := by
    have h_integral_product : (∫ p in r.interior, f p) = (∫ x in Set.Ioo r.x (r.x + r.w),
      Real.cos (2 * Real.pi * x) + Complex.I * Real.sin (2 * Real.pi * x)) *
      (∫ y in Set.Ioo r.y (r.y + r.h), Real.cos (2 * Real.pi * y) +
      Complex.I * Real.sin (2 * Real.pi * y)) := by
      rw [ ← MeasureTheory.setIntegral_prod_mul ];
      unfold f Rectangle.interior
      congr
      ext
      simp +decide [Complex.exp_mul_I]
      ring;
    have h_integral_zero : ∀ a b : ℝ, (∫ t in a..b, Complex.exp (2 * Real.pi * Complex.I * t)) = 0 ↔
      (∃ k : ℤ, (b - a) = k) := by
      intros a b
      have h_ftc : ∫ t in a..b, Complex.exp (2 * Real.pi * Complex.I * t) =
        (1 / (2 * Real.pi * Complex.I)) * (Complex.exp (2 * Real.pi * Complex.I * b) -
        Complex.exp (2 * Real.pi * Complex.I * a)) := by
        have := @integral_exp_mul_complex a b;
        simpa [ div_eq_inv_mul ] using this ( show ( 2 * Real.pi * Complex.I : ℂ ) ≠ 0
          by norm_num [ Complex.ext_iff, Real.pi_ne_zero ] );
      simp_all +decide [sub_eq_iff_eq_add];
      rw [ Complex.exp_eq_exp_iff_exists_int ]
      exact
        ⟨ fun ⟨ k, hk ⟩ => ⟨ k, by norm_num [ Complex.ext_iff ] at hk; nlinarith [ Real.pi_pos ] ⟩,
        fun ⟨ k, hk ⟩ => ⟨ k, by norm_num [ Complex.ext_iff ] ; nlinarith [ Real.pi_pos ] ⟩ ⟩ ;
    have h_integral_zero_applied :
      (∫ x in Set.Ioo r.x (r.x + r.w), Complex.exp (2 * Real.pi * Complex.I * x)) = 0 ∨
      (∫ y in Set.Ioo r.y (r.y + r.h), Complex.exp (2 * Real.pi * Complex.I * y)) = 0 ↔
      (∃ k : ℤ, r.w = k) ∨ (∃ k : ℤ, r.h = k) := by
      rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ( by linarith [ r.w_pos ] ),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ( by linarith [ r.h_pos ] ) ]
      simp_all only [Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_sin, add_sub_cancel_left];
    simp_all +decide
    convert h_integral_zero_applied using 4 <;> ext <;>
      rw [ Complex.exp_eq_exp_re_mul_sin_add_cos ] <;> norm_num ; ring;
    ring


/-- The integral of `f` over a rectangle is equal to the integral of `f` over its interior. -/
lemma integral_rectangle_eq_integral_interior (r : Rectangle) :
  ∫ p in r.toSet, f p = ∫ p in r.interior, f p := by
    rw [ MeasureTheory.Measure.restrict_congr_set ];
    have h_boundary_zero :
      MeasureTheory.volume (Set.Icc r.x (r.x + r.w) ×ˢ Set.Icc r.y (r.y + r.h) \
      Set.Ioo r.x (r.x + r.w) ×ˢ Set.Ioo r.y (r.y + r.h)) = 0 := by
      erw [ MeasureTheory.measure_diff ] <;> norm_num;
      · erw [ show ( Set.Icc ( r.x, r.y ) ( r.x + r.w, r.y + r.h ) : Set ( ℝ × ℝ ) ) =
          Set.Icc r.x ( r.x + r.w ) ×ˢ Set.Icc r.y ( r.y + r.h ) by ext ; aesop,
          show ( Set.Ioo r.x ( r.x + r.w ) ×ˢ Set.Ioo r.y ( r.y + r.h ) : Set ( ℝ × ℝ ) ) =
          Set.Ioo r.x ( r.x + r.w ) ×ˢ Set.Ioo r.y ( r.y + r.h ) by rfl,
          MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod ]
        norm_num
      · exact fun x hx => ⟨ ⟨ hx.1.1.le, hx.2.1.le ⟩, ⟨ hx.1.2.le, hx.2.2.le ⟩ ⟩;
      · exact measurableSet_Ioo.prod measurableSet_Ioo |> MeasurableSet.nullMeasurableSet;
      · erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
        exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
    rw [ MeasureTheory.ae_eq_set ];
    constructor
    · exact h_boundary_zero
    · rw [Set.diff_eq_empty.mpr
        (by exact Set.prod_mono (Set.Ioo_subset_Icc_self) (Set.Ioo_subset_Icc_self))]
      norm_num

/-- The integral of `f` over the union of a list of rectangles with disjoint interiors is the sum of
  the integrals over each rectangle. -/
lemma integral_union_rectangles (Ts : List Rectangle)
  (h_disjoint : ∀ i j : Fin Ts.length, i ≠ j → (Ts.get i).interior ∩ (Ts.get j).interior = ∅) :
  ∫ p in (⋃ t ∈ Ts, t.toSet), f p = (Ts.map (fun t => ∫ p in t.toSet, f p)).sum := by
    have h_split :
      ∫ p in (⋃ t ∈ Ts, t.toSet), f p = ∑ t ∈ (List.toFinset Ts), ∫ p in t.interior, f p := by
      have h_split : ∫ p in (⋃ t ∈ Ts.toFinset, t.interior),
        f p = ∑ t ∈ Ts.toFinset, ∫ p in t.interior, f p := by
        rw [ MeasureTheory.integral_biUnion_finset ];
        · exact fun t ht => measurableSet_Ioo.prod measurableSet_Ioo;
        · intros t ht t' ht' h; simp_all +decide [ Set.disjoint_iff_inter_eq_empty ] ;
          obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp ht;
          obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp ht';
          specialize h_disjoint ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ ;
          subst hi hj
          simp_all only [Fin.eta, List.get_eq_getElem]
          apply h_disjoint
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false, Set.inter_self, IsEmpty.forall_iff]
          simp_all only [List.get_eq_getElem, List.getElem_mem, not_true_eq_false];
        · intro i hi
          have h_cont : ContinuousOn f (i.toSet) :=
            Continuous.continuousOn (Continuous.mul ( Complex.continuous_exp.comp <| by continuity )
              ( Complex.continuous_exp.comp <| by continuity ) );
          exact h_cont.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) |>
            fun h => h.mono_set ( Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self );
      rw [ ← h_split, MeasureTheory.setIntegral_congr_set ];
      have h_boundary_zero : ∀ t : Rectangle, MeasureTheory.volume (t.toSet \ t.interior) = 0 := by
        intro t;
        rw [ show t.toSet \ t.interior = ( Set.Icc t.x ( t.x + t.w ) ×ˢ Set.Icc t.y ( t.y + t.h ) )
          \ ( Set.Ioo t.x ( t.x + t.w ) ×ˢ Set.Ioo t.y ( t.y + t.h ) ) by rfl ];
        erw [ MeasureTheory.measure_diff ] ;
        norm_num;
        · erw [ show ( Set.Icc ( t.x, t.y ) ( t.x + t.w, t.y + t.h ) : Set ( ℝ × ℝ ) ) =
            Set.Icc t.x ( t.x + t.w ) ×ˢ Set.Icc t.y ( t.y + t.h )
            by ext ; aesop, MeasureTheory.Measure.prod_prod ] ;
          norm_num;
          erw [ MeasureTheory.Measure.prod_prod ] ; norm_num [ t.w_pos, t.h_pos ];
        · exact Set.prod_mono ( Set.Ioo_subset_Icc_self ) ( Set.Ioo_subset_Icc_self );
        · exact measurableSet_Ioo.prod measurableSet_Ioo |> MeasurableSet.nullMeasurableSet;
        · erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
          exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
      have h_boundary_zero : MeasureTheory.volume (⋃ t ∈ Ts.toFinset, (t.toSet \ t.interior)) = 0 :=
        MeasureTheory.measure_biUnion_null_iff (I := Ts.toFinset) ( Finset.countable_toSet _ ) |>.2
          fun t ht => h_boundary_zero t
      rw [ MeasureTheory.ae_eq_set ];
      constructor;
      · refine' MeasureTheory.measure_mono_null _ h_boundary_zero;
        simp +contextual [ Set.subset_def ];
      · refine' MeasureTheory.measure_mono_null _ h_boundary_zero;
        simp +contextual [ Set.subset_def ];
        exact fun a b x hx hx' =>
          ⟨ x, hx, ⟨ ⟨ hx'.1.1.le, hx'.1.2.le ⟩, ⟨ hx'.2.1.le, hx'.2.2.le ⟩ ⟩ ⟩;
    simp_all +decide [ integral_rectangle_eq_integral_interior ];
    have h_sum_eq : ∀ (l : List Rectangle),
      (∀ i j : Fin l.length, i ≠ j → (l.get i).interior ∩ (l.get j).interior = ∅) →
      (List.map (fun t => ∫ p in t.interior, f p) l).sum =
      ∑ t ∈ l.toFinset, ∫ p in t.interior, f p := by
      intros l hl_disjoint
      induction l;
      case nil => norm_num;
      case cons t l ih =>
        by_cases h : t ∈ l.toFinset <;> simp_all +decide [ Fin.forall_fin_succ ];
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h;
        specialize hl_disjoint;
        have := hl_disjoint.2 ⟨ i, by aesop ⟩ ;
        subst hi
        simp_all only [List.get_eq_getElem, Set.inter_self, Fin.eta, not_false_eq_true,
          implies_true, and_true, Measure.restrict_empty, integral_zero_measure]
    exact Eq.symm ( h_sum_eq Ts h_disjoint )

/-- Whenever a rectangle is tiled by rectangles all of which have at least one side of integer
  length, then the tiled rectangle has at least one side of integer length. -/
theorem rectangle_tiling_integer_side (R : Rectangle) (Ts : List Rectangle)
  (h_tiling : is_tiling R Ts)
  (h_integer : ∀ t ∈ Ts, t.w = ⌊t.w⌋ ∨ t.h = ⌊t.h⌋) :
  R.w = ⌊R.w⌋ ∨ R.h = ⌊R.h⌋ := by
    have h_integral : ∫ p in R.toSet, f p = 0 := by
      have h_integral_sum :
        ∫ p in (⋃ t ∈ Ts, t.toSet), f p = (Ts.map (fun t => ∫ p in t.toSet, f p)).sum := by
        convert integral_union_rectangles Ts _;
        exact h_tiling.1;
      have h_integral_zero : ∀ t ∈ Ts, ∫ p in t.toSet, f p = 0 := by
        intros t ht
        have h_integral_zero : ∫ p in t.interior, f p = 0 := by
          apply (integral_f_eq_zero_iff_int_side t).mpr;
          exact Or.imp ( fun h => ⟨ _, h ⟩ ) ( fun h => ⟨ _, h ⟩ ) ( h_integer t ht );
        rw [ ← h_integral_zero, integral_rectangle_eq_integral_interior ];
      rw [ h_tiling.2.symm, h_integral_sum, List.sum_eq_zero ] ;
      intro x a
      simp_all only [List.mem_map]
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only
    rw [ integral_rectangle_eq_integral_interior ] at h_integral;
    convert integral_f_eq_zero_iff_int_side R |>.1 h_integral using 1;
    · exact ⟨ fun h => ⟨ _, h ⟩, fun ⟨ k, hk ⟩ => hk ▸ by norm_num ⟩;
    · exact ⟨ fun h => ⟨ _, h ⟩, fun ⟨ k, hk ⟩ => hk ▸ by norm_num ⟩

/- We now turn into proving that a rectangle can be tiled by squares if and only if the ratio of
  its side lengths is rational. -/

/-- A rectangle is a square if its width equals its height. -/
def is_square (r : Rectangle) : Prop := r.w = r.h

/-- A rectangle can be tiled with squares if there exists a tiling of it consisting only of
  squares. -/
def can_be_tiled_with_squares (R : Rectangle) : Prop :=
  ∃ (Ts : List Rectangle), is_tiling R Ts ∧ ∀ t ∈ Ts, is_square t

/-- The `f`-area of a rectangle is the product of the function applied to its width and the function
  applied to its height. -/
def f_area (f : ℝ →+ ℝ) (r : Rectangle) : ℝ := f r.w * f r.h

/-- The `f`-area is additive with respect to width. -/
lemma f_area_add_width (f : ℝ →+ ℝ) (r1 r2 : Rectangle) (h_height : r1.h = r2.h) :
  f_area f ⟨r1.x, r1.y, r1.w + r2.w, r1.h, by linarith [r1.w_pos, r2.w_pos], r1.h_pos⟩ =
  f_area f r1 + f_area f r2 := by
    unfold f_area;
    simp_all only [map_add];
    apply add_mul;

/-- The `f`-area is additive with respect to height. -/
lemma f_area_add_height (f : ℝ →+ ℝ) (r1 r2 : Rectangle) (h_width : r1.w = r2.w) :
  f_area f ⟨r1.x, r1.y, r1.w, r1.h + r2.h, r1.w_pos, by linarith [r1.h_pos, r2.h_pos]⟩ =
  f_area f r1 + f_area f r2 := by
    unfold f_area;
    simp_all only [map_add]
    apply mul_add

/-- For any non-empty list of real numbers, the sum of the function applied to the differences of
  consecutive elements equals the function applied to the difference of the last and first elements,
  given the function is additive. -/
lemma sum_f_diffs_eq (f : ℝ →+ ℝ) (l : List ℝ) (hl : l ≠ []) :
  (List.zipWith (fun x y => f (y - x)) l l.tail).sum = f (l.getLast hl - l.head hl) := by
    induction l
    case nil => grind;
    case cons hd tl ih => cases tl <;> aesop

/-- A grid is defined by sorted lists of x and y coordinates. This will be used to construct the
  "grid of rectangles" associated to a tiling of squares as in the given proof. -/
structure Grid where
  /-- The list of `x` coordinates. -/
  xs : List ℝ
  /-- The list of `y` coordinates. -/
  ys : List ℝ
  xs_sorted : xs.Pairwise (· < ·)
  ys_sorted : ys.Pairwise (· < ·)
  xs_ne_nil : xs ≠ []
  ys_ne_nil : ys ≠ []

/-- The cells of a grid are the rectangles formed by adjacent x and y coordinates.
  We use a conditional to ensure the width and height are positive, although for a valid grid they
  always will be. -/
def Grid.cells (g : Grid) : List Rectangle :=
  (g.xs.zip g.xs.tail).flatMap fun (x1, x2) =>
    (g.ys.zip g.ys.tail).flatMap fun (y1, y2) =>
      if h : x1 < x2 ∧ y1 < y2 then
        [{ x := x1, y := y1, w := x2 - x1, h := y2 - y1,
           w_pos := sub_pos.mpr h.1,
           h_pos := sub_pos.mpr h.2 }]
      else
        []

/-- The sum of the `f`-areas of the cells in a grid equals the `f`-area of the rectangle defined by
  the grid's boundaries. -/
lemma grid_f_area_sum (f : ℝ →+ ℝ) (g : Grid) :
  (g.cells.map (f_area f)).sum = f (g.xs.getLast g.xs_ne_nil - g.xs.head g.xs_ne_nil) *
    f (g.ys.getLast g.ys_ne_nil - g.ys.head g.ys_ne_nil) := by
    rw [ Grid.cells ];
    have h_expand : (List.map (f_area f)
      (List.flatMap (fun (x1, x2) => List.flatMap (fun (y1, y2) =>
      if h : x1 < x2 ∧ y1 < y2 then [⟨x1, y1, x2 - x1, y2 - y1, sub_pos.mpr h.1, sub_pos.mpr h.2⟩]
      else []) (List.zip g.ys g.ys.tail)) (List.zip g.xs g.xs.tail))).sum =
      (List.map (fun (x1, x2) => if h : x1 < x2 then f (x2 - x1) else 0)
      (List.zip g.xs g.xs.tail)).sum * (List.map (fun (y1, y2) => if h : y1 < y2 then f (y2 - y1)
      else 0) (List.zip g.ys g.ys.tail)).sum := by
      induction g.xs.zip g.xs.tail using List.reverseRecOn
      case nil => simp_all +decide
      case append_singleton x xs ih =>
        simp_all +decide
        split_ifs <;> simp_all +decide [ add_mul ];
        · induction ( g.ys.zip g.ys.tail ) using List.reverseRecOn
          case pos.nil => simp_all +decide
          case pos.append_singleton x xs ih =>
            simp_all +decide
            split_ifs <;> simp_all +decide [ mul_add ];
            unfold f_area; simp_all only [map_sub]
        · rw [ List.sum_eq_zero ] ;
          intros
          simp_all only [List.mem_map, List.mem_flatMap, List.mem_dite_nil_right, List.mem_cons,
            List.not_mem_nil, or_false, isEmpty_Prop, not_and, not_lt, IsEmpty.forall_iff,
            IsEmpty.exists_iff, and_false, exists_const, false_and, exists_false]
    have h_sum_widths : (List.map (fun (x1, x2) => if h : x1 < x2 then f (x2 - x1) else 0)
      (List.zip g.xs g.xs.tail)).sum = f (g.xs.getLast g.xs_ne_nil - g.xs.head g.xs_ne_nil) := by
      have h_sum_x : (List.map (fun (x1, x2) => f (x2 - x1)) (List.zip g.xs g.xs.tail)).sum =
        f (g.xs.getLast g.xs_ne_nil - g.xs.head g.xs_ne_nil) := by
        convert sum_f_diffs_eq f g.xs g.xs_ne_nil using 1;
        congr;
        refine' List.ext_get _ _ <;> aesop;
      convert h_sum_x using 2;
      refine' List.ext_get _ _ <;> simp +decide;
      intro n hn h; have := g.xs_sorted; simp_all +decide;
      exact absurd h ( not_le_of_gt ( this.rel_get_of_lt ( Nat.lt_succ_self _ ) ) );
    rw [ h_expand, h_sum_widths ];
    convert rfl using 2;
    convert sum_f_diffs_eq f g.ys g.ys_ne_nil |> Eq.symm using 1;
    congr! 1;
    refine' List.ext_get _ _ <;> simp +decide;
    intro n hn h; have := g.ys_sorted; simp_all +decide;
    rw [ List.pairwise_iff_get ] at this;
    exact absurd h
      ( not_le_of_gt ( this ⟨ n, by omega ⟩ ⟨ n + 1, by omega ⟩ ( Nat.lt_succ_self _ ) ) )

/- The grid associated with a tiling is formed by the sorted unique `x` and `y` coordinates of the
  boundaries of the tiles and the large rectangle. -/

/-- The list of `x` coordinates of the grid associated with a tiling. -/
def tiling_grid_xs (R : Rectangle) (Ts : List Rectangle) : List ℝ :=
  (R.x :: (R.x + R.w) :: Ts.flatMap (fun t => [t.x, t.x + t.w])).mergeSort (· ≤ ·) |>.dedup

/-- The list of `y` coordinates of the grid associated with a tiling. -/
def tiling_grid_ys (R : Rectangle) (Ts : List Rectangle) : List ℝ :=
  (R.y :: (R.y + R.h) :: Ts.flatMap (fun t => [t.y, t.y + t.h])).mergeSort (· ≤ ·) |>.dedup

/-- The grid associated with a tiling. This corresponds to "prolonging all the sides of all the
  small rectangles along the big one and considering all the resulting (smaller) rectangles".
  In fact, a cell of this grid is a rectangle starting at some set of coordinates `(x₀,y₀)` that
  were individually present in the tiling (so the intersection of the possibly prolonged sides of
  rectangles in the tiling), extending up to the next valid values of `x` and `y`. -/
def tiling_grid (R : Rectangle) (Ts : List Rectangle) : Grid :=
  { xs := tiling_grid_xs R Ts
    ys := tiling_grid_ys R Ts
    xs_sorted := by
      refine' List.pairwise_iff_get.mpr _;
      intro i j hij;
      have h_sorted : List.Pairwise (· < ·) (List.dedup (List.mergeSort
        (R.x :: (R.x + R.w) :: List.flatMap (fun t => [t.x, t.x + t.w]) Ts)
        (fun x1 x2 => decide (x1 ≤ x2)))) := by
        have h_sorted : List.Pairwise (· ≤ ·) ((R.x :: (R.x + R.w) :: List.flatMap
          (fun t => [t.x, t.x + t.w]) Ts).mergeSort fun x1 x2 => decide (x1 ≤ x2)) := by
          exact List.pairwise_mergeSort' (fun x1 x2 => x1 ≤ x2)
              (R.x :: (R.x + R.w) :: List.flatMap (fun t => [t.x, t.x + t.w]) Ts);
        have h_sorted : List.Pairwise (· ≤ ·) (List.dedup (List.mergeSort
          (R.x :: (R.x + R.w) :: List.flatMap (fun t => [t.x, t.x + t.w]) Ts)
          (fun x1 x2 => decide (x1 ≤ x2)))) := by
          exact h_sorted.sublist ( List.dedup_sublist _ );
        have h_sorted : List.Nodup (List.dedup (List.mergeSort (R.x :: (R.x + R.w) :: List.flatMap
          (fun t => [t.x, t.x + t.w]) Ts) (fun x1 x2 => decide (x1 ≤ x2)))) := by
          exact List.nodup_dedup _;
        expose_names;
        rw[← List.sortedLT_iff_pairwise];
        rw[← List.sortedLE_iff_pairwise] at h_sorted_2
        exact List.SortedLE.sortedLT_of_nodup h_sorted_2 h_sorted
      exact h_sorted.rel_get_of_lt hij
    ys_sorted := by
      convert List.Pairwise.imp_of_mem _ _;
      exact fun x y => x < y ∧ x ∈ tiling_grid_ys R Ts ∧ y ∈ tiling_grid_ys R Ts;
      · aesop;
      · unfold tiling_grid_ys;
        have h_sorted : List.Pairwise (· ≤ ·) ((R.y :: (R.y + R.h) :: List.flatMap
          (fun t => [t.y, t.y + t.h]) Ts).mergeSort (· ≤ ·)) :=
          List.pairwise_mergeSort' (fun x1 x2 => x1 ≤ x2)
              (R.y :: (R.y + R.h) :: List.flatMap (fun t => [t.y, t.y + t.h]) Ts);
        have h_dedup_sorted : ∀ {l : List ℝ},
          List.Pairwise (· ≤ ·) l → List.Pairwise (· < ·) (List.dedup l) := by
          intros l hl_sorted
          induction l
          case nil => trivial;
          case cons x l ih =>
            by_cases hx : x ∈ l <;> simp_all +decide [ List.dedup_cons_of_mem ];
            exact fun y hy => lt_of_le_of_ne ( hl_sorted.1 y hy ) fun h => hx <| h ▸ hy;
        exact List.Pairwise.imp_of_mem ( fun x y hxy => ⟨ hxy,
          List.mem_dedup.mpr ( List.mem_mergeSort.mpr ( by aesop ) ),
          List.mem_dedup.mpr ( List.mem_mergeSort.mpr ( by aesop ) ) ⟩ ) ( h_dedup_sorted h_sorted )
    xs_ne_nil := by
      unfold tiling_grid_xs;
      by_contra h_empty;
      replace h_empty := congr_arg List.length h_empty ; simp_all +decide;
      replace h_empty := congr_arg List.length h_empty ; simp_all +decide
    ys_ne_nil := by
      unfold tiling_grid_ys;
      by_contra h_contra;
      replace h_contra := congr_arg List.toFinset h_contra ; simp_all +decide [ Finset.ext_iff ];
      simpa using h_contra R.y }

/-- The cells of a grid that are contained in a given rectangle. -/
def cells_in_rect (g : Grid) (r : Rectangle) : List Rectangle :=
  g.cells.filter (fun c => r.x ≤ c.x ∧ c.x + c.w ≤ r.x + r.w ∧ r.y ≤ c.y ∧ c.y + c.h ≤ r.y + r.h)

/-- A subgrid is defined by filtering the coordinates of a grid to those that fall within a given
  rectangle, provided the rectangle's boundaries are in the grid. -/
def subgrid (g : Grid) (r : Rectangle)
  (hx1 : r.x ∈ g.xs) (hy1 : r.y ∈ g.ys) : Grid :=
  { xs := g.xs.filter (fun x => r.x ≤ x ∧ x ≤ r.x + r.w)
    ys := g.ys.filter (fun y => r.y ≤ y ∧ y ≤ r.y + r.h)
    xs_sorted := by
      exact g.xs_sorted.filter _
    ys_sorted := by
      exact g.ys_sorted.filter _
    xs_ne_nil := by
      have h_nonempty_x : r.x ∈ List.filter (fun x => r.x ≤ x ∧ x ≤ r.x + r.w) g.xs := by
        simp [hx1, List.mem_filter];
        linarith [ r.w_pos ];
      exact List.ne_nil_of_mem h_nonempty_x
    ys_ne_nil := by
      simp +zetaDelta at *;
      exact ⟨ r.y, hy1, le_rfl, by linarith [ r.h_pos ] ⟩ }

/-- Filtering a sorted list and then zipping adjacent elements is equivalent to zipping adjacent
  elements and then filtering the pairs where both elements satisfy the predicate, provided the
  predicate is convex on the list. -/
lemma filter_zip_eq_zip_filter (l : List ℝ) (hl : l.Pairwise (· < ·)) (p : ℝ → Prop)
  [DecidablePred p] (h_convex : ∀ x y z, x ∈ l → y ∈ l → z ∈ l → x < y → y < z → p x → p z → p y) :
  (l.filter p).zip (l.filter p).tail = ((l.zip l.tail).filter (fun (x, y) => p x ∧ p y)) := by
    induction l --with x l ih;
    case nil => rfl;
    case cons x l ih =>
      by_cases hx : p x <;> simp +decide [ hx ];
      · induction l
        case pos.nil => simp +decide
        case pos.cons y l ih =>
          by_cases hy : p y <;> simp +decide [ hy ];
          · simp +zetaDelta at *;
            grind;
          · cases l <;> simp +decide [ List.zip ] at *;
            grind;
      · rcases l with ( _ | ⟨ y, l ⟩ ) <;> simp_all +decide;
        grind

/-- Filtering a flatMap with a predicate that splits into a condition on the source and a condition
  on the result is equivalent to filtering the source and then filtering the results. -/
lemma filter_flatMap_split {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) (q : α → Bool)
  (r : β → Bool) (h : ∀ a, ∀ b ∈ f a, p b = (q a && r b)) :
  (l.flatMap f).filter p = (l.filter q).flatMap (fun a => (f a).filter r) := by
    induction l <;> simp_all +decide [ List.filter_cons, List.flatMap ];
    split_ifs <;> simp_all +decide [ Function.comp_def ];
    · exact List.filter_congr fun x hx => by specialize h _ _ hx; aesop;
    · grind

/-- The list of cells in a grid that are contained in a rectangle is equal to the list of cells of
  the subgrid defined by that rectangle. -/
lemma cells_in_rect_eq_subgrid_cells (g : Grid) (r : Rectangle)
  (hx1 : r.x ∈ g.xs) (hy1 : r.y ∈ g.ys) :
  cells_in_rect g r = (subgrid g r hx1 hy1).cells := by
    rw [ subgrid ];
    unfold cells_in_rect
    generalize_proofs at *;
    unfold Grid.cells;
    rw [ filter_zip_eq_zip_filter, filter_zip_eq_zip_filter ];
    · rw [ filter_flatMap_split ];
      rotate_left;
      use fun p => ( r.x ≤ p.1 ∧ p.1 ≤ r.x + r.w ) ∧ ( r.x ≤ p.2 ∧ p.2 ≤ r.x + r.w );
      use fun b => decide ( r.y ≤ b.y ∧ b.y + b.h ≤ r.y + r.h );
      · grind;
      · induction ( g.xs.zip g.xs.tail ) <;> simp +decide [ * ];
        simp_all +decide [ List.filter_cons ];
        split_ifs <;> simp_all +decide [ List.flatMap ];
        induction ( g.ys.zip g.ys.tail ) <;> simp +decide [ * ];
        grind;
    · exact g.xs_sorted;
    · exact fun x y z hx hy hz hxy hyz hx' hz' => ⟨ by linarith, by linarith ⟩;
    · exact g.ys_sorted;
    · exact fun x y z hx hy hz hxy hyz hx' hz' => ⟨ by linarith, by linarith ⟩

/- If a sorted list contains `a` and `a <= b`, then the head of the list filtered by the interval
  `[a, b]` is `a`. -/
lemma head_filter_interval_eq_left (l : List ℝ) (hl : l.Pairwise (· < ·)) (a b : ℝ)
  (ha : a ∈ l) (hab : a ≤ b) :
  (l.filter (fun x => a ≤ x ∧ x ≤ b)).head (by
  aesop) = a := by
    all_goals generalize_proofs at *;
    induction l
    case nil => contradiction;
    case cons x l _ _ =>
      by_cases hx : x = a <;> by_cases hx' : a ∈ l <;> simp_all +decide [ List.filter_cons ];
      grind

/-- If a sorted list contains `b` and `a <= b`, then the last element of the list filtered by the
  interval `[a, b]` is `b`. -/
lemma last_filter_interval_eq_right (l : List ℝ) (hl : l.Pairwise (· < ·)) (a b : ℝ)
  (hb : b ∈ l) (hab : a ≤ b) :
  (l.filter (fun x => a ≤ x ∧ x ≤ b)).getLast (by
  aesop) = b := by
    all_goals generalize_proofs at *;
    induction l generalizing a b; --with hd tl ih
    case nil => contradiction;
    case cons hd tl ih _ =>
      simp +zetaDelta at *;
      cases hb <;> simp_all +decide;
      · rw [ List.find?_eq_none.mpr ] <;> aesop;
      · split_ifs <;> simp_all +decide;
        · convert ih a b ‹_› ( by linarith ) _ ‹_› ( by linarith ) ( by linarith ) using 1;
          exact Eq.symm
              (Option.get_eq_getD
                (List.find? (fun x => decide (a ≤ x) && decide (x ≤ b)) tl.reverse));
        · exact ih _ _ ‹_› ( by linarith [ hl.1 _ ‹_› ] ) _ ‹_› ( by linarith [ hl.1 _ ‹_› ] )
            ( by linarith [ hl.1 _ ‹_› ] )

/-- The boundaries of the subgrid are exactly the boundaries of the rectangle, provided the
  rectangle's boundaries are in the original grid. -/
lemma subgrid_bounds (g : Grid) (r : Rectangle)
  (hx1 : r.x ∈ g.xs) (hx2 : r.x + r.w ∈ g.xs)
  (hy1 : r.y ∈ g.ys) (hy2 : r.y + r.h ∈ g.ys) :
  (subgrid g r hx1 hy1).xs.head (by
    have := (subgrid g r hx1 hy1).xs_ne_nil
    exact this) = r.x ∧
  (subgrid g r hx1 hy1).xs.getLast (by
    have := (subgrid g r hx1 hy1).xs_ne_nil
    exact this) = r.x + r.w ∧
  (subgrid g r hx1 hy1).ys.head (by
    have := (subgrid g r hx1 hy1).ys_ne_nil
    exact this) = r.y ∧
  (subgrid g r hx1 hy1).ys.getLast (by
    have := (subgrid g r hx1 hy1).ys_ne_nil
    exact this) = r.y + r.h := by
      refine' ⟨ _, _, _, _ ⟩;
      · convert head_filter_interval_eq_left g.xs g.xs_sorted r.x ( r.x + r.w ) hx1
          ( by linarith [ r.w_pos ] );
      · convert last_filter_interval_eq_right g.xs g.xs_sorted r.x ( r.x + r.w ) hx2
          ( by linarith [ r.w_pos ] );
      · convert head_filter_interval_eq_left g.ys g.ys_sorted r.y ( r.y + r.h ) hy1
          ( by linarith [ r.h_pos ] );
      · convert last_filter_interval_eq_right g.ys g.ys_sorted r.y ( r.y + r.h ) hy2
          ( by linarith [ r.h_pos ] );

/-- If a rectangle's boundaries are in the grid, then the sum of the `f`-areas of the grid cells
  contained in the rectangle equals the `f`-area of the rectangle. -/
lemma sum_cells_in_rect_eq_f_area (f : ℝ →+ ℝ) (g : Grid) (r : Rectangle)
  (hx1 : r.x ∈ g.xs) (hx2 : r.x + r.w ∈ g.xs)
  (hy1 : r.y ∈ g.ys) (hy2 : r.y + r.h ∈ g.ys) :
  ((cells_in_rect g r).map (f_area f)).sum = f_area f r := by
    rw [cells_in_rect_eq_subgrid_cells g r hx1 hy1]
    rw [grid_f_area_sum]
    have h_bounds := subgrid_bounds g r hx1 hx2 hy1 hy2
    obtain ⟨h1, h2, h3, h4⟩ := h_bounds
    unfold f_area
    congr 1
    · rw [h2, h1]; ring_nf
    · rw [h4, h3]; ring_nf

/-- The grid generated by a tiling contains the boundaries of every tile in the tiling. -/
lemma tiling_grid_contains_boundaries (R : Rectangle) (Ts : List Rectangle) (t : Rectangle)
  (ht : t ∈ Ts) :
  t.x ∈ (tiling_grid R Ts).xs ∧ t.x + t.w ∈ (tiling_grid R Ts).xs ∧
  t.y ∈ (tiling_grid R Ts).ys ∧ t.y + t.h ∈ (tiling_grid R Ts).ys := by
    unfold tiling_grid;
    unfold tiling_grid_xs tiling_grid_ys; aesop;

/-- If two tiles in a tiling are distinct, then the sets of grid cells contained in them are
  disjoint. -/
lemma disjoint_cells_of_tiling (R : Rectangle) (Ts : List Rectangle) (h : is_tiling R Ts)
  (t1 t2 : Rectangle) (h1 : t1 ∈ Ts) (h2 : t2 ∈ Ts) (hne : t1 ≠ t2) :
  List.Disjoint (cells_in_rect (tiling_grid R Ts) t1) (cells_in_rect (tiling_grid R Ts) t2) := by
    have h_interiors_disjoint : ∀ t1 t2 : Rectangle, t1 ∈ Ts → t2 ∈ Ts → t1 ≠ t2 →
      t1.interior ∩ t2.interior = ∅ := by
      rcases h with ⟨ h₁, h₂ ⟩;
      intro t1 t2 h1 h2 hne;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h1;
      obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h2;
      subst hi hj
      simp_all only [ne_eq, List.get_eq_getElem, List.getElem_mem]
      apply h₁
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_true_eq_false]
    intro c hc1 hc2;
    obtain ⟨x, y, hx, hy, hc⟩ : ∃ x y : ℝ, x ∈ Set.Ioo c.x (c.x + c.w) ∧
      y ∈ Set.Ioo c.y (c.y + c.h) ∧ x ∈ Set.Ioo t1.x (t1.x + t1.w) ∧
      y ∈ Set.Ioo t1.y (t1.y + t1.h) ∧ x ∈ Set.Ioo t2.x (t2.x + t2.w) ∧
      y ∈ Set.Ioo t2.y (t2.y + t2.h) := by
      unfold cells_in_rect at hc1 hc2;
      simp_all +decide [ List.mem_filter ];
      refine' ⟨ c.x + c.w / 2, _, c.y + c.h / 2, _, _, _, _ ⟩;
      · constructor <;> linarith [ c.w_pos ];
      · constructor <;> linarith [ c.h_pos ];
      · constructor <;> linarith [ c.w_pos ];
      · constructor <;> linarith [ c.h_pos ];
      · constructor <;> constructor <;> linarith [ c.w_pos, c.h_pos ];
    specialize h_interiors_disjoint t1 t2 h1 h2 hne ; simp_all +decide [ Set.ext_iff ];
    exact h_interiors_disjoint x y ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩
      ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩

/-- A grid cell does not cross any x-coordinate of the grid. -/
lemma grid_cell_no_cross_x (g : Grid) (c : Rectangle) (hc : c ∈ g.cells) (x : ℝ) (hx : x ∈ g.xs) :
  x ≤ c.x ∨ c.x + c.w ≤ x := by
    unfold Grid.cells at hc;
    simp +zetaDelta at *;
    obtain ⟨ a, b, h₁, a', b', h₂, h₃, rfl ⟩ := hc;
    rw [ List.mem_iff_get ] at *;
    rcases h₁ with ⟨ n, hn ⟩ ; rcases h₂ with ⟨ m, hm ⟩ ; simp_all +decide ;
    have h_sorted : ∀ i j : Fin g.xs.length, i < j → g.xs[i] < g.xs[j] := by
      exact fun i j hij => g.xs_sorted.rel_get_of_lt hij;
    contrapose! h_sorted;
    obtain ⟨ k, hk ⟩ := hx;
    by_cases h_cases : k.val < n.val + 1;
    · use ⟨ k, by
        exact k.2 ⟩, ⟨ n, by
        exact lt_of_lt_of_le n.2 ( by simp ) ⟩
      generalize_proofs at *;
      grind;
    · use ⟨ n + 1, by
        grind ⟩, k
      generalize_proofs at *;
      grind

/-- A real number `a` is irrational if and only if `\{1, a\}` is linearly independent over
  `\mathbb{Q}`. -/
lemma irrational_linear_independent (a : ℝ) (ha : Irrational a) : LinearIndependent ℚ ![1, a] := by
  refine' Fintype.linearIndependent_iff.2 _;
  intro g hg
  by_contra h_nonzero;
  simp_all +decide [ Fin.sum_univ_succ, Algebra.smul_def ];
  exact ha.ne_rat ( -g 0 / g 1 ) ( by push_cast; rw [ eq_div_iff ( by aesop ) ] ; linarith )

/-- If `a` is irrational, there exists an additive function `f: \mathbb{R} \to \mathbb{R}` such that
  `f(1) = 1` and `f(a) = -1`. This is the key property of the `f` used in our proof. -/
lemma exists_additive_map_of_irrational (a : ℝ) (ha : Irrational a) :
  ∃ f : ℝ →+ ℝ, f 1 = 1 ∧ f a = -1 := by
  have h_basis : ∃ B : Set ℝ, B ⊆ Set.univ ∧ LinearIndependent ℚ (fun x : B => x.val) ∧
    Submodule.span ℚ B = ⊤ ∧ (1 : ℝ) ∈ B ∧ a ∈ B := by
    have h_basis : ∃ B : Set ℝ, LinearIndependent ℚ (fun x : B => x.val) ∧ Submodule.span ℚ B = ⊤ ∧
      (1 : ℝ) ∈ B ∧ a ∈ B := by
      have h_linear_indep : LinearIndependent ℚ ![1, a] := by
        exact irrational_linear_independent a ha
      have := exists_isCompl ( Submodule.span ℚ { 1, a } );
      obtain ⟨ B, hB ⟩ := this;
      obtain ⟨ C, hC ⟩ := exists_linearIndependent ℚ ( B : Set ℝ );
      refine' ⟨ { 1, a } ∪ C, _, _, _, _ ⟩ <;> simp_all +decide [ Submodule.span_union ];
      · rw [ linearIndependent_subtype_iff ] at *;
        refine' LinearIndepOn.union _ _ _;
        · convert h_linear_indep.linearIndepOn_id using 1;
          aesop;
        · exact hC.2.2;
        · simp_all +decide [ Set.image_insert_eq, Set.image_singleton ];
          exact hB.disjoint;
      · exact hB.sup_eq_top;
    simp_all only [Set.subset_univ, true_and]
  obtain ⟨ B, hB₁, hB₂, hB₃, hB₄, hB₅ ⟩ := h_basis;
  obtain ⟨f, hf⟩ : ∃ f : B → ℝ, f ⟨1, hB₄⟩ = 1 ∧ f ⟨a, hB₅⟩ = -1 := by
    use fun x => if x = ⟨1, hB₄⟩ then 1 else if x = ⟨a, hB₅⟩ then -1 else 0;
    simp_all only [Set.subset_univ, ↓reduceIte, Subtype.mk.injEq, ite_eq_right_iff, true_and]
    intro a_1
    subst a_1
    simp_all only [not_irrational_one]
  have h_ext : ∃ g : ℝ →ₗ[ℚ] ℝ, ∀ b : B, g b.val = f b := by
    have h_ext : ∃ g : (B →₀ ℚ) →ₗ[ℚ] ℝ, ∀ b : B, g (Finsupp.single b 1) = f b := by
      exact ⟨ Finsupp.linearCombination ℚ f, fun b => by simp +decide ⟩;
    obtain ⟨ g, hg ⟩ := h_ext;
    have h_ext : ∃ h : (↥B →₀ ℚ) ≃ₗ[ℚ] ℝ, ∀ b : B, h (Finsupp.single b 1) = b.val := by
      refine' ⟨ _, _ ⟩;
      refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
      refine' Finsupp.linearCombination ℚ ( fun x => x.val );
      all_goals norm_num [ Finsupp.linearCombination_apply ];
      · exact hB₂;
      · intro x;
        have := hB₃.ge ( show x ∈ ⊤ from trivial );
        rw [ Finsupp.mem_span_iff_linearCombination ] at this ; aesop;
    obtain ⟨ h, hh ⟩ := h_ext;
    exact ⟨ g.comp h.symm.toLinearMap, fun b => by simp +decide [ ← hg, ← hh ] ⟩;
  exact ⟨ h_ext.choose, by simpa [ hf ] using h_ext.choose_spec ⟨ 1, hB₄ ⟩,
    by simpa [ hf ] using h_ext.choose_spec ⟨ a, hB₅ ⟩ ⟩

/-- If the ratio of two real numbers is irrational, there exists an additive function mapping
  the first to -1 and the second to 1. We explicitly use this slight generalization of
  `exists_additive_map_of_irrational` instead of "assuming the rectangle has sides `1, a`" as in
  the given proof. -/
lemma exists_additive_map_of_irrational_ratio (w h : ℝ) (h_irr : Irrational (w / h)) :
  ∃ f : ℝ →+ ℝ, f w = -1 ∧ f h = 1 := by
  by_cases hh : h = 0;
  · subst hh
    simp_all only [div_zero, not_irrational_zero]
  · obtain ⟨f, hf⟩ : ∃ f : ℝ →+ ℝ, f 1 = 1 ∧ f (w / h) = -1 := by
      exact exists_additive_map_of_irrational (w / h) h_irr;
    use AddMonoidHom.comp f (AddMonoidHom.mk' (fun x => x / h) (by
    exact fun x y => by ring;))
    generalize_proofs at *;
    simp_all only [AddMonoidHom.coe_comp, AddMonoidHom.mk'_apply, Function.comp_apply, ne_eq,
      not_false_eq_true, div_self, and_self]

/-- If a grid cell is contained in a tile, it is contained in the tiled rectangle. -/
lemma union_subset_cells_in_rect (R : Rectangle) (Ts : List Rectangle) (h : is_tiling R Ts) :
  ∀ t ∈ Ts, ∀ c ∈ cells_in_rect (tiling_grid R Ts) t, c ∈ cells_in_rect (tiling_grid R Ts) R := by
    unfold cells_in_rect;
    intros t ht c hc
    have h_t_subset_R : t.x ≥ R.x ∧ t.x + t.w ≤ R.x + R.w ∧ t.y ≥ R.y ∧ t.y + t.h ≤ R.y + R.h := by
      have h_t_subset_R : t.toSet ⊆ R.toSet := by
        exact Set.Subset.trans ( Set.subset_iUnion₂_of_subset t ht ( Set.Subset.refl _ ) ) h.2.le;
      unfold Rectangle.toSet at h_t_subset_R;
      have := h_t_subset_R ( Set.mk_mem_prod ( Set.left_mem_Icc.mpr ( by linarith [ t.w_pos ] ) )
        ( Set.left_mem_Icc.mpr ( by linarith [ t.h_pos ] ) ) ) ;
      have := h_t_subset_R ( Set.mk_mem_prod ( Set.right_mem_Icc.mpr ( by linarith [ t.w_pos ] ) )
        ( Set.right_mem_Icc.mpr ( by linarith [ t.h_pos ] ) ) ) ;
      simp_all only [Bool.decide_and, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
        Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk, ge_iff_le, and_self];
    grind

/-- The center of a grid cell contained in a rectangle is contained in the rectangle. -/
lemma center_mem_rect_of_mem_cells (g : Grid) (R : Rectangle) (c : Rectangle)
  (hc : c ∈ cells_in_rect g R) :
  (c.x + c.w / 2, c.y + c.h / 2) ∈ R.toSet := by
    have h_x_bounds : R.x ≤ c.x ∧ c.x + c.w ≤ R.x + R.w := by
      unfold cells_in_rect at hc; aesop;
    have h_y_bounds : R.y ≤ c.y ∧ c.y + c.h ≤ R.y + R.h := by
      unfold cells_in_rect at hc; aesop;
    constructor <;> constructor <;> linarith [ c.w_pos, c.h_pos ]

/-- If the center of a grid cell is in a tile, then the cell is contained in the tile. -/
lemma cell_subset_tile_of_center_mem (R : Rectangle) (Ts : List Rectangle)
  (c : Rectangle) (hc : c ∈ (tiling_grid R Ts).cells) (t : Rectangle) (ht : t ∈ Ts)
  (h_center : (c.x + c.w / 2, c.y + c.h / 2) ∈ t.toSet) :
  c ∈ cells_in_rect (tiling_grid R Ts) t := by
    refine' List.mem_filter.mpr ⟨ hc, _ ⟩;
    have h_boundaries : t.x ∈ (tiling_grid R Ts).xs ∧ t.x + t.w ∈ (tiling_grid R Ts).xs ∧
      t.y ∈ (tiling_grid R Ts).ys ∧ t.y + t.h ∈ (tiling_grid R Ts).ys := by
      exact tiling_grid_contains_boundaries R Ts t ht;
    have h_no_cross_x : ∀ x ∈ (tiling_grid R Ts).xs, x ≤ c.x ∨ c.x + c.w ≤ x := by
      exact fun x a => grid_cell_no_cross_x (tiling_grid R Ts) c hc x a;
    have h_no_cross_y : ∀ y ∈ (tiling_grid R Ts).ys, y ≤ c.y ∨ c.y + c.h ≤ y := by
      intros y hy;
      convert grid_cell_no_cross_x _ _ _ _ _ using 1;
      rotate_left;
      rotate_left;
      exact ⟨ ( tiling_grid R Ts ).ys, ( tiling_grid R Ts ).xs, ( tiling_grid R Ts ).ys_sorted,
        ( tiling_grid R Ts ).xs_sorted, ( tiling_grid R Ts ).ys_ne_nil,
        ( tiling_grid R Ts ).xs_ne_nil ⟩;
      exact ⟨ c.y, c.x, c.h, c.w, c.h_pos, c.w_pos ⟩;
      rotate_left;
      exact y;
      · exact hy;
      · rfl;
      · rfl;
      · unfold Grid.cells at *; aesop;
    cases h_no_cross_x t.x h_boundaries.1 <;> cases h_no_cross_x ( t.x + t.w ) h_boundaries.2.1 <;>
      cases h_no_cross_y t.y h_boundaries.2.2.1 <;> cases h_no_cross_y ( t.y + t.h )
      h_boundaries.2.2.2 <;> simp_all +decide;
    all_goals unfold Rectangle.toSet at h_center; norm_num at h_center; linarith [ c.w_pos,
      c.h_pos, t.w_pos, t.h_pos ] ;

/-- The `f`-area of a rectangle is the sum of the `f`-areas of the squares in its tiling. This is
  `Claim 2` in the book. -/
lemma f_area_sum_tiling (f : ℝ →+ ℝ) (R : Rectangle) (Ts : List Rectangle) (h : is_tiling R Ts) :
  f_area f R = (Ts.map (f_area f)).sum := by
    have h_sum_f_areas : f_area f R = ∑ c ∈ (tiling_grid R Ts).cells.toFinset,
      if c ∈ cells_in_rect (tiling_grid R Ts) R then f_area f c else 0 := by
      convert sum_cells_in_rect_eq_f_area f ( tiling_grid R Ts ) R _ _ _ _ using 1;
      rw [ sum_cells_in_rect_eq_f_area ];
      all_goals norm_num [ tiling_grid ];
      all_goals norm_num [ tiling_grid_xs, tiling_grid_ys ];
      convert sum_cells_in_rect_eq_f_area f _ _ _ _ _ _ using 1;
      any_goals exact tiling_grid R Ts;
      · rw [ Finset.sum_ite ];
        simp +zetaDelta at *;
        rw [ ← List.sum_toFinset ];
        · congr! 1;
          ext; simp [cells_in_rect];
          unfold tiling_grid;
          intros;
          rfl;
        · refine' List.Nodup.filter _ _;
          unfold Grid.cells;
          rw [ List.nodup_flatMap ];
          constructor;
          · intro x hx;
            rw [ List.nodup_flatMap ];
            constructor;
            · intro x_1 a
              simp_all only
              obtain ⟨fst, snd⟩ := x
              obtain ⟨fst_1, snd_1⟩ := x_1
              simp_all only
              split
              next h_1 => simp_all only
                [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
              next h_1 => simp_all only [not_and, not_lt, List.nodup_nil]
            · rw [ List.pairwise_iff_get ];
              intro i j hij; simp +decide [ List.disjoint_left ] ;
              rintro a ha hb rfl ha' hb';
              intro H; have := congr_arg ( fun z => z.y ) H; norm_num at this;
              have := List.pairwise_iff_get.mp ( show List.Pairwise ( fun x y => x < y )
                ( tiling_grid R Ts |> Grid.ys ) from ( tiling_grid R Ts ).ys_sorted );
              exact absurd ( this ⟨ i, by
                exact lt_of_lt_of_le i.2 ( by simp ) ⟩ ⟨ j, by
                exact j.2.trans_le ( by simp ) ⟩ hij ) ( by aesop );
          · rw [ List.pairwise_iff_get ];
            intro i j hij;
            simp +decide [ Function.onFun, List.disjoint_left ];
            rintro a x y hxy hx hy rfl u v huv hu hv;
            intro H;
            have := List.pairwise_iff_get.mp ( show List.Pairwise ( fun x y => x < y )
              ( tiling_grid R Ts |> Grid.xs ) from ( tiling_grid R Ts ).xs_sorted );
            exact absurd ( this ⟨ i, by
              exact lt_of_lt_of_le i.2 ( by simp ) ⟩ ⟨ j, by
              exact Nat.lt_of_lt_of_le j.2 ( by simp ) ⟩ hij ) ( by aesop );
      · unfold tiling_grid tiling_grid_xs;
        simp_all only [List.mem_dedup, List.mem_mergeSort, List.mem_cons, left_eq_add,
          List.mem_flatMap, List.not_mem_nil, or_false, true_or]
      · exact List.mem_dedup.mpr ( List.mem_mergeSort.mpr ( by aesop ) );
      · exact List.mem_dedup.mpr ( List.mem_mergeSort.mpr ( by aesop ) );
      · exact List.mem_dedup.mpr ( List.mem_mergeSort.mpr ( by aesop ) );
    have h_sum_over_tiles : ∑ c ∈ (tiling_grid R Ts).cells.toFinset,
      (if c ∈ cells_in_rect (tiling_grid R Ts) R then f_area f c else 0) =
      ∑ t ∈ Ts.toFinset, ∑ c ∈ (tiling_grid R Ts).cells.toFinset,
      (if c ∈ cells_in_rect (tiling_grid R Ts) t then f_area f c else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro c hc
      by_cases h_center : (c.x + c.w / 2, c.y + c.h / 2) ∈ R.toSet;
      · obtain ⟨t, ht⟩ : ∃ t ∈ Ts, (c.x + c.w / 2, c.y + c.h / 2) ∈ t.toSet := by
          have := h.2;
          replace this := Set.ext_iff.mp this ( c.x + c.w / 2, c.y + c.h / 2 ) ;
          simp_all only [List.mem_toFinset, Set.mem_iUnion, exists_prop, iff_true]
        have h_cell_subset_tile : c ∈ cells_in_rect (tiling_grid R Ts) t := by
          apply cell_subset_tile_of_center_mem R Ts c (by
          aesop) t ht.left ht.right;
        rw [ Finset.sum_eq_single t ] <;> simp_all +decide [ Finset.sum_ite ];
        · exact fun h => False.elim <| h <| by
            apply union_subset_cells_in_rect R Ts ‹_› t ht.left c h_cell_subset_tile;
        · intros b hb hb_ne_t hb_cell_subset_tile;
          have := disjoint_cells_of_tiling R Ts h b t hb ht.1 hb_ne_t;
          simp_all +decide [ List.disjoint_left ] ;
      · rw [ Finset.sum_eq_zero ];
        · rw [ if_neg ];
          exact fun h => h_center <| center_mem_rect_of_mem_cells _ _ _ h;
        · intro t ht; split_ifs <;> simp_all +decide [ cells_in_rect ] ;
          have h_center_in_t : (c.x + c.w / 2, c.y + c.h / 2) ∈ t.toSet := by
            constructor <;> constructor <;> linarith [ c.w_pos, c.h_pos ];
          exact False.elim <| h_center <| h.2.subset <| Set.mem_iUnion₂.mpr ⟨ t, ht, h_center_in_t ⟩
    have h_inner_sum : ∀ t ∈ Ts.toFinset, ∑ c ∈ (tiling_grid R Ts).cells.toFinset,
      (if c ∈ cells_in_rect (tiling_grid R Ts) t then f_area f c else 0) = f_area f t := by
      intro t ht
      have h_cell_subset : ∀ c ∈ (tiling_grid R Ts).cells.toFinset,
        (if c ∈ cells_in_rect (tiling_grid R Ts) t then f_area f c else 0) =
        (if c ∈ cells_in_rect (tiling_grid R Ts) t then f_area f c else 0) := by
        exact fun _ _ => rfl;
      have h_inner_sum : ∑ c ∈ (tiling_grid R Ts).cells.toFinset,
        (if c ∈ cells_in_rect (tiling_grid R Ts) t then f_area f c else 0) =
        ∑ c ∈ (cells_in_rect (tiling_grid R Ts) t).toFinset, f_area f c := by
        rw [ ← Finset.sum_filter ];
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +contextual;
        exact fun x hx => List.mem_filter.mp hx |>.1;
      convert sum_cells_in_rect_eq_f_area f ( tiling_grid R Ts ) t _ _ _ _ using 1;
      · rw [ h_inner_sum, ← List.sum_toFinset ];
        refine' List.Nodup.filter _ _;
        unfold Grid.cells;
        rw [ List.nodup_flatMap ];
        constructor;
        · intro x hx;
          rw [ List.nodup_flatMap ];
          constructor;
          · grind;
          · rw [ List.pairwise_iff_get ];
            intro i j hij; simp +decide [ List.disjoint_left ] ;
            rintro a ha₁ ha₂ rfl ha₃ ha₄; simp_all +decide ;
            intro h_eq;
            have h_sorted : List.Pairwise (· < ·) (tiling_grid R Ts).ys := by
              exact ( tiling_grid R Ts ).ys_sorted;
            have := List.pairwise_iff_get.mp h_sorted;
            exact absurd h_eq ( ne_of_lt ( this ⟨ i, by
              exact lt_of_lt_of_le i.2 ( by simp ) ⟩ ⟨ j, by
              exact j.2.trans_le ( by simp ) ⟩ hij ) );
        · rw [ List.pairwise_iff_get ];
          intro i j hij; simp +decide [ List.disjoint_left ] ;
          rintro a x y hxy hx hy rfl u v huv hu hv; simp_all +decide ;
          intro h₁ h₂ h₃ h₄;
          have := List.pairwise_iff_get.mp ( tiling_grid R Ts |>.xs_sorted ) ; simp_all +decide;
          exact absurd h₁ ( ne_of_lt ( this ⟨ i, by
            exact lt_of_lt_of_le i.2 ( by simp ) ⟩ ⟨ j, by
            exact j.2.trans_le ( by simp ) ⟩ hij ) );
      · exact tiling_grid_contains_boundaries R Ts t ( List.mem_toFinset.mp ht ) |>.1;
      · exact tiling_grid_contains_boundaries R Ts t ( List.mem_toFinset.mp ht ) |>.2.1;
      · exact tiling_grid_contains_boundaries R Ts t ( List.mem_toFinset.mp ht ) |>.2.2.1;
      · exact tiling_grid_contains_boundaries R Ts t ( List.mem_toFinset.mp ht ) |>.2.2.2;
    rw [ h_sum_f_areas, h_sum_over_tiles, Finset.sum_congr rfl h_inner_sum, List.sum_toFinset ];
    rw [ List.nodup_iff_injective_get ];
    intro i j hij;
    have := h.1 i j;
    contrapose! this;
    simp_all +decide [ Rectangle.interior ];
    exact ⟨ Ts[j].w_pos, Ts[j].h_pos ⟩

/-- If a rectangle can be tiled with squares, then the ratio of its side lengths is rational. -/
lemma rational_ratio_of_tiling (R : Rectangle) (h : can_be_tiled_with_squares R) :
  ∃ (q : ℚ), R.w = q * R.h := by
  by_contra h_irr
  obtain ⟨f, hf1, hf2⟩ : ∃ f : ℝ →+ ℝ, f R.w = -1 ∧ f R.h = 1 := by
    convert exists_additive_map_of_irrational_ratio R.w R.h _ using 1;
    exact fun ⟨ q, hq ⟩ => h_irr ⟨ q, by rw [ hq, div_mul_cancel₀ _ ( by linarith [ R.h_pos ] ) ] ⟩;
  have h_f_area_neg : f_area f R = -1 := by
    unfold f_area; aesop;
  obtain ⟨Ts, hTs_tiling, hTs_squares⟩ := h;
  have h_f_area_sum_nonneg : 0 ≤ (Ts.map (f_area f)).sum := by
    have h_f_area_sum_nonneg : ∀ t ∈ Ts, 0 ≤ f_area f t := by
      intros t ht
      have h_square : t.w = t.h := by
        exact hTs_squares t ht;
      simp [f_area, h_square];
      exact mul_self_nonneg _;
    exact List.sum_nonneg ( by aesop );
  linarith [ f_area_sum_tiling f R Ts hTs_tiling ]

/-- A list of squares forming a grid. This is meant to be an explicit tiling of a rectangle into
  squares whenever we know that the ratio of its side length is rational, by setting an appropriate
  value for `s`, proving one direction of the main theorem. -/
def grid_squares (x y s : ℝ) (m n : ℕ) (hs : 0 < s) : List Rectangle :=
  (List.product (List.range m) (List.range n)).map fun (i, j) =>
    { x := x + i * s, y := y + j * s, w := s, h := s, w_pos := hs, h_pos := hs }

/-- The squares in the above grid are pairwise disjoint. -/
lemma grid_squares_disjoint (x y s : ℝ) (m n : ℕ) (hs : 0 < s) :
  let squares := grid_squares x y s m n hs
  ∀ i j : Fin squares.length, i ≠ j → (squares.get i).interior ∩ (squares.get j).interior = ∅ := by
    unfold grid_squares;
    intro squares i j hij; contrapose! hij; simp_all +decide;
    obtain ⟨ p, hp ⟩ := hij;
    have h_eq : ∃ i' j' : ℕ, i' < m ∧ j' < n ∧ squares[i] = ⟨x + i' * s, y + j' * s, s, s, hs, hs⟩ ∧
      ∃ i'' j'' : ℕ, i'' < m ∧ j'' < n ∧ squares[j] = ⟨x + i'' * s, y + j'' * s, s, s, hs, hs⟩ := by
      have h_eq : ∀ k : Fin squares.length, ∃ i' j' : ℕ,
        i' < m ∧ j' < n ∧ squares[k] = ⟨x + i' * s, y + j' * s, s, s, hs, hs⟩ := by
        intro k; have := List.mem_map.mp ( show squares[k] ∈ squares from by simp +decide ) ; aesop;
      exact ⟨ _, _, h_eq i |> Classical.choose_spec |> Classical.choose_spec |> And.left,
        h_eq i |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.left,
        h_eq i |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.right, _, _,
        h_eq j |> Classical.choose_spec |> Classical.choose_spec |> And.left,
        h_eq j |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.left,
        h_eq j |> Classical.choose_spec |> Classical.choose_spec |> And.right |> And.right ⟩;
    obtain ⟨ i', j', hi', hj', hi, i'', j'', hi'', hj'', hj ⟩ := h_eq;
    simp_all +decide [ Fin.ext_iff, Rectangle.interior ] ;
    have h_eq_indices : i' = i'' ∧ j' = j'' := by
      exact ⟨ Nat.le_antisymm
        ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith } )
        ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith } ),
        Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith })
        ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith } ) ⟩;
    have h_eq_indices : ∀ (l : List Rectangle), List.Nodup l →
      ∀ (i j : Fin l.length), l[i] = l[j] → i = j := by
      exact fun l hl i j hij => by simpa [Fin.ext_iff] using List.nodup_iff_injective_get.mp hl hij;
    convert h_eq_indices squares _ i j _;
    · simp +decide [ Fin.ext_iff ];
    · rw [ List.nodup_map_iff_inj_on ];
      · simp +decide [ Rectangle.ext_iff ];
        grind;
      · exact List.Nodup.product ( List.nodup_range ) ( List.nodup_range );
    · grind

/-- If the rectangle has width `m * s` and height `n * s`, then the union of the squares in the grid
  we defined above is the rectangle itself. -/
lemma grid_squares_union (R : Rectangle) (s : ℝ) (m n : ℕ) (hs : 0 < s)
  (hw : R.w = m * s) (hh : R.h = n * s) :
  let squares := grid_squares R.x R.y s m n hs
  (⋃ t ∈ squares, t.toSet) = R.toSet := by
    have h_union : ⋃ t ∈ grid_squares R.x R.y s m n hs, t.toSet =
      ⋃ i ∈ Finset.range m, ⋃ j ∈ Finset.range n,
      Set.Icc (R.x + i * s) (R.x + (i + 1) * s) ×ˢ Set.Icc (R.y + j * s) (R.y + (j + 1) * s) := by
      unfold grid_squares;
      simp +decide [ Set.ext_iff, Rectangle.toSet ];
      intro a b
      refine ⟨ fun ⟨w, ⟨w_1, ⟨⟨left, right_1⟩, ⟨⟨left_1, right_2⟩, ⟨left_2, right⟩⟩⟩⟩⟩ => ?_,
        fun ⟨w, ⟨left, ⟨w_1, ⟨⟨left_1, right_1⟩, ⟨left_2, ⟨left_3, right⟩⟩⟩ ⟩⟩⟩ => ?_ ⟩
      · refine ⟨w, left_1, w_1, ⟨ ⟨left, right_1⟩, ⟨right_2, ⟨?_, ?_⟩⟩⟩⟩
        · rw[add_mul, one_mul, ← add_assoc]; exact left_2
        · rw[add_mul, one_mul, ← add_assoc]; exact right
      · rw[add_mul, one_mul, ← add_assoc] at left_3 right
        exact ⟨w, w_1, ⟨left_1, right_1⟩, ⟨left, left_2⟩, ⟨left_3, right⟩⟩
    have h_union_eq_R : ⋃ i ∈ Finset.range m, ⋃ j ∈ Finset.range n,
      Set.Icc (R.x + i * s) (R.x + (i + 1) * s) ×ˢ Set.Icc (R.y + j * s) (R.y + (j + 1) * s) =
      Set.Icc R.x (R.x + R.w) ×ˢ Set.Icc R.y (R.y + R.h) := by
      ext ⟨x, y⟩; simp [hw, hh];
      constructor <;> intro h;
      · rcases h with ⟨ i, hi, j, ⟨ hx, hy ⟩, hx', hj, hy' ⟩ ;
        exact ⟨⟨ by nlinarith, by nlinarith ⟩, by nlinarith [ show ( i : ℝ ) + 1 ≤ m by norm_cast ],
          by nlinarith [ show ( j : ℝ ) + 1 ≤ n by norm_cast ] ⟩ ;
      · by_cases hx : x = R.x + m * s;
        · rcases m with ( _ | m ) <;> rcases n with ( _ | n ) <;> norm_num at *;
          · linarith [ R.w_pos ];
          · linarith [ R.w_pos ];
          · linarith [ R.h_pos ];
          · by_cases hy : y = R.y + (n + 1) * s;
            · exact ⟨ m, Nat.lt_succ_self _, n,
                ⟨ by linarith, by linarith ⟩, by linarith, Nat.lt_succ_self _, by linarith ⟩;
            · use m, by linarith, Nat.floor ((y - R.y) / s), by
                exact ⟨ by linarith,
                  by nlinarith [ Nat.floor_le
                      ( show 0 ≤ ( y - R.y ) / s by exact div_nonneg ( by linarith ) hs.le ),
                      mul_div_cancel₀ ( y - R.y ) hs.ne' ] ⟩;
              exact ⟨ by linarith,
                Nat.succ_le_of_lt <|
                by rw [ Nat.floor_lt' ] <;>
                  norm_num ; cases lt_or_gt_of_ne hy <;>
                  nlinarith [ mul_div_cancel₀ ( y - R.y ) hs.ne' ],
                by nlinarith [ Nat.lt_floor_add_one ( ( y - R.y ) / s ),
                  mul_div_cancel₀ ( y - R.y ) hs.ne' ] ⟩;
        · obtain ⟨i, hi⟩ : ∃ i : ℕ, i < m ∧ R.x + i * s ≤ x ∧ x < R.x + (i + 1) * s := by
            use Nat.floor ((x - R.x) / s);
            constructor
            · rw [ Nat.floor_lt ( div_nonneg ( by linarith ) hs.le ) ] ;
              rw [ div_lt_iff₀ hs ] ;
              cases lt_or_gt_of_ne hx <;> nlinarith
            · constructor
              · nlinarith [ Nat.floor_le ( show 0 ≤ ( x - R.x ) / s
                  by exact div_nonneg ( by linarith ) hs.le ), mul_div_cancel₀ ( x - R.x ) hs.ne' ]
              · nlinarith [ Nat.lt_floor_add_one ( ( x - R.x ) / s ),
                  mul_div_cancel₀ ( x - R.x ) hs.ne' ];
          by_cases hy : y = R.y + n * s;
          · by_cases hn : n = 0;
            · have := R.h_pos;
              subst hy hn
              simp_all only [CharP.cast_eq_zero, zero_mul, lt_self_iff_false];
            · refine ⟨ i, hi.1, n-1, ⟨ ⟨hi.2.1, ?_⟩ , ⟨le_of_lt hi.2.2, ?_⟩⟩ ⟩
              · cases n
                · case neg.refine_1.zero =>
                    norm_num at hy;
                    rw[hy];
                    simp only [zero_tsub, CharP.cast_eq_zero, zero_mul, add_zero, le_refl]
                · case neg.refine_1.succ n => rw[hy]; norm_num; linarith
              · cases n
                · case neg.refine_2.zero => simp only [not_true_eq_false] at hn
                · case neg.refine_2.succ n => rw[hy]; norm_num;
          · obtain ⟨j, hj⟩ : ∃ j : ℕ, j < n ∧ R.y + j * s ≤ y ∧ y < R.y + (j + 1) * s := by
              use Nat.floor ((y - R.y) / s);
              constructor
              · rw [ Nat.floor_lt ( div_nonneg ( by linarith ) hs.le ) ] ;
                rw [ div_lt_iff₀ hs ] ;
                cases lt_or_gt_of_ne hy <;> linarith
              · constructor
                · have h1 := Nat.floor_le
                    ( show 0 ≤ ( y - R.y ) / s by exact div_nonneg ( by linarith ) hs.le )
                  have := mul_le_mul_of_nonneg_right h1 (le_of_lt hs)
                  rw [← sub_le_sub_iff_right R.y]
                  simp
                  refine this.trans ?_
                  nth_rewrite 2 [← mul_div_cancel₀ ( y - R.y ) hs.ne']
                  rw [mul_comm]
                · have h1 := Nat.lt_floor_add_one ( ( y - R.y ) / s )
                  have h2 := mul_div_cancel₀ ( y - R.y ) hs.ne'
                  have := (mul_lt_mul_iff_left₀ hs).mpr h1
                  grind
            exact ⟨ i, hi.1, j, ⟨ hi.2.1, hj.2.1 ⟩, hi.2.2.le, hj.1, hj.2.2.le ⟩;
    exact h_union.trans h_union_eq_R

/-- The list of squares generated by `grid_squares` forms a tiling of the rectangle. -/
lemma grid_squares_is_tiling (R : Rectangle) (s : ℝ) (m n : ℕ) (hs : 0 < s)
  (hw : R.w = m * s) (hh : R.h = n * s) :
  is_tiling R (grid_squares R.x R.y s m n hs) := by
    constructor;
    · convert grid_squares_disjoint R.x R.y s m n hs using 1;
    · exact grid_squares_union R s m n hs hw hh

/-- A rectangle can be tiled with squares if and only if the ratio of its side lengths is a
  rational number. -/
theorem tiling_iff_rational_ratio (R : Rectangle) :
  can_be_tiled_with_squares R ↔ ∃ (q : ℚ), R.w = q * R.h := by
  constructor <;> intro h;
  · exact rational_ratio_of_tiling R h;
  · obtain ⟨q, hq⟩ := h
    obtain ⟨m, n, hm, hn, hs⟩ : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ R.w = m * (R.h / n) := by
      obtain ⟨m, n, hm, hn, hs⟩ : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ q = m / n := by
        have hq_pos : 0 < q := by
          exact_mod_cast ( by nlinarith [ R.w_pos, R.h_pos ] : ( 0 : ℝ ) < q );
        exact ⟨ q.num.natAbs, q.den, by aesop, Nat.cast_pos.mpr q.pos,
          by simpa [ abs_of_pos ( Rat.num_pos.mpr hq_pos ) ] using q.num_div_den.symm ⟩;
      exact ⟨ m, n, hm, hn, by rw [ hq, hs ] ; push_cast; ring ⟩;
    have h_tiling : is_tiling R (grid_squares R.x R.y (R.h / n) m n (by
    exact div_pos R.h_pos ( Nat.cast_pos.mpr hn ))) := by
      all_goals generalize_proofs at *;
      convert grid_squares_is_tiling R ( R.h / n ) m n ‹_› _ _ using 1 <;> ring_nf;
      · exact hs.trans ( by ring );
      · rw [ mul_right_comm, mul_inv_cancel₀ ( by positivity ), one_mul ]
    generalize_proofs at *;
    use grid_squares R.x R.y (R.h / n) m n ‹_›;
    unfold grid_squares;
    simp_all only [gt_iff_lt, List.mem_map, Prod.exists, List.pair_mem_product, List.mem_range,
      forall_exists_index, and_imp]
    apply And.intro
    · exact h_tiling
    · intro t x x_1 a a_1 a_2
      subst a_2
      rfl;
