import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs



local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n


noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (- (T 0 1) * (T 1 0) + (T 0 0) * (T 1 1) + (T 0 1) * (T 2 0) - (T 1 1) * (T 2 0) - (T 0 0) * (T 2 1) + (T 1 0) * (T 2 1)) / 2

def is_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_hull T) ∧
  (Set.PairwiseDisjoint S open_hull)


def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)

def unit_square : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  sorry




def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


/- These two triangles dissect the square and have equal area.-/
def Δ₀  : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

/- Corner of the standard simplex.-/
def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

/- Such a corner is actually a member of the simplex-/
lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} :
    simplex_vertex i ∈ closed_simplex n := by
  unfold simplex_vertex
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp_all, by simp⟩


@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by
  unfold simplex_vertex; simp

lemma vertex_mem_closed {n : ℕ} {i : Fin n} {f : Fin n → ℝ²} :
    f i ∈ ((fun α ↦ ∑ i, α i • f i) '' closed_simplex n) :=
  ⟨simplex_vertex i, ⟨simplex_vertex_in_simplex, by simp⟩⟩











noncomputable def vertex_set {n : ℕ} (P : Fin n → ℝ²) : Finset ℝ² :=
    image P univ






lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closed_simplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closed_simplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push_neg at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero _ (fun _ ↦ rfl)
  linarith



lemma simplex_co_leq_1 {n : ℕ} {α : Fin n → ℝ}
    (h₁ : α ∈ closed_simplex n) : ∀ i, α i ≤ 1 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨i,hi⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1   < α i             := hi
    _   = ∑ k ∈ {i}, α k  := (sum_singleton _ _).symm
    _   ≤ ∑ k, α k        := sum_le_univ_sum_of_nonneg h₁.1
    _   = 1               := h₁.2



/- Vertex set of polygon P₁ lies inside the closed hull of polygon P₂ implies
    the closed hull of P₁ lies inside the closed hull of P₂. -/
lemma closed_hull_convex {n₁ n₂ : ℕ} {P₁ : Fin n₁ → ℝ²} {P₂ : Fin n₂ → ℝ²}
  (h : ∀ i, P₁ i ∈ closed_hull P₂) :
  closed_hull P₁ ⊆ closed_hull P₂ := by
  intro p ⟨β, hβ, hβp⟩
  use fun i ↦ ∑ k, (β k) * (choose (h k) i)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact fun _ ↦ Fintype.sum_nonneg fun _ ↦ mul_nonneg (hβ.1 _) ((choose_spec (h _)).1.1 _)
  · simp_rw [sum_comm (γ := Fin n₂), ←mul_sum, (choose_spec (h _)).1.2, mul_one]
    exact hβ.2
  · simp_rw [sum_smul, mul_smul, sum_comm (γ := Fin n₂), ←smul_sum, (choose_spec (h _)).2]
    exact hβp




/- A basic lemma about sums that I want to use but that I cannot find.-/
lemma sum_if_comp {α β : Type} [Fintype α] [AddCommMonoid β] (f : α → β) (i : α) :
    ∑ k, (if k = i then 0 else f k) = ∑ k ∈ {i}ᶜ, f k := by
  rw [←sum_add_sum_compl {i}, add_comm, ←add_zero (∑ k ∈ {i}ᶜ, f k)]
  congr 1
  · exact sum_ite_of_false (fun _ hk₁ hk₂ ↦ by simp at hk₁; exact hk₁ hk₂) _ _
  · simp


/-
  Given a v ∈ ℝ² inside a closed triangle that is not one of its vertices
  there exists a (non-trivial) segment L with v in its interior and
  L inside the closed triangle. This statement is true even if the triangle
  is degenerate.
-/
lemma non_vtx_imp_seg (T : Triangle) (v : ℝ²) (h₁ : v ∉ vertex_set T) (h₂ : v ∈ closed_hull T) :
    ∃ (L : Segment), L 0 ≠ L 1 ∧ closed_hull L ⊆ closed_hull T ∧ v ∈ open_hull L := by
  have ⟨α, hα, hvα⟩ := h₂; dsimp at hvα
  have ⟨i,hi⟩ := simplex_exists_co_pos hα
  have hneq : α i ≠ 1 := by
    intro hcontra
    refine h₁ (mem_image.mpr ⟨i, by simp, ?_⟩)
    rw [←hvα, ←sum_add_sum_compl {i} fun k ↦ α k • T k, ←add_zero (T i)]
    congr
    · rw [sum_singleton, hcontra, one_smul]
    · refine (sum_eq_zero ?_).symm
      intro k hk; simp at hk
      rw [simplex_co_eq_1 hα hcontra k hk, zero_smul]
  have heq : v - α i • T i = (1 - α i) • ∑ k ∈ {i}ᶜ, (α k / (1 - α i)) • T k := by
    simp [smul_sum, smul_smul, mul_div_cancel₀ _ (sub_ne_zero_of_ne hneq.symm),
      sub_eq_iff_eq_add', ←hvα, ←sum_add_sum_compl {i} fun k ↦ α k • T k]
  use fun | 0 => T i | 1 => ∑ k ∈ {i}ᶜ, ((α k) / (1 - α i)) • T k
  dsimp
  refine ⟨?_,?_,?_⟩
  · intro hTi
    refine h₁ (mem_image.mpr ⟨i, by simp, ?_⟩)
    have hcontra := congrArg (HSMul.hSMul (1 - α i)) hTi
    simp only [sub_smul, one_smul, ← heq, sub_eq_iff_eq_add', add_sub_cancel] at hcontra
    exact hcontra
  · apply closed_hull_convex
    intro k; fin_cases k
    exact vertex_mem_closed
    use fun j ↦ if j = i then 0 else (α j) / (1 - α i)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro j
      by_cases h : j = i <;> simp_all
      exact div_nonneg (hα.1 j) (sub_nonneg_of_le (simplex_co_leq_1 hα i))
    · convert sum_if_comp (fun j ↦ (α j /  (1 - α i))) i
      apply mul_left_cancel₀ (sub_ne_zero_of_ne hneq.symm)
      simp [mul_sum, mul_div_cancel₀ _ (sub_ne_zero_of_ne hneq.symm),sub_eq_iff_eq_add']
      convert hα.2.symm
      rw [←(sum_add_sum_compl {i} fun k ↦ α k)]
      convert add_right_cancel_iff.mpr (sum_singleton _ _).symm
      exact AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd ℝ -- This feels strange
    · simp
      convert sum_if_comp (fun j ↦ (α j /  (1 - α i)) • T j) i
  · use fun | 0 => α i | 1 => 1 - α i
    refine ⟨⟨?_, by simp⟩,?_⟩
    · intro k
      fin_cases k <;> simp
      · linarith
      · exact lt_of_le_of_ne (simplex_co_leq_1 hα _) hneq
    · simp [←heq]

/-
  There is no non-trivial segment going through (0,0) of the unit square.
  This should imply the same statement for the other corners of the square without too much work.
-/
lemma no_segment_through_origin_square {L : Segment} (h₁ : L 0 ≠ L 1)
    (h₂ : closed_hull L ⊆ unit_square) : v 0 0 ∉ open_hull L := by
  have hNonzero : ∃ i j, L i j ≠ 0 := by
    by_contra hcontra; push_neg at hcontra
    exact h₁ (PiLp.ext fun i ↦ (by rw [hcontra 0 i, hcontra 1 i]))
  have ⟨i,j,hNonzero⟩ := hNonzero
  intro ⟨α,hα,hαv⟩
  have hLpos : ∀ l k, 0 ≤ L l k := by
    intro l k
    have ⟨_,_,_,_⟩ := h₂ (vertex_mem_closed (i := l))
    fin_cases k <;> assumption
  rw [←lt_self_iff_false (0 : ℝ)]
  calc
    0 < α i * L i j             := mul_pos (hα.1 i) (lt_of_le_of_ne (hLpos i j) (hNonzero.symm))
    _ = ∑ k ∈ {i}, α k * L k j  := by simp
    _ ≤ ∑ k, α k * L k j        := sum_le_univ_sum_of_nonneg (fun k ↦ (mul_nonneg_iff_of_pos_left (hα.1 k)).mpr (hLpos k j))
    _ ≤ (v 0 0) j               := by rw [←hαv]; simp
    _ = 0                       := by fin_cases j <;> simp





/-
  Dions stuff

  For a collection of segments, we define the collection of basis segments.
  Next, we define what it means for a collection of segments to be complete,
  and we show that any segment in a complete collection is a union of basis segments.
-/

local notation "SegmentSet" => Finset Segment


instance partialorder (X : SegmentSet) : Preorder X where
  le := fun S ↦ (fun T ↦ closed_hull S.val ⊆ closed_hull T.val)
  le_refl := by exact fun a ⦃a_1⦄ a ↦ a
  le_trans := by exact fun a b c a_1 a_2 ⦃a_3⦄ a ↦ a_2 (a_1 a)


-- A basis segment is a segment that does not properly contain another segment
def basis_segment (X : SegmentSet) (S : X) : Prop :=
  ∀ T : X, closed_hull T.val ⊆ closed_hull S.val → closed_hull T.val = closed_hull S.val

-- A SegmentSet is complete if for any inclusions of segements, the closure of the complement
-- of a segment is also in the SegmentSet
def complete_segment_set (X : SegmentSet) : Prop :=
  ∀ S T : X, closed_hull S.val ⊂ closed_hull T.val → ∃ S' : X,
  (closed_hull T.val = closed_hull S.val ∪ closed_hull S'.val ∧
  ∃ p : ℝ², closed_hull S.val ∩ closed_hull S'.val = {p})

-- A decomposition of a segment is a collection of segments covering it
def segment_covering {X : SegmentSet} (S : X) {n : ℕ} (f : Fin n → X) : Prop :=
  closed_hull S.val = ⋃ (i : Fin n), closed_hull (f i).val

-- A SegmentSet is splitting if every segment is the union of the basic segments it contains.
def splitting_segment_set : SegmentSet → Prop :=
  fun X ↦ ∀ S : X, ∃ n : ℕ, ∃ f : Fin n → X,
  (segment_covering S f ∧ ∀ i : Fin n, basis_segment X (f i))


theorem complete_is_splitting (X : SegmentSet) (h : complete_segment_set X) :
  splitting_segment_set X := by
    sorry

-- Example: if X : Segment_Set is a singleton, its only member is a basis segment
example (S : Segment) : basis_segment (singleton S) ⟨S, by tauto⟩  := by
  intro T _
  have hTeqS : T = S := by
    rw [← Set.mem_singleton_iff]
    exact Set.mem_toFinset.mp T.2
  exact congrArg closed_hull hTeqS


theorem basis_segments_exist (X : SegmentSet) :
  ∃ S : X, basis_segment X S := by
  sorry




/-
  Lenny's stuff

-/


-- side i of triangle T; probably better to do this for a polygon or so

def side (T : Triangle) (i : Fin 3) : Segment :=
  fun | 0 => T ((i + 1) % 3) | 1 => T ((i - 1) % 3)


-- let's just test if this works

variable (P Q R : ℝ²)

def triangle (P Q R : ℝ²) : Triangle :=
  fun | 0 => P | 1 => Q | 2 => R

def interval (P Q : ℝ²) : Segment :=
  fun | 0 => P | 1 => Q

example : side (triangle P Q R) 0 = interval Q R := rfl
example : side (triangle P Q R) 1 = interval R P := rfl
example : side (triangle P Q R) 2 = interval P Q := rfl

-- now we can define the notion of a segment being on a trianglef




def segment_on_triangle (L : Segment) (T : Triangle)  : Prop :=
  ∃ i : Fin 3, closed_hull L ⊆ closed_hull (side T i)



/-
  State the theorem on colourings
-/

-- things carried over from other groups:

def color : ℝ² → Fin 3 := sorry

lemma no_three_colors_on_a_line (L : Segment) :
    ∃ i : Fin 3, ∀ P ∈ closed_hull L, color P ≠ i := sorry

lemma color00 : color (v 0 0) = 0 := sorry
lemma color01 : color (v 0 1) = 1 := sorry
lemma color10 : color (v 1 0) = 2 := sorry


-- main goal for our group

theorem Monsky_rainbow (S : Finset Triangle) (hS : is_cover unit_square S) :
    ∃ T ∈ S, Function.Surjective (color ∘ T) := sorry
