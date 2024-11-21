import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic



local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

def closed_triangle (T : Triangle) : Set ℝ² :=
    (fun α ↦ ∑ i, α i • T i) '' closed_simplex 3

def open_triangle (T : Triangle) : Set ℝ² :=
    (fun α ↦ ∑ i, α i • T i) '' open_simplex 3

def closed_segment (L : Segment) : Set ℝ² :=
    (fun α ↦ ∑ i, α i • L i) '' closed_simplex 2

def open_segment (L : Segment) : Set ℝ² :=
    (fun α ↦ ∑ i, α i • L i) '' open_simplex 2


noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (- (T 0 1) * (T 1 0) + (T 0 0) * (T 1 1) + (T 0 1) * (T 2 0) - (T 1 1) * (T 2 0) - (T 0 0) * (T 2 1) + (T 1 0) * (T 2 1)) / 2

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_triangle T) ∧
  (Set.PairwiseDisjoint S open_triangle) ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)

def unit_square : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle), is_equal_area_cover unit_square S ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  sorry




/- Some examples. -/
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl

def Δ₀  : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)


def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} :
    simplex_vertex i ∈ closed_simplex n := by
  unfold simplex_vertex
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp_all, by simp⟩

/- Ofcourse the image of f does not have to be ℝ² in this lemma. -/
@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by
  unfold simplex_vertex; simp








noncomputable def vertex_set (T : Triangle) : Finset ℝ² :=
    image T univ






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
  sorry

/- A convexity version of closed triangles. -/
lemma closed_triangle_convex {T : Triangle} {L : Segment}
  (h₀ : L 0 ∈ closed_triangle T) (h₁ : L 1 ∈ closed_triangle T) :
  closed_segment L ⊆ closed_triangle T := by

  sorry

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
lemma non_vtx_imp_seg (T : Triangle) (v : ℝ²) (h₁ : v ∉ vertex_set T) (h₂ : v ∈ closed_triangle T) :
    ∃ (L : Segment), L 0 ≠ L 1 ∧ closed_segment L ⊆ closed_triangle T ∧ v ∈ open_segment L := by
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
  · refine closed_triangle_convex ?_ ?_
    · exact ⟨simplex_vertex i, ⟨simplex_vertex_in_simplex, by simp⟩⟩
    · use fun j ↦ if j = i then 0 else (α j) / (1 - α i)
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




example {a b c : ℝ} (h₁ : a ≠ 0) (h₂ : a  = b ) : a + c = b + c ↔ a = b := by
  exact add_right_cancel_iff

  sorry
