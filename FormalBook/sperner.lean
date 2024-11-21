import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic



local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators


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


noncomputable def vertex_set (T : Triangle) : Finset ℝ² :=
    Finset.image T Finset.univ





lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closed_simplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (Finset.sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := Finset.sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closed_simplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push_neg at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := Finset.sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero (fun _ ↦ 0) (fun _ ↦ rfl)
  linarith
