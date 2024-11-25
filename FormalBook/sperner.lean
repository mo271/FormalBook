import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs
import Mathlib.Data.Real.Sign


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

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_hull T) ∧
  (Set.PairwiseDisjoint S open_hull) ∧
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


lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext v
  constructor
  · intro ⟨α, hα,hαv⟩
    simp [←sum_smul, hα.2] at hαv
    exact hαv.symm
  · intro hv
    rw [hv]
    exact vertex_mem_closed (i := ⟨0,Nat.zero_lt_of_ne_zero hn⟩)






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


/- Basic lemmas about signs. -/
lemma sign_mul_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  by_cases hb₀ : 0 < b
  · rw [Real.sign_of_pos hb₀, Real.sign_of_pos (mul_pos ha hb₀)]
  · by_cases hb₁ : b < 0
    · rw [Real.sign_of_neg hb₁, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb₁)]
    · simp [(by linarith : b = 0)]

lemma sign_pos' {a : ℝ} (h : Real.sign a = 1) : 0 < a := by
  by_contra hnonpos; simp at hnonpos
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_neg (lt_of_le_of_ne hnonpos h0 )] at h
    linarith

lemma sign_neg' {a : ℝ} (h : Real.sign a = -1) : a < 0 := by
  by_contra hnonneg; simp at hnonneg
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_pos (lt_of_le_of_ne hnonneg ?_)] at h
    linarith
    exact fun a_1 ↦ h0 (id (Eq.symm a_1)) -- very strange

lemma sign_div_pos {a b : ℝ} (hb₀ : b ≠ 0) (hs : Real.sign a = Real.sign b) :
    0 < a / b := by
  cases' Real.sign_apply_eq_of_ne_zero _ hb₀ with hbs hbs <;> rw [hbs] at hs
  · exact div_pos_of_neg_of_neg (sign_neg' hs) (sign_neg' hbs)
  · exact div_pos (sign_pos' hs) (sign_pos' hbs)

example {a b : ℝ} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a / b := by
  exact div_pos h₁ h₂

/- Proofs of these helper things are ugly-/
lemma mul_cancel {a b c : ℝ} (h : a ≠ 0) (h2: a * b = a * c) :
        b = c := by simp_all only [ne_eq, mul_eq_mul_left_iff, or_false]

lemma smul_cancel {a : ℝ} {b c : ℝ²} (h₁ : a ≠ 0) (h₂: a • b = a • c)
    : b = c := by
  refine PiLp.ext ?_
  intro i
  rw [PiLp.ext_iff] at h₂
  have l := h₂ i
  simp [PiLp.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, h₁] at l
  assumption


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
  Some stuff about bijections Fin 3 → Fin 3.
  This might be useful to brute force things later.
-/

def bijections_Fin3 : Fin 6 → (Fin 3 → Fin 3) := fun
| 0 => (fun | 0 => 0 | 1 => 1 | 2 => 2)
| 1 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
| 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)
| 3 => (fun | 0 => 1 | 1 => 2 | 2 => 0)
| 4 => (fun | 0 => 2 | 1 => 0 | 2 => 1)
| 5 => (fun | 0 => 2 | 1 => 1 | 2 => 0)

def b_sign : Fin 6 → ℝ := fun
  | 0 => 1 | 1 => -1 | 2 => -1 | 3 => 1 | 4 => 1 | 5 => -1

def b_inv : Fin 6 → Fin 6 := fun
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5

def last_index : Fin 3 → Fin 3 → Fin 3 := fun
  | 0 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
  | 1 => (fun | 0 => 2 | 1 => 1 | 2 => 0)
  | 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)




lemma last_index_diff {i j : Fin 3} (hij : i ≠ j) :
    i ≠ last_index i j ∧ j ≠ last_index i j := by
  fin_cases i <;> fin_cases j <;> tauto

lemma last_index_comp {i j : Fin 3} (hij : i ≠ j) :
    ({i,j} : Finset (Fin 3))ᶜ = {last_index i j} := by
  fin_cases i <;> fin_cases j <;> tauto

lemma bijection_right_inv
    : ∀ b, (bijections_Fin3 b) ∘ (bijections_Fin3 (b_inv b)) = id := by
  intro b; funext x
  fin_cases b <;> fin_cases x <;> rfl

lemma bijection_left_inv
    : ∀ b, (bijections_Fin3 (b_inv b)) ∘ (bijections_Fin3 b) = id := by
  intro b; funext x
  fin_cases b <;> fin_cases x <;> rfl

lemma fun_in_bijections {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ b, bijections_Fin3 b = (fun | 0 => i | 1 => j | 2 => k)  := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (tauto)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

lemma sign_non_zero : ∀ b, b_sign b ≠ 0 := by
  intro b; fin_cases b <;> simp [b_sign]


/- Given i j map to the bijection that maps i to 0, j to 1 and last to 2 -/
def normalize_map : Fin 3 → Fin 3 → (Fin 3 → Fin 3) := fun
  | 0 => (fun | 0 => bijections_Fin3 0 | 1 => bijections_Fin3 0 | 2 => bijections_Fin3 1)
  | 1 => (fun | 0 => bijections_Fin3 2 | 1 => bijections_Fin3 0 | 2 => bijections_Fin3 4)
  | 2 => (fun | 0 => bijections_Fin3 3 | 1 => bijections_Fin3 5 | 2 => bijections_Fin3 0)


lemma normalize_val_i {i j : Fin 3} (hij : i ≠ j) : normalize_map i j i = 0 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, bijections_Fin3]; try tauto)

lemma normalize_val_j {i j : Fin 3} (hij : i ≠ j) : normalize_map i j j = 1 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, bijections_Fin3]; try tauto)

lemma normalize_val_k {i j : Fin 3} (hij : i ≠ j)
    : normalize_map i j (last_index i j) = 2 := by
  fin_cases i <;> fin_cases j <;> (simp [normalize_map, last_index, bijections_Fin3]; try tauto)





/-
  Better I think to just define the determinant.
-/

def det (T : Triangle) : ℝ
  := (T 0 1 - T 1 1) * (T 2 0) + (T 1 0 - T 0 0) * (T 2 1) + ((T 0 0) * (T 1 1) - (T 1 0) * (T 0 1))

lemma linear_combination_det_last {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => y | 2 => (∑ i, α i • P i)) =
  ∑ i, (α i * det (fun | 0 => x | 1 => y | 2 => (P i))) := by
  simp [det, left_distrib, sum_add_distrib, sum_apply _, mul_sum, ←sum_mul, hα]
  congr <;> (ext; ring)

lemma det_perm {T : Triangle} (b : Fin 6) :
    det T = (b_sign b) *  det (T ∘ (bijections_Fin3 b)) := by
  fin_cases b <;> (simp_all [det, b_sign, bijections_Fin3]; try ring)

lemma det_zero_perm {T : Triangle} (hT  : det T = 0) :
    ∀ i j k, det (fun | 0 => T i | 1 => T j | 2 => T k) = 0 := by
  intro i j k
  by_cases hij : i = j
  · simp [det, hij]
  · by_cases hik : i = k
    · simp [det, hik]; ring
    · by_cases hjk : j = k
      · simp [det, hjk]; ring
      · have ⟨b, hb⟩ := fun_in_bijections hij hik hjk
        rw [det_perm b] at hT
        convert eq_zero_of_ne_zero_of_mul_left_eq_zero (sign_non_zero b) hT
        split <;> simp [hb]

lemma det_zero_01 {T : Triangle} (h01 : T 0 = T 1) :
    det T = 0 := by simp [det, h01]

lemma det_zero_02 {T : Triangle} (h02 : T 0 = T 2) :
    det T = 0 := by simp [det, h02]; ring

lemma det_zero_12 {T : Triangle} (h12 : T 1 = T 2) :
    det T = 0 := by simp [det, h12]; ring

/- Doing it with bijections here doesn't really seem to gain anything. -/
lemma linear_combination_det_middle {n : ℕ} {x z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => (∑ i, α i • P i) | 2 => z) =
  ∑ i, (α i * det (fun | 0 => x | 1 => (P i) | 2 => z)) := by
  convert linear_combination_det_last (y := x) (P := P) (x := z) hα using 1
  · convert det_perm 4
    simp [b_sign, bijections_Fin3];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 4
    simp [b_sign, bijections_Fin3];
    congr; funext k; fin_cases k <;> rfl

lemma linear_combination_det_first {n : ℕ} {y z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => (∑ i, α i • P i) | 1 => y | 2 => z) =
  ∑ i, (α i * det (fun | 0 => (P i) | 1 => y | 2 => z)) := by
  convert linear_combination_det_last (y := z) (P := P) (x := y) hα using 1
  · convert det_perm 3
    simp [b_sign, bijections_Fin3];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 3
    simp [b_sign, bijections_Fin3];
    congr; funext k; fin_cases k <;> rfl



lemma det_0_triangle_imp_triv {T : Triangle} (hT : det T = 0) :
    ∀ x y z, x ∈ closed_hull T → y ∈ closed_hull T → z ∈ closed_hull T →
      det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  intro x y z ⟨_, ⟨_, hαx⟩ , hx⟩ ⟨_, ⟨_, hαy⟩ , hy⟩ ⟨_, ⟨_, hαz⟩ , hz⟩
  simp [←hx, ← hy, ←hz, linear_combination_det_first hαx,
    linear_combination_det_middle hαy, linear_combination_det_last hαz, det_zero_perm hT]


def sign_seg (L : Segment) (v : ℝ²) : ℝ := det (fun | 0 => L 0 | 1 => L 1 | 2 => v)

lemma open_triangle_sign_det {T : Triangle} {i j : Fin 3} (hij : i ≠ j) :
    ∀ v ∈ open_hull T,
    Real.sign (sign_seg (fun | 0 => T i | 1 => T j) v) =
    Real.sign (det (fun | 0 => T i | 1 => T j | 2 => T (last_index i j))) := by
  intro v ⟨α,⟨hαpos,hα⟩ ,hαv⟩
  rw [←hαv, sign_seg, linear_combination_det_last hα, ←sum_add_sum_compl {i,j},
      sum_pair hij, det_zero_02, det_zero_12, last_index_comp hij]
  simp [sign_mul_pos (hαpos _)]
  all_goals rfl


/-
def boundary_triangle (T : Triangle) : Set ℝ² :=
    closed_hull ((fun | 0 => T 0 | 1 => T 1) : Segment) ∪
    closed_hull ((fun | 0 => T 1 | 1 => T 2) : Segment) ∪
    closed_hull ((fun | 0 => T 2 | 1 => T 0) : Segment)
-/

def boundary_triangle (T : Triangle) : Set ℝ² :=
  ⋃ l : Prod (Fin 3) (Fin 3), closed_hull ((fun | 0 => T l.1 | 1 => T l.2) : Segment)


lemma boundary_sub_closed (T : Triangle)
    : boundary_triangle T ⊆ closed_hull T := by
  intro v ⟨S, ⟨⟨i,j⟩, hS⟩ ,hvS⟩
  rw [←hS] at hvS; dsimp at hvS
  by_cases hij : i = j
  · rw [hij] at hvS
    conv at hvS => lhs; change closed_hull (fun (_ : Fin 2) ↦ T j)
    simp_rw [closed_hull_constant (n := 2) (P := T j) (by simp)] at hvS
    rw [hvS]
    exact vertex_mem_closed
  · have ⟨α, hα, hαv⟩ := hvS
    use (fun | 0 => α 0 | 1 => α 1 | 2 => 0) ∘ (normalize_map i j)
    constructor
    · constructor
      · intro l
        fin_cases l <;> fin_cases i <;> fin_cases j
        all_goals (try tauto)
        all_goals (simp [normalize_map, bijections_Fin3, hα.1 0, hα.1 1])
      · simp [←sum_add_sum_compl {i,j}, last_index_comp hij,
          sum_pair hij, normalize_val_i hij, normalize_val_j hij, normalize_val_k hij]
        convert hα.2
        exact (Fin.sum_univ_two α).symm
    · dsimp at hαv
      simp [←hαv, Fin.sum_univ_two, ←sum_add_sum_compl {i,j}, last_index_comp hij,
          sum_pair hij, normalize_val_i hij, normalize_val_j hij, normalize_val_k hij]

lemma open_triangle_iff (T : Triangle) (hdet : det T ≠ 0) (v : ℝ²) :
    v ∈ open_hull T ↔
    ∀ b : Fin 6,
      Real.sign (sign_seg (fun | 0 => T ((bijections_Fin3 b) 0) | 1 => T ((bijections_Fin3 b) 1)) v)  =
      Real.sign (det (T ∘ (bijections_Fin3 b))) := by
  constructor
  · intro hv b
    have temp := open_triangle_sign_det (?_ : bijections_Fin3 b 0 ≠ bijections_Fin3 b 1) v hv
    · rw [temp]
      congr
      fin_cases b <;> funext i <;> fin_cases i <;> simp [last_index, bijections_Fin3]
    · fin_cases b <;> simp [bijections_Fin3]
  · intro hb
    use fun
      | 0 => (sign_seg (fun | 0 => T 1 | 1 => T 2) v) / (det T)
      | 1 => (sign_seg (fun | 0 => T 2 | 1 => T 0) v) / (det T)
      | 2 => (sign_seg (fun | 0 => T 0 | 1 => T 1) v) / (det T)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i; fin_cases i <;> (dsimp; apply sign_div_pos hdet;)
      · convert (hb 3) using 1
        rw [det_perm 3, b_sign]
        simp
      · convert (hb 4) using 1
        rw [det_perm 4, b_sign]
        simp
      · convert (hb 0) using 1
    · apply mul_cancel hdet
      simp_rw [mul_sum, Fin.sum_univ_three, mul_div_cancel₀ _ hdet, sign_seg, det]
      ring
    · apply smul_cancel hdet
      simp [smul_sum, smul_smul, Fin.sum_univ_three, mul_div_cancel₀ _ hdet]
      simp [sign_seg, det]
      apply PiLp.ext
      intro i
      fin_cases i <;> (simp; ring)


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
