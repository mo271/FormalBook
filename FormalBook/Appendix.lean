import Mathlib.Tactic

noncomputable section

open ValuationSubring
open Algebra

-- Any maximal subring of ℝ not containing 1/2 is a valuation ring.
lemma inclusion_maximal_valuation (B : Subring ℝ) (h1 : (1/2) ∉ B)
(h2 : ∀(C : Subring ℝ), (B ≤ C) ∧ (1/2) ∉ C → B = C) : ∃(D : ValuationSubring ℝ), D.toSubring = B := by
  by_contra no_vr
  have alpha_existence : ∃(α : ℝ), (α ∉ B ∧ α⁻¹ ∉ B) := by
    by_contra H
    rw[← not_forall_not, not_not] at H
    simp_rw[← or_iff_not_and_not] at H
    -- def D : ValuationSubring ℝ :=
    --   { B with
    --     mem_or_inv_mem' := H}
    sorry
  cases' alpha_existence with α H
  let Balpha := adjoin B {a : ℝ | a = α}
  let Balpha' := adjoin B {a : ℝ | a = α⁻¹}
  let twoBalpha := {b : ℝ | ∃c ∈ Balpha, b = 2*c}
  let twoBalpha' := {b : ℝ | ∃c ∈ Balpha', b = 2*c}
  have rings_equal : twoBalpha = Balpha ∧ twoBalpha' = Balpha' := by

    sorry
  sorry


-- There exists a valuation subring of ℝ not containing 1/2.
lemma valuation_ring_no_half : ∃(B : ValuationSubring ℝ), (1/2) ∉ B := by
  let S := {A : Subring ℝ | (1/2) ∉ A}
  have h1 : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    -- Idea: The upper bound is the union of the subrings.

    sorry
  have h2 := zorn_le₀ S h1
  rcases h2 with ⟨B, hl, hr⟩
  have h3 : ∀(C : Subring ℝ), (B ≤ C) ∧ (1/2) ∉ C → B = C := by
    -- Idea: This is exactly hr, so maybe change statement of
    -- inclusion_maximal_valuation to have hr as hypothesis.
    rintro y ⟨h2, h3⟩
    have h4 : y ∈ S := by
      exact h3
    have h5 : y ≤ B := hr h4 h2
    exact LE.le.antisymm h2 h5
  have h4 := inclusion_maximal_valuation B hl h3
  cases' h4 with D hd
  use D
  -- Idea: B ∈ S so (1/2) ∉ B. D=B implies (1/2) ∉ D.
  -- Maybe again try to change statement of inclusion_maximal_valuation to:
  -- B is a valuation ring.
  -- have B_no_half : 1/2 ∉ B := hl
  have D_no_half : 1/2 ∉ D.toSubring := by
    rwa[hd]
  exact D_no_half


lemma non_archimedean (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] (K : Type) [Field K] (v : Valuation K Γ₀) :
  (∀(x y : K), v x ≠ v y → v (x + y) = max (v x) (v y)) := by
  intro x y h
  sorry


-- There is a valuation v on ℝ such that v(1/2) > 1.
theorem valuation_on_reals : ∃(Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀)
  (v : Valuation ℝ Γ₀), (v (1/2)) > 1 := by
    have h := valuation_ring_no_half
    cases' h with B h
    use B.ValueGroup, inferInstance, B.valuation
    have g := valuation_le_one_iff B (1/2)
    rw[← not_iff_not] at g
    rwa[gt_iff_lt, ← not_le, g]
