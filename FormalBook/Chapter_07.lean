/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
/-!
# The spectral theorem and Hadamard's determinant problem

Formalization of the chapter "The spectral theorem and Hadamard's determinant problem".

## Main results
  - `Theorem₁`: the spectral theorem for real symmetric matrices (orthogonal diagonalization).
  - `det_sq_le`, `det_sq_le_of_pm_one`: Hadamard's bound `(det M) ^ 2 ≤ n ^ n` for matrices
    with entries of absolute value at most `1` (in particular for `±1` matrices), proved as in
    the book via AM-GM applied to the eigenvalues of `Mᵀ M`.
  - `hadamard_matrix_exists`, `hadamard_det_sq`, `max_det_sq_pow_two`: Hadamard matrices exist
    for all `n = 2 ^ m`, and they attain Hadamard's bound.
  - `sum_det_sq_signMatrices`: the sum of `(det M) ^ 2` over all `±1` matrices is
    `2 ^ (n ^ 2) * n!`, i.e. its average is `n!`.
  - `Theorem₂`: for `n ≥ 2` there is a `±1` matrix with `det M > √(n!)`.
-/

namespace chapter7

open Matrix Equiv

/-- **Theorem 1** (spectral theorem for real symmetric matrices): every real symmetric matrix
can be diagonalized by an orthogonal matrix. -/
theorem Theorem₁ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : IsHermitian A) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
    Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
    ∃ (d : (Fin n) → ℝ), diagonal d = (Q.conjTranspose * A * Q) := by
  refine ⟨h.eigenvectorUnitary, h.eigenvectorUnitary.2, RCLike.ofReal ∘ h.eigenvalues, ?_⟩
  rw [← h.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_star_apply]
  rfl

/-! ### Hadamard's determinant problem: the upper bound -/

/-- **Hadamard's bound**: if all entries of a real `n × n` matrix `M` satisfy `|M i j| ≤ 1`,
then `(det M) ^ 2 ≤ n ^ n`, i.e. `|det M| ≤ n ^ (n / 2)`. As in the book, the proof applies
the AM-GM inequality to the (nonnegative) eigenvalues of `Mᵀ M`. -/
theorem det_sq_le (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, |M i j| ≤ 1) :
    M.det ^ 2 ≤ (n : ℝ) ^ n := by
  have hA := posSemidef_conjTranspose_mul_self M
  set A := Mᴴ * M
  have hdet : A.det = M.det ^ 2 := by
    simp [A, det_mul, sq, conjTranspose_eq_transpose_of_trivial]
  have htr : A.trace ≤ n * n := by
    simp only [A, trace, diag, mul_apply, conjTranspose_apply, star_trivial]
    calc ∑ i, ∑ j, M j i * M j i ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
          gcongr with i _ j _
          nlinarith [abs_le.1 (hM j i), abs_nonneg (M j i), sq_abs (M j i)]
      _ = n * n := by simp
  rw [← hdet, hA.1.det_eq_prod_eigenvalues]
  rw [hA.1.trace_eq_sum_eigenvalues] at htr
  simp only [RCLike.ofReal_real_eq_id, id] at htr ⊢
  set z := hA.1.eigenvalues
  have hz : ∀ i, 0 ≤ z i := hA.eigenvalues_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have amgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 / n : ℝ)) z
    (fun _ _ => by positivity) (by simp; field_simp) (fun i _ => hz i)
  rw [← Finset.mul_sum, Real.finsetProd_rpow _ _ (fun i _ => hz i)] at amgm
  have h1 : (∏ i, z i) ^ (1 / n : ℝ) ≤ n := by
    refine amgm.trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hnR]; exact htr
  have h0 : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  calc ∏ i, z i = ((∏ i, z i) ^ (1 / n : ℝ)) ^ n := by
        rw [one_div, Real.rpow_inv_natCast_pow h0 hn.ne']
    _ ≤ (n : ℝ) ^ n := by gcongr

/-- Hadamard's bound for `±1` matrices: `(det M) ^ 2 ≤ n ^ n`. -/
theorem det_sq_le_of_pm_one (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, M i j = -1 ∨ M i j = 1) : M.det ^ 2 ≤ (n : ℤ) ^ n := by
  have h := det_sq_le n (M.map (Int.cast : ℤ → ℝ)) fun i j => by
    rcases hM i j with h | h <;> simp [h]
  have e : ((M.det : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)).det :=
    (Int.castRingHom ℝ).map_det M
  rw [← e] at h
  exact_mod_cast h

/-! ### Hadamard matrices exist for all `n = 2 ^ m` (Sylvester's construction) -/

/-- Sylvester's Hadamard matrix of size `2 ^ m`, indexed by `Fin m → Bool`:
the entry at `(x, y)` is `(-1) ^ #{k | x k ∧ y k}`. -/
def sylvester (m : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) ℤ :=
  of fun x y => ∏ k, (if x k && y k then -1 else 1)

lemma sylvester_mul_transpose (m : ℕ) :
    sylvester m * (sylvester m)ᵀ = (2 ^ m : ℤ) • (1 : Matrix _ _ ℤ) := by
  ext x z
  simp only [mul_apply, transpose_apply, sylvester, of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum
    (fun k b => (if x k && b then (-1 : ℤ) else 1) * (if z k && b then -1 else 1))]
  have : ∀ k, ∑ b : Bool, (if x k && b then (-1 : ℤ) else 1) * (if z k && b then -1 else 1)
      = if x k = z k then 2 else 0 := by
    intro k; cases x k <;> cases z k <;> simp
  simp_rw [this]
  by_cases h : x = z
  · subst h; simp
  · obtain ⟨k, hk⟩ : ∃ k, x k ≠ z k := by
      by_contra hc; push Not at hc; exact h (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
    simp [h]

lemma pm_one_sylvester (m : ℕ) (x y) : sylvester m x y = -1 ∨ sylvester m x y = 1 := by
  simp only [sylvester, of_apply]
  refine Finset.prod_induction _ (fun a : ℤ => a = -1 ∨ a = 1) ?_ (Or.inr rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · intro k _; split_ifs <;> simp

/-- **Hadamard matrices exist for all `n = 2 ^ m`**: there is a `2 ^ m × 2 ^ m` matrix `H`
with entries `±1` and `H * Hᵀ = 2 ^ m • 1`. -/
theorem hadamard_matrix_exists (m : ℕ) : ∃ H : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℤ,
    (∀ i j, H i j = -1 ∨ H i j = 1) ∧ H * Hᵀ = (2 ^ m : ℤ) • (1 : Matrix _ _ ℤ) := by
  let e : (Fin m → Bool) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨reindex e e (sylvester m), fun i j => pm_one_sylvester m _ _, ?_⟩
  rw [transpose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv,
    sylvester_mul_transpose]
  ext i j
  rw [submatrix_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply, one_apply]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (e.symm.injective.ne h)]

/-- A Hadamard matrix attains Hadamard's bound: `(det H) ^ 2 = n ^ n` for `n = 2 ^ m`. -/
theorem hadamard_det_sq (m : ℕ) (H : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℤ)
    (hH : H * Hᵀ = (2 ^ m : ℤ) • (1 : Matrix _ _ ℤ)) :
    H.det ^ 2 = ((2 ^ m) ^ (2 ^ m) : ℤ) := by
  have := congrArg det hH
  rwa [det_mul, det_transpose, det_smul, det_one, Fintype.card_fin, mul_one, ← sq] at this

/-- Consequently, for `n = 2 ^ m` the maximal value of `(det M) ^ 2` over `±1` matrices is
exactly `n ^ n`. -/
theorem max_det_sq_pow_two (m : ℕ) :
    (∃ H : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℤ, (∀ i j, H i j = -1 ∨ H i j = 1) ∧
      H.det ^ 2 = ((2 ^ m : ℕ) : ℤ) ^ (2 ^ m)) ∧
    ∀ M : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℤ, (∀ i j, M i j = -1 ∨ M i j = 1) →
      M.det ^ 2 ≤ ((2 ^ m : ℕ) : ℤ) ^ (2 ^ m) := by
  refine ⟨?_, fun M hM => det_sq_le_of_pm_one _ M hM⟩
  obtain ⟨H, h1, h2⟩ := hadamard_matrix_exists m
  exact ⟨H, h1, by rw [hadamard_det_sq m H h2]; push_cast; rfl⟩

/-! ### Theorem 2: a lower bound via averaging -/

/-- The finite set of all `n × n` matrices with entries `±1`. -/
abbrev signMatrices (n : ℕ) : Finset (Matrix (Fin n) (Fin n) ℤ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => ({-1, 1} : Finset ℤ)

lemma mem_signMatrices {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} :
    M ∈ signMatrices n ↔ ∀ i j, M i j = -1 ∨ M i j = 1 :=
  Fintype.mem_piFinset.trans (forall_congr' fun _ => Fintype.mem_piFinset.trans (by simp))

/-- The "independence" computation: summing the product of the entries
`M (σ i) i * M (τ i) i` over all `±1` matrices gives zero unless `σ = τ`. -/
lemma sum_prod_signMatrices {n : ℕ} (σ τ : Perm (Fin n)) :
    ∑ M ∈ signMatrices n, ∏ i, (M (σ i) i * M (τ i) i) =
      if σ = τ then ((signMatrices n).card : ℤ) else 0 := by
  split_ifs with h
  · subst h
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [mem_signMatrices] at hM
    simp only [Nat.cast_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases hM (σ i) i with h | h <;> simp [h]
  · obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
      by_contra hc
      push Not at hc
      exact h (Equiv.ext hc)
    -- flipping the sign of the entry `(σ i, i)` is a sign-reversing involution
    let flip : Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ :=
      fun M a b => if a = σ i ∧ b = i then -M a b else M a b
    have hflip : ∀ M, flip (flip M) = M := by
      intro M; ext a b; simp only [flip]; split_ifs <;> simp
    have hmem : ∀ M ∈ signMatrices n, flip M ∈ signMatrices n := by
      intro M hM
      rw [mem_signMatrices] at hM ⊢
      intro a b
      simp only [flip]
      split_ifs
      · rcases hM a b with h | h <;> simp [h]
      · exact hM a b
    have hneg : ∀ M, ∏ j, (flip M (σ j) j * flip M (τ j) j) =
        -∏ j, (M (σ j) j * M (τ j) j) := by
      intro M
      have : ∀ j, flip M (σ j) j * flip M (τ j) j =
          (if j = i then -1 else 1) * (M (σ j) j * M (τ j) j) := by
        intro j
        simp only [flip]
        by_cases hj : j = i
        · subst hj
          simp [hi.symm]
        · simp [hj]
      rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_mul_distrib,
        Finset.prod_ite_eq' Finset.univ i]
      simp
    have key : ∑ M ∈ signMatrices n, ∏ j, (M (σ j) j * M (τ j) j) =
        ∑ M ∈ signMatrices n, ∏ j, (flip M (σ j) j * flip M (τ j) j) :=
      (Finset.sum_nbij' flip flip hmem hmem (fun M _ => hflip M) (fun M _ => hflip M)
        (fun M _ => rfl)).symm
    simp only [hneg, Finset.sum_neg_distrib] at key
    linarith

/-- The average of `det M ^ 2` over all `±1` matrices `M` is `n!`. -/
theorem sum_det_sq_signMatrices (n : ℕ) :
    ∑ M ∈ signMatrices n, M.det ^ 2 = ((signMatrices n).card : ℤ) * n.factorial := by
  have : ∀ M : Matrix (Fin n) (Fin n) ℤ,
      M.det ^ 2 = ∑ σ : Perm (Fin n), ∑ τ : Perm (Fin n),
      ((Perm.sign σ * Perm.sign τ : ℤˣ) : ℤ) * ∏ i, (M (σ i) i * M (τ i) i) := by
    intro M
    rw [sq, det_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, Finset.prod_mul_distrib]
    push_cast; ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := signMatrices n), ← Finset.mul_sum, sum_prod_signMatrices]
  simp [Fintype.card_perm, mul_comm]

/-- **Theorem 2**: for `n ≥ 2` there is an `n × n` matrix with entries `±1` whose determinant
exceeds `√(n!)`. -/
theorem Theorem₂ (n : ℕ) (hn : 1 < n) : ∃ (M : Matrix (Fin n) (Fin n) ℤ),
    (∀ i j, M i j = -1 ∨ M i j = 1) ∧
    M.det > Real.sqrt n.factorial := by
  -- some `±1` matrix has `det ^ 2 > n!`, since the average of `det ^ 2` is `n!` and the
  -- all-ones matrix is singular
  obtain ⟨M, hM, hdet⟩ : ∃ M ∈ signMatrices n, (n.factorial : ℤ) < M.det ^ 2 := by
    by_contra hc
    push Not at hc
    have hJ : (of fun _ _ => (1 : ℤ)) ∈ signMatrices n :=
      mem_signMatrices.2 fun _ _ => Or.inr rfl
    have hJdet : (of fun (_ : Fin n) (_ : Fin n) => (1 : ℤ)).det = 0 :=
      det_zero_of_row_eq (i := (⟨0, by omega⟩ : Fin n)) (j := ⟨1, hn⟩) (by simp) rfl
    have hlt :
        ∑ M ∈ signMatrices n, M.det ^ 2 < ∑ _M ∈ signMatrices n, (n.factorial : ℤ) :=
      Finset.sum_lt_sum hc ⟨_, hJ, by rw [hJdet]; simpa using n.factorial_pos⟩
    rw [sum_det_sq_signMatrices, Finset.sum_const, nsmul_eq_mul] at hlt
    exact lt_irrefl _ hlt
  rw [mem_signMatrices] at hM
  have key : ∀ N : Matrix (Fin n) (Fin n) ℤ,
      (n.factorial : ℤ) < N.det ^ 2 → 0 < N.det → (N.det : ℝ) > Real.sqrt n.factorial := by
    intro N h1 h2
    rw [gt_iff_lt, Real.sqrt_lt' (by exact_mod_cast h2)]
    exact_mod_cast h1
  rcases lt_trichotomy M.det 0 with h | h | h
  · -- negate the first row to make the determinant positive
    let i₀ : Fin n := ⟨0, by omega⟩
    have hd : (M.updateRow i₀ (-M i₀)).det = -M.det := by
      rw [show -M i₀ = (-1 : ℤ) • M i₀ by simp, det_updateRow_smul, updateRow_eq_self]; ring
    refine ⟨M.updateRow i₀ (-M i₀), fun i j => ?_, key _ ?_ ?_⟩
    · by_cases hi : i = i₀
      · subst hi; rcases hM i₀ j with h | h <;> simp [h]
      · simpa [updateRow_ne hi] using hM i j
    · rw [hd, neg_sq]; exact hdet
    · rw [hd]; omega
  · rw [h] at hdet; simp at hdet; exact absurd hdet (not_lt.2 (Nat.cast_nonneg _))
  · exact ⟨M, hM, key M hdet h⟩

end chapter7
