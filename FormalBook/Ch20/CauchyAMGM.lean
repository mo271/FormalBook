import FormalBook.Mathlib.EdgeFinset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real
open BigOperators
open Classical

/-! ### Cauchy forward-backward AM-GM helpers for Proof ₁ -/

lemma cauchy_amgm_base (a b : ℝ) :
    a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]

/-- The Cauchy AM-GM induction predicate: for n values, the product is at most (sum/n)^n. -/
def CauchyAMGM (n : ℕ) : Prop :=
  ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) → ∏ i, a i ≤ ((∑ i, a i) / n) ^ n

lemma cauchy_amgm_two : CauchyAMGM 2 := by
  intro a _; simp only [Fin.prod_univ_two, Fin.sum_univ_two]; exact cauchy_amgm_base _ _

set_option maxHeartbeats 800000 in
lemma cauchy_amgm_doubling (n : ℕ) (hn : 0 < n) (h : CauchyAMGM n) :
    CauchyAMGM (n + n) := by
  intro a hpos
  set S₁ := ∑ i : Fin n, a (Fin.castAdd n i)
  set S₂ := ∑ i : Fin n, a (Fin.natAdd n i)
  have hS₁ : 0 ≤ S₁ := Finset.sum_nonneg fun i _ => hpos _
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => hpos _
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 := h (fun i => a (Fin.castAdd n i)) (fun i => hpos _)
  have h2 := h (fun i => a (Fin.natAdd n i)) (fun i => hpos _)
  have hnn : (↑(n + n) : ℝ) = ↑n + ↑n := by push_cast; ring
  rw [hnn]
  calc ∏ i : Fin (n + n), a i
      = (∏ i : Fin n, a (Fin.castAdd n i)) * (∏ i : Fin n, a (Fin.natAdd n i)) :=
        Fin.prod_univ_add a
    _ ≤ (S₁ / n) ^ n * (S₂ / n) ^ n :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => hpos _)
          (pow_nonneg (div_nonneg hS₁ hn_pos.le) _)
    _ = (S₁ / n * (S₂ / n)) ^ n := (mul_pow _ _ _).symm
    _ ≤ (((S₁ + S₂) / (↑n + ↑n)) ^ 2) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        calc S₁ / ↑n * (S₂ / ↑n)
            ≤ ((S₁ / ↑n + S₂ / ↑n) / 2) ^ 2 := cauchy_amgm_base _ _
          _ = ((S₁ + S₂) / (↑n + ↑n)) ^ 2 := by field_simp; ring
    _ = ((S₁ + S₂) / (↑n + ↑n)) ^ (n + n) := by rw [← pow_mul]; congr 1; omega
    _ = ((∑ i, a i) / (↑n + ↑n)) ^ (n + n) := by
        congr 2; exact (Fin.sum_univ_add a).symm

lemma cauchy_amgm_pow2 : ∀ k : ℕ, 0 < k → CauchyAMGM (2 ^ k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ihk =>
    by_cases hk0 : k = 0
    · subst hk0; exact cauchy_amgm_two
    · have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
      rw [this]; exact cauchy_amgm_doubling _ (by positivity) (ihk (by omega))

set_option maxHeartbeats 1600000 in
lemma cauchy_amgm_backward (n : ℕ) (hn : 0 < n) (h : CauchyAMGM (n + 1)) :
    CauchyAMGM n := by
  intro a hpos
  set A := (∑ i, a i) / ↑n with hA_def
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA_nn : 0 ≤ A := div_nonneg (Finset.sum_nonneg fun i _ => hpos i) hn_pos.le
  set a' : Fin (n + 1) → ℝ := Fin.snoc a A with ha'_def
  have ha'_pos : ∀ i, 0 ≤ a' i := by
    intro i; simp only [ha'_def, Fin.snoc]; split <;> [exact hpos _; exact hA_nn]
  have key := h a' ha'_pos
  have hsum_a' : ∑ i : Fin (n + 1), a' i = (∑ i : Fin n, a i) + A := by
    rw [Fin.sum_univ_castSucc]; simp [ha'_def]
  have hprod_a' : ∏ i : Fin (n + 1), a' i = (∏ i : Fin n, a i) * A := by
    rw [Fin.prod_univ_castSucc]; simp [ha'_def]
  have hsum_eq : (∑ i : Fin n, a i) + A = (↑n + 1) * A := by rw [hA_def]; field_simp
  have hcast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
  rw [hsum_a', hprod_a', hsum_eq, hcast] at key
  rw [mul_div_cancel_left₀ A (by positivity : (↑n + (1 : ℝ)) ≠ 0), pow_succ] at key
  by_cases hA0 : A = 0
  · have hsum0 : ∑ j : Fin n, a j = 0 := by
      rw [hA_def] at hA0; exact (div_eq_zero_iff.mp hA0).resolve_right (ne_of_gt hn_pos)
    have hzero : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos j)).mp hsum0 i (Finset.mem_univ _)
    simp only [hzero, Finset.prod_const]
    rw [hA0]; simp [Fintype.card_fin, zero_pow (by omega : n ≠ 0)]
  · exact le_of_mul_le_mul_right key (lt_of_le_of_ne hA_nn (Ne.symm hA0))

lemma cauchy_amgm_backward_iter (d n : ℕ) (hn : 0 < n) (h : CauchyAMGM (n + d)) :
    CauchyAMGM n := by
  induction d with
  | zero => exact h
  | succ d ihd =>
    apply ihd
    exact cauchy_amgm_backward (n + d) (by omega) (by convert h using 1)

/-- **Cauchy's AM-GM inequality**: for n ≥ 1 and nonneg reals, ∏aᵢ ≤ (∑aᵢ/n)ⁿ.
    Proved by forward doubling P(2)→P(4)→...→P(2^k), then backward P(2^k)→...→P(n). -/
lemma cauchy_amgm (n : ℕ) (hn : 0 < n) : CauchyAMGM n := by
  obtain ⟨k, hk, hkn⟩ : ∃ k, 0 < k ∧ n ≤ 2 ^ k :=
    ⟨n, by omega, Nat.lt_two_pow_self.le⟩
  exact cauchy_amgm_backward_iter (2 ^ k - n) n hn
    (by convert cauchy_amgm_pow2 k hk using 1; omega)

set_option maxHeartbeats 1600000 in
lemma cauchy_amgm_fintype {α : Type*} [Fintype α]
    (hcard : 0 < Fintype.card α)
    (a : α → ℝ) (hpos : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ((∑ i, a i) / Fintype.card α) ^ Fintype.card α := by
  set n := Fintype.card α
  set e := Fintype.equivFin α
  have h1 : ∏ i, a i = ∏ i : Fin n, a (e.symm i) := by
    rw [← Finset.prod_equiv e.symm (s := Finset.univ) (t := Finset.univ)] <;> simp
  have h2 : ∑ i, a i = ∑ i : Fin n, a (e.symm i) := by
    rw [← Finset.sum_equiv e.symm (s := Finset.univ) (t := Finset.univ)] <;> simp
  rw [h1, h2]
  exact cauchy_amgm n hcard (fun i => a (e.symm i)) (fun i => hpos _)

set_option maxHeartbeats 800000 in
lemma cauchy_amgm_rpow {n : ℕ} (hn : 0 < n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ n) :
    x ^ ((1 : ℝ) / n) ≤ y := by
  calc x ^ ((1 : ℝ) / n)
      ≤ (y ^ n) ^ ((1 : ℝ) / n) := rpow_le_rpow hx h (by positivity)
    _ = y := by
        rw [← rpow_natCast y n, ← rpow_mul hy]
        simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]


