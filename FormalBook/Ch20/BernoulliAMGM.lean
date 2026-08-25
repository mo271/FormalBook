import Mathlib

open Real
open BigOperators
open Classical

/-! ### Bernoulli induction AM-GM helpers for Proof ₃ -/

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Key step for AM-GM induction: Bernoulli's inequality gives
    ((S + a)/(n+1))^(n+1) ≥ (S/n)^n · a for positive S, a. -/
lemma bernoulli_amgm_step (n : ℕ) (hn : 0 < n)
    (S a_last : ℝ) (hS : 0 < S) (ha : 0 < a_last) :
    ((S + a_last) / (↑n + 1)) ^ (n + 1) ≥ (S / ↑n) ^ n * a_last := by
  have hm : (0 : ℝ) < ↑n + 1 := by positivity
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hSn : 0 < S / ↑n := div_pos hS hn_pos
  set r := (S + a_last) / (↑n + 1) / (S / ↑n) with hr_def
  have hr_pos : 0 < r := by positivity
  have h_eq : (S + a_last) / (↑n + 1) = (S / ↑n) * r := by
    rw [hr_def, mul_div_cancel₀ _ (ne_of_gt hSn)]
  have h_alg : (S / ↑n) * (1 + (↑n + 1) * (r - 1)) = a_last := by
    rw [hr_def]; field_simp; ring
  have bernoulli : 1 + (↑n + 1) * (r - 1) ≤ r ^ (n + 1) := by
    have h2 := one_add_mul_le_pow (show (-2 : ℝ) ≤ r - 1 by linarith) (n + 1)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel] at h2; exact h2
  rw [h_eq]
  calc (S / ↑n * r) ^ (n + 1)
      = (S / ↑n) ^ (n + 1) * r ^ (n + 1) := mul_pow _ _ _
    _ ≥ (S / ↑n) ^ (n + 1) * (1 + (↑n + 1) * (r - 1)) := by gcongr
    _ = (S / ↑n) ^ n * ((S / ↑n) * (1 + (↑n + 1) * (r - 1))) := by rw [pow_succ]; ring
    _ = (S / ↑n) ^ n * a_last := by rw [h_alg]

set_option maxHeartbeats 3200000 in
set_option linter.unusedSimpArgs false in
/-- AM-GM inequality by ordinary induction using Bernoulli's inequality (Hirschhorn's proof). -/
lemma amgm_bernoulli (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (hpos : ∀ i, 0 < a i) :
    ∏ i, a i ≤ ((∑ i, a i) / n) ^ n := by
  induction n with
  | zero => omega
  | succ k ihk =>
    by_cases hk : k = 0
    · subst hk; simp [Fin.prod_univ_one, Fin.sum_univ_one]
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      set S := ∑ i : Fin k, a (Fin.castSucc i)
      set a_last := a (Fin.last k)
      have hS : 0 < S := Finset.sum_pos (fun i _ => hpos _) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      have ha_last : 0 < a_last := hpos _
      have ih := ihk hk_pos (fun i => a (Fin.castSucc i)) (fun i => hpos _)
      have step := bernoulli_amgm_step k hk_pos S a_last hS ha_last
      calc (∏ i : Fin k, a (Fin.castSucc i)) * a_last
          ≤ (S / ↑k) ^ k * a_last := by gcongr
        _ ≤ ((S + a_last) / (↑k + 1)) ^ (k + 1) := step
        _ = ((S + a_last) / ↑(k + 1)) ^ (k + 1) := by norm_cast

set_option maxHeartbeats 3200000 in
/-- AM-GM for general Fintype, via Bernoulli induction. -/
lemma amgm_bernoulli_fintype {α : Type*} [Fintype α]
    (hcard : 0 < Fintype.card α)
    (a : α → ℝ) (hpos : ∀ i, 0 < a i) :
    ∏ i, a i ≤ ((∑ i, a i) / Fintype.card α) ^ Fintype.card α := by
  set n := Fintype.card α
  set e := Fintype.equivFin α
  have h1 : ∏ i, a i = ∏ i : Fin n, a (e.symm i) := by
    rw [← Finset.prod_equiv e.symm (s := Finset.univ) (t := Finset.univ)] <;> simp
  have h2 : ∑ i, a i = ∑ i : Fin n, a (e.symm i) := by
    rw [← Finset.sum_equiv e.symm (s := Finset.univ) (t := Finset.univ)] <;> simp
  rw [h1, h2]
  exact amgm_bernoulli n hcard (fun i => a (e.symm i)) (fun i => hpos _)

