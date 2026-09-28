/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, AItoBit
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Auxiliary results for Erdős' theorem on binomial coefficients

This file contains the ingredients of the proof (following *Proofs from THE BOOK*) that
`choose n k = m ^ l` has no solutions with `l ≥ 2` and `4 ≤ k ≤ n - 4`:

* every factor `n - j` (`j < k`) is written as `n - j = a_j * m_j ^ l` where `a_j` is `l`-th
  power free (`freePart`, `powPart`);
* the `a_j` are pairwise distinct (`free_ne`);
* their product divides `k !` (`sum_mod_le_factorial`), hence they are exactly `1, …, k`
  (`eq_Icc_of_prod_le`);
* the final contradiction for `l = 2` (`4` is a square) and `l ≥ 3` (`final_l3`).
-/

namespace chapter3.Erdos

open Nat Finset

/-! ### Splitting off `l`-th powers -/

/-- The `l`-th power free part of `x`: the exponent of every prime is reduced modulo `l`. -/
noncomputable def freePart (l x : ℕ) : ℕ :=
  (Finsupp.mapRange (fun e => e % l) (Nat.zero_mod l) x.factorization).prod (· ^ ·)

/-- The part of `x` which is an `l`-th power, so that `x = freePart l x * powPart l x ^ l`. -/
noncomputable def powPart (l x : ℕ) : ℕ :=
  (Finsupp.mapRange (fun e => e / l) (Nat.zero_div l) x.factorization).prod (· ^ ·)

theorem factorization_freePart (l x : ℕ) :
    (freePart l x).factorization =
      Finsupp.mapRange (fun e => e % l) (Nat.zero_mod l) x.factorization := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)

theorem factorization_powPart (l x : ℕ) :
    (powPart l x).factorization =
      Finsupp.mapRange (fun e => e / l) (Nat.zero_div l) x.factorization := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)

theorem freePart_factorization_apply (l x p : ℕ) :
    (freePart l x).factorization p = x.factorization p % l := by
  rw [factorization_freePart]; rfl

theorem freePart_ne_zero (l x : ℕ) : freePart l x ≠ 0 := by
  unfold freePart
  rw [Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply pow_ne_zero
  exact (Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)).ne_zero

theorem powPart_ne_zero (l x : ℕ) : powPart l x ≠ 0 := by
  unfold powPart
  rw [Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply pow_ne_zero
  exact (Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)).ne_zero

theorem freePart_mul_powPart (l x : ℕ) (hx : x ≠ 0) : freePart l x * powPart l x ^ l = x := by
  apply Nat.eq_of_factorization_eq
  · exact mul_ne_zero (freePart_ne_zero l x) (pow_ne_zero _ (powPart_ne_zero l x))
  · exact hx
  intro p
  rw [Nat.factorization_mul (freePart_ne_zero l x) (pow_ne_zero _ (powPart_ne_zero l x)),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, factorization_freePart,
    factorization_powPart]
  simp only [Finsupp.mapRange_apply, smul_eq_mul]
  exact Nat.mod_add_div _ _

/-! ### The product of the `l`-th power free parts divides `k !` -/

/-- Among `k` consecutive numbers `n - k + 1, …, n` there are at most `k / d + 1` multiples
of `d`. -/
theorem card_multiples_window (n k d : ℕ) (hd : 0 < d) (hkn : k ≤ n) :
    #{j ∈ range k | d ∣ n - j} ≤ k / d + 1 := by
  have h1 : #{j ∈ range k | d ∣ n - j} ≤ #(Ioc ((n - k) / d) (n / d)) := by
    apply card_le_card_of_injOn (fun j => (n - j) / d)
    · intro j hj
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj
      simp only [coe_Ioc, Set.mem_Ioc]
      obtain ⟨hj, t, ht⟩ := hj
      rw [ht, Nat.mul_div_cancel_left _ hd]
      constructor
      · rw [Nat.div_lt_iff_lt_mul hd]; rw [mul_comm]; omega
      · rw [Nat.le_div_iff_mul_le hd, mul_comm]; omega
    · intro i hi j hj hij
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
      obtain ⟨hi, t, ht⟩ := hi
      obtain ⟨hj, u, hu⟩ := hj
      simp only [ht, hu, Nat.mul_div_cancel_left _ hd] at hij
      subst hij
      omega
  rw [Nat.card_Ioc] at h1
  have h2 : n / d < (n - k) / d + k / d + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    obtain ⟨a, ha⟩ : ∃ a, a = n - k := ⟨_, rfl⟩
    have hn : n = a + k := by omega
    rw [← ha, hn]
    have := Nat.div_add_mod a d
    have := Nat.div_add_mod k d
    have := Nat.mod_lt a hd
    have := Nat.mod_lt k hd
    nlinarith
  generalize n / d = A at h1 h2
  generalize (n - k) / d = B at h1 h2
  generalize k / d = C at h1 h2 ⊢
  omega

theorem sum_factorization_sub (n k p m l : ℕ) (hkn : k ≤ n)
    (hdesc : n.descFactorial k = k ! * m ^ l) :
    ∑ j ∈ range k, (n - j).factorization p = (k !).factorization p + l * m.factorization p := by
  have hne : ∀ j ∈ range k, n - j ≠ 0 := by intro j hj; simp at hj; omega
  have hml : m ^ l ≠ 0 := by
    intro h0
    rw [h0, mul_zero, descFactorial_eq_prod_range] at hdesc
    exact prod_ne_zero_iff.mpr hne hdesc
  have : (n.descFactorial k).factorization p = (k ! * m ^ l).factorization p := by rw [hdesc]
  rw [descFactorial_eq_prod_range, Nat.factorization_prod hne, Finsupp.coe_finsetSum,
    Finset.sum_apply, Nat.factorization_mul (factorial_ne_zero k) hml,
    Nat.factorization_pow] at this
  simpa using this

theorem mod_le_card_dvd (x p l : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hl : 1 ≤ l) :
    x.factorization p % l ≤ #{i ∈ Ico 1 l | p ^ i ∣ x} := by
  have : {i ∈ Ico 1 l | p ^ i ∣ x} = Ico 1 (min (x.factorization p + 1) l) := by
    ext i
    simp only [mem_filter, mem_Ico, hp.pow_dvd_iff_le_factorization hx]
    omega
  rw [this, Nat.card_Ico]
  have := Nat.mod_le (x.factorization p) l
  have := Nat.mod_lt (x.factorization p) (show 0 < l by omega)
  omega

theorem sum_mod_le (n k p l : ℕ) (hp : p.Prime) (hl : 1 ≤ l) (hkn : k ≤ n) :
    ∑ j ∈ range k, (n - j).factorization p % l ≤ ∑ i ∈ Ico 1 l, (k / p ^ i + 1) := by
  calc ∑ j ∈ range k, (n - j).factorization p % l
      ≤ ∑ j ∈ range k, #{i ∈ Ico 1 l | p ^ i ∣ n - j} := by
        apply sum_le_sum; intro j hj; simp at hj
        exact mod_le_card_dvd _ _ _ hp (by omega) hl
    _ = ∑ i ∈ Ico 1 l, #{j ∈ range k | p ^ i ∣ n - j} := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ _ := by
        apply sum_le_sum; intro i _
        exact card_multiples_window n k (p ^ i) (pow_pos hp.pos _) hkn

/-- The exponent of `p` in the product of the `l`-th power free parts of `n, …, n - k + 1`
is at most the exponent of `p` in `k !`, provided `n (n - 1) ⋯ (n - k + 1) = k ! * m ^ l`. -/
theorem sum_mod_le_factorial (n k p m l : ℕ) (hp : p.Prime) (hl : 1 ≤ l) (hkn : k ≤ n)
    (hdesc : n.descFactorial k = k ! * m ^ l) :
    ∑ j ∈ range k, (n - j).factorization p % l ≤ (k !).factorization p := by
  have h1 := sum_factorization_sub n k p m l hkn hdesc
  have h2 := sum_mod_le n k p l hp hl hkn
  have hF : (k !).factorization p = ∑ i ∈ Ico 1 (l + k), k / p ^ i :=
    Nat.factorization_factorial hp (by
      have := Nat.log_le_self p k
      omega)
  have h3 : ∑ i ∈ Ico 1 l, (k / p ^ i + 1) ≤ (k !).factorization p + (l - 1) := by
    rw [sum_add_distrib, hF]
    simp only [sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
    have : ∑ i ∈ Ico 1 l, k / p ^ i ≤ ∑ i ∈ Ico 1 (l + k), k / p ^ i :=
      sum_le_sum_of_subset (Ico_subset_Ico_right (by omega))
    omega
  have h4 : ∑ j ∈ range k, (n - j).factorization p =
      ∑ j ∈ range k, (n - j).factorization p % l +
        l * ∑ j ∈ range k, (n - j).factorization p / l := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => (Nat.mod_add_div _ _).symm
  set X := ∑ j ∈ range k, (n - j).factorization p % l
  set Y := ∑ j ∈ range k, (n - j).factorization p / l
  set F := (k !).factorization p
  set M := m.factorization p
  have hXY : X + l * Y = F + l * M := by rw [← h4, h1]
  rcases le_or_gt M Y with h | h
  · have : l * M ≤ l * Y := Nat.mul_le_mul_left _ h
    omega
  · have : l * (Y + 1) ≤ l * M := Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

/-! ### `k` distinct positive integers with product at most `k !` are `1, …, k` -/

theorem card_le_max (S : Finset ℕ) (hS : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x) :
    #S ≤ S.max' hS := by
  calc #S ≤ #(Icc 1 (S.max' hS)) := card_le_card fun x hx =>
        mem_Icc.mpr ⟨hpos x hx, le_max' S x hx⟩
    _ = S.max' hS := by simp

theorem factorial_le_prod : ∀ (k : ℕ) (S : Finset ℕ), #S = k → (∀ x ∈ S, 0 < x) →
    k ! ≤ ∏ x ∈ S, x := by
  intro k
  induction k with
  | zero => intro S hS _; rw [Finset.card_eq_zero] at hS; simp [hS]
  | succ k ih =>
    intro S hS hpos
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    set M := S.max' hne
    have hM : M ∈ S := max'_mem S hne
    have hMk : k + 1 ≤ M := hS ▸ card_le_max S hne hpos
    have h1 := ih (S.erase M) (by rw [card_erase_of_mem hM]; omega)
      (fun x hx => hpos x (mem_of_mem_erase hx))
    rw [← mul_prod_erase S _ hM, factorial_succ]
    exact Nat.mul_le_mul hMk h1

theorem eq_Icc_of_prod_le : ∀ (k : ℕ) (S : Finset ℕ), #S = k → (∀ x ∈ S, 0 < x) →
    ∏ x ∈ S, x ≤ k ! → S = Icc 1 k := by
  intro k
  induction k with
  | zero => intro S hS _ _; rw [Finset.card_eq_zero] at hS; simp [hS]
  | succ k ih =>
    intro S hS hpos hprod
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    set M := S.max' hne
    have hM : M ∈ S := max'_mem S hne
    have hMk : k + 1 ≤ M := hS ▸ card_le_max S hne hpos
    have hcard : #(S.erase M) = k := by rw [card_erase_of_mem hM]; omega
    have hpos' : ∀ x ∈ S.erase M, 0 < x := fun x hx => hpos x (mem_of_mem_erase hx)
    have h1 := factorial_le_prod k (S.erase M) hcard hpos'
    rw [← mul_prod_erase S _ hM, factorial_succ] at hprod
    have hkpos : 0 < k ! := factorial_pos k
    have hMeq : M = k + 1 := by
      by_contra hne'
      have : (k + 2) * k ! ≤ M * ∏ x ∈ S.erase M, x := Nat.mul_le_mul (by omega) h1
      nlinarith
    have h2 : ∏ x ∈ S.erase M, x ≤ k ! := by
      have : (k + 1) * ∏ x ∈ S.erase M, x ≤ (k + 1) * k ! := by
        calc (k + 1) * ∏ x ∈ S.erase M, x = M * ∏ x ∈ S.erase M, x := by rw [hMeq]
          _ ≤ _ := hprod
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have h3 := ih _ hcard hpos' h2
    rw [← insert_erase hM, h3, hMeq]
    ext x; simp only [mem_insert, mem_Icc]; omega

/-! ### The `l`-th power free parts are distinct -/

theorem bernoulli_nat (B L : ℕ) : B ^ (L + 1) + (L + 1) * B ^ L ≤ (B + 1) ^ (L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    calc B ^ (L + 2) + (L + 2) * B ^ (L + 1)
        ≤ (B + 1) * (B ^ (L + 1) + (L + 1) * B ^ L) := by
          ring_nf; nlinarith [Nat.zero_le (B ^ L), Nat.zero_le (L * B ^ L)]
      _ ≤ (B + 1) * (B + 1) ^ (L + 1) := Nat.mul_le_mul_left _ ih
      _ = (B + 1) ^ (L + 2) := by ring

theorem pow_sub_pow_ge (c B l : ℕ) (hl : 1 ≤ l) (hcB : B < c) :
    B ^ l + l * B ^ (l - 1) ≤ c ^ l := by
  obtain ⟨L, rfl⟩ : ∃ L, l = L + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact (bernoulli_nat B L).trans (Nat.pow_le_pow_left hcB _)

/-- If `n - i = a * c ^ l` and `n - j = a * B ^ l` with `i < j < k`, `l ≥ 2`, `n ≥ 2 k` and
`n > k ^ 2`, we get a contradiction. -/
theorem free_ne (n k l i j a c B : ℕ) (hl : 2 ≤ l) (hij : i < j) (hjk : j < k)
    (hn : 2 * k ≤ n) (hk2 : k * k < n) (hi : n - i = a * c ^ l) (hj : n - j = a * B ^ l) :
    False := by
  have hlt : a * B ^ l < a * c ^ l := by rw [← hi, ← hj]; omega
  have hBc : B < c := by
    by_contra h
    have : a * c ^ l ≤ a * B ^ l := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hlt)
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; rw [zero_pow (by omega), mul_zero] at hj; omega
    · exact h
  have h1 := pow_sub_pow_ge c B l (by omega) hBc
  have hdiff : j - i = a * c ^ l - a * B ^ l := by omega
  have h2 : a * (l * B ^ (l - 1)) ≤ j - i := by
    rw [hdiff, ← Nat.mul_sub]
    exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨L, rfl⟩ : ∃ L, l = L + 2 := ⟨l - 2, by omega⟩
  simp only [show L + 2 - 1 = L + 1 by omega] at h2
  have h3 : a * B ^ (L + 2) ≤ a * (B ^ (L + 1)) * (a * B ^ (L + 1)) := by
    have : 1 ≤ a * B ^ L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc a * B ^ (L + 2) = a * B ^ (L + 2) * 1 := by ring
      _ ≤ a * B ^ (L + 2) * (a * B ^ L) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have h4 : (L + 2) * (L + 2) * (n - j) ≤ (j - i) * (j - i) := by
    rw [hj]
    calc (L + 2) * (L + 2) * (a * B ^ (L + 2))
        ≤ (L + 2) * (L + 2) * (a * (B ^ (L + 1)) * (a * B ^ (L + 1))) :=
          Nat.mul_le_mul_left _ h3
      _ = (a * ((L + 2) * B ^ (L + 1))) * (a * ((L + 2) * B ^ (L + 1))) := by ring
      _ ≤ _ := Nat.mul_le_mul h2 h2
  have h5 : (j - i) * (j - i) < k * k := Nat.mul_self_lt_mul_self (by omega)
  have h6 : 4 * (n - j) ≤ (L + 2) * (L + 2) * (n - j) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  omega

/-! ### The final contradiction in the case `l ≥ 3` -/

theorem core_contra (N k c l : ℕ) (hl : 3 ≤ l) (hk : 4 ≤ k) (hkN : k ^ 3 < N)
    (h1 : 4 * l * c ^ (l - 1) + (N - k + 1) ^ 2 ≤ N ^ 2) (h2 : (N - k + 1) ^ 2 ≤ 4 * c ^ l) :
    False := by
  set M := N - k + 1 with hM
  have h16 : 16 * k ≤ k ^ 3 := by
    have : 16 ≤ k * k := by nlinarith
    calc 16 * k ≤ k * k * k := Nat.mul_le_mul_right _ this
      _ = k ^ 3 := by ring
  have hMN : M ≤ N := by omega
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; rw [zero_pow (by omega)] at h2
      have : M = 0 := by nlinarith
      omega
    · exact h
  set D := N ^ 2 - M ^ 2 with hD
  set E := c ^ (l - 1)
  have hE : 12 * E ≤ D := by
    have : 12 * E ≤ 4 * l * E := Nat.mul_le_mul_right _ (by omega)
    omega
  have hcl : (c ^ l) ^ 2 ≤ E ^ 3 := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right hc (by omega)
  have hM4 : M ^ 4 ≤ 16 * E ^ 3 := by
    calc M ^ 4 = (M ^ 2) ^ 2 := by ring
      _ ≤ (4 * c ^ l) ^ 2 := Nat.pow_le_pow_left h2 _
      _ = 16 * (c ^ l) ^ 2 := by ring
      _ ≤ 16 * E ^ 3 := Nat.mul_le_mul_left _ hcl
  have hE3 : 1728 * E ^ 3 ≤ D ^ 3 := by
    calc 1728 * E ^ 3 = (12 * E) ^ 3 := by ring
      _ ≤ D ^ 3 := Nat.pow_le_pow_left hE _
  have hD2 : D ≤ 2 * N * (k - 1) := by
    have hNM : N = M + (k - 1) := by omega
    rw [hD, hNM]
    have : (M + (k - 1)) ^ 2 = M ^ 2 + (2 * M * (k - 1) + (k - 1) ^ 2) := by ring
    rw [this, Nat.add_sub_cancel_left]
    nlinarith
  have hD3 : D ^ 3 ≤ 8 * N ^ 4 := by
    have hk1 : (k - 1) ^ 3 ≤ N := by
      have : (k - 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left (by omega) _
      omega
    calc D ^ 3 ≤ (2 * N * (k - 1)) ^ 3 := Nat.pow_le_pow_left hD2 _
      _ = 8 * N ^ 3 * (k - 1) ^ 3 := by ring
      _ ≤ 8 * N ^ 3 * N := Nat.mul_le_mul_left _ hk1
      _ = 8 * N ^ 4 := by ring
  have h15 : 15 * N ≤ 16 * M := by omega
  have h15' : (15 * N) ^ 4 ≤ (16 * M) ^ 4 := Nat.pow_le_pow_left h15 _
  have hN : 0 < N := by omega
  have hN4 : 0 < N ^ 4 := by positivity
  nlinarith

theorem sq_ne_mul_aux (N k x b y : ℕ) (hk : 2 ≤ k) (hkN : k ^ 3 < N)
    (hx : N - k < x) (hbN : N - k < b) (hy : y ≤ N) (hxy : x < y) (hxb : x ≠ b) (hyb : y ≠ b)
    (h : b * b = x * y) : False := by
  have hk3 : (k - 1) * (k - 1) < N - k + 1 := by
    have : (k - 1) * (k - 1) + k ≤ k ^ 3 := by
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
      rw [show t + 2 - 1 = t + 1 by omega]
      ring_nf; nlinarith
    omega
  have hxb' : x < b := by
    by_contra hc
    have : b * b ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
    have : x * x < x * y := Nat.mul_lt_mul_of_pos_left hxy (by omega)
    omega
  have hby : b < y := by
    by_contra hc
    have : y * y ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
    have : x * y < y * y := Nat.mul_lt_mul_of_pos_right hxy (by omega)
    omega
  have hz : (b : ℤ) * b = x * y := by exact_mod_cast h
  have hid : (b : ℤ) * ((y - b) - (b - x)) = (b - x) * (y - b) := by linear_combination -hz
  have hpos : (0 : ℤ) < (b - x) * (y - b) := by
    apply mul_pos <;> omega
  have hd : (0 : ℤ) < (y - b) - (b - x) := by
    by_contra hc
    push_neg at hc
    have : (b : ℤ) * ((y - b) - (b - x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have h1 : (b : ℤ) ≤ (b - x) * (y - b) := by nlinarith
  have h2 : ((b : ℤ) - x) * (y - b) ≤ ((k : ℤ) - 1) * (k - 1) := by
    apply mul_le_mul <;> omega
  have hk3' : ((k : ℤ) - 1) * (k - 1) < N - k + 1 := by
    have := hk3
    zify [show 1 ≤ k by omega, show k ≤ N by nlinarith] at this
    linarith
  omega

/-- If `x, b, y` are among `N - k + 1, …, N` with `N > k ^ 3`, and `b ≠ x`, `b ≠ y`, then
`b ^ 2 ≠ x * y`. -/
theorem sq_ne_mul (N k x b y : ℕ) (hk : 2 ≤ k) (hkN : k ^ 3 < N)
    (hx : N - k < x) (hx' : x ≤ N) (hbN : N - k < b) (hy : N - k < y) (hy' : y ≤ N)
    (hxb : x ≠ b) (hyb : y ≠ b) : b * b ≠ x * y := by
  intro h
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact sq_ne_mul_aux N k x b y hk hkN hx hbN hy' hxy hxb hyb h
  · have : b = x := by nlinarith
    exact hxb this.symm
  · exact sq_ne_mul_aux N k y b x hk hkN hy hbN hx' hxy hyb hxb (by rw [h, mul_comm])

/-- There are no three numbers `x = B1 ^ l`, `b = 2 * B2 ^ l`, `y = 4 * B3 ^ l` among
`N - k + 1, …, N` if `l ≥ 3`, `k ≥ 4` and `N > k ^ 3`. -/
theorem final_l3 (N k l x b y B1 B2 B3 : ℕ) (hl : 3 ≤ l) (hk : 4 ≤ k) (hkN : k ^ 3 < N)
    (hx : N - k < x) (hx' : x ≤ N) (hb : N - k < b) (hb' : b ≤ N) (hy : N - k < y)
    (hy' : y ≤ N) (hxb : x ≠ b) (hyb : y ≠ b)
    (ex : x = B1 ^ l) (eb : b = 2 * B2 ^ l) (ey : y = 4 * B3 ^ l) : False := by
  have hne := sq_ne_mul N k x b y (by omega) hkN hx hx' hb hy hy' hxb hyb
  have ebb : b * b = 4 * (B2 ^ 2) ^ l := by rw [eb, ← pow_mul, mul_comm 2 l, pow_mul]; ring
  have exy : x * y = 4 * (B1 * B3) ^ l := by rw [ex, ey, mul_pow]; ring
  have hM : (N - k + 1) ^ 2 ≤ b * b := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hM' : (N - k + 1) ^ 2 ≤ x * y := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hN : b * b ≤ N ^ 2 := by rw [sq]; exact Nat.mul_le_mul hb' hb'
  have hN' : x * y ≤ N ^ 2 := by rw [sq]; exact Nat.mul_le_mul hx' hy'
  rcases lt_trichotomy (B2 ^ 2) (B1 * B3) with h | h | h
  · have h1 := pow_sub_pow_ge (B1 * B3) (B2 ^ 2) l (by omega) h
    refine core_contra N k (B2 ^ 2) l hl hk hkN ?_ (by omega)
    have : 4 * ((B2 ^ 2) ^ l + l * (B2 ^ 2) ^ (l - 1)) ≤ 4 * (B1 * B3) ^ l :=
      Nat.mul_le_mul_left _ h1
    nlinarith
  · exact hne (by rw [ebb, exy, h])
  · have h1 := pow_sub_pow_ge (B2 ^ 2) (B1 * B3) l (by omega) h
    refine core_contra N k (B1 * B3) l hl hk hkN ?_ (by omega)
    have : 4 * ((B1 * B3) ^ l + l * (B1 * B3) ^ (l - 1)) ≤ 4 * (B2 ^ 2) ^ l :=
      Nat.mul_le_mul_left _ h1
    nlinarith

/-! ### Steps (2) – (4) of the proof -/

/-- Steps (2) – (4) of the proof of Erdős' theorem: if `n ≥ 2 k`, `k ≥ 4`, `l ≥ 2` and
`n > k ^ l` (Step (1)), then `choose n k` is not an `l`-th power. -/
theorem erdos_main (n k l m : ℕ) (hl : 2 ≤ l) (hk : 4 ≤ k) (h2k : 2 * k ≤ n)
    (hnk : k ^ l < n)
    (H : choose n k = m ^ l) : False := by
  have hkn : k ≤ n := by omega
  have hk2 : k * k < n := by
    have : k ^ 2 ≤ k ^ l := Nat.pow_le_pow_right (by omega) hl
    nlinarith
  have hdesc : n.descFactorial k = k ! * m ^ l := by
    rw [descFactorial_eq_factorial_mul_choose, H]
  set a : ℕ → ℕ := fun j => freePart l (n - j) with ha_def
  set B : ℕ → ℕ := fun j => powPart l (n - j) with hB_def
  have hab : ∀ j < k, n - j = a j * B j ^ l := fun j hj =>
    (freePart_mul_powPart l (n - j) (by omega)).symm
  -- Step (2): the `a j` are distinct
  have hinj : Set.InjOn a (range k) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact free_ne n k l i j (a i) (B i) (B j) hl h hj h2k hk2 (hab i hi)
        (by rw [hab j hj, hij])
    · exact free_ne n k l j i (a j) (B j) (B i) hl h hi h2k hk2 (hab j hj)
        (by rw [hab i hi, hij])
  -- Step (3): the product of the `a j` divides `k !`, so the `a j` are `1, …, k`
  have hdvd : ∏ j ∈ range k, a j ∣ k ! := by
    have hne : ∀ j ∈ range k, a j ≠ 0 := fun j _ => freePart_ne_zero _ _
    rw [← Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hne) (factorial_ne_zero k),
      Nat.factorization_prod hne]
    intro p
    rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [ha_def, freePart_factorization_apply]
    by_cases hp : p.Prime
    · exact sum_mod_le_factorial n k p m l hp (by omega) hkn hdesc
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  set S := (range k).image a with hS
  have hSk : #S = k := by rw [Finset.card_image_of_injOn hinj, card_range]
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact Nat.pos_of_ne_zero (freePart_ne_zero _ _)
  have hSprod : ∏ x ∈ S, x ≤ k ! := by
    rw [prod_image hinj]
    exact Nat.le_of_dvd (factorial_pos k) hdvd
  have hSeq := eq_Icc_of_prod_le k S hSk hSpos hSprod
  have hmem : ∀ v, 1 ≤ v → v ≤ k → ∃ j < k, a j = v := by
    intro v h1 h2
    have : v ∈ S := by rw [hSeq]; exact mem_Icc.mpr ⟨h1, h2⟩
    obtain ⟨j, hj, hjv⟩ := mem_image.mp this
    exact ⟨j, mem_range.mp hj, hjv⟩
  -- Step (4)
  obtain ⟨j4, hj4, ha4⟩ := hmem 4 (by norm_num) hk
  rcases eq_or_lt_of_le hl with hl2 | hl3
  · -- the case `l = 2`: `4` is a square
    subst hl2
    have h1 : (a j4).factorization 2 = (n - j4).factorization 2 % 2 :=
      freePart_factorization_apply _ _ _
    have h2 : (a j4).factorization 2 = 2 := by
      rw [ha4, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have := Nat.mod_lt ((n - j4).factorization 2) (show 0 < 2 by norm_num)
    omega
  · -- the case `l ≥ 3`
    obtain ⟨j1, hj1, ha1⟩ := hmem 1 le_rfl (by omega)
    obtain ⟨j2, hj2, ha2⟩ := hmem 2 (by norm_num) (by omega)
    have hk3 : k ^ 3 < n := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hl3) hnk
    have e1 := hab j1 hj1
    have e2 := hab j2 hj2
    have e4 := hab j4 hj4
    rw [ha1, one_mul] at e1
    rw [ha2] at e2
    rw [ha4] at e4
    refine final_l3 n k l (n - j1) (n - j2) (n - j4) (B j1) (B j2) (B j4) hl3 hk hk3
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ e1 e2 e4
    · intro h
      have : j1 = j2 := by omega
      rw [this] at ha1; omega
    · intro h
      have : j4 = j2 := by omega
      rw [this] at ha4; omega

end chapter3.Erdos
