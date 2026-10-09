/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic
/-!
# On a lemma of Littlewood and Offord

Formalization of Chapter 25 of *Proofs from THE BOOK* (Aigner–Ziegler).

## Main results

* `LittlewoodOfford.kleitman` : **Kleitman's theorem.** For vectors `a₁, …, aₙ` of length at
  least `1` in a real inner product space and `k` regions `R₁, …, R_k` such that any two points
  of the same region have distance `< 2`, the number of sign vectors `ε ∈ {1, -1}ⁿ` with
  `∑ εᵢ aᵢ ∈ ⋃ Rⱼ` is at most the sum of the `k` largest binomial coefficients `(n choose j)`.
* `LittlewoodOfford.kleitman_ball` : the case `k = 1` (Erdős' conjecture, in any real
  Hilbert space): at most `(n choose ⌊n/2⌋)` sums lie in an open ball of radius `1`.
* `LittlewoodOfford.erdos_complex` : the same for complex numbers and open discs.
* `LittlewoodOfford.erdos_real` : Erdős' argument for real numbers via Sperner's theorem.
* `LittlewoodOfford.choose_half_le` : `(n choose ⌊n/2⌋) ≤ 2ⁿ / √n` (the Stirling-type estimate),
  giving Erdős' improvement `LittlewoodOfford.erdos_bound` and the original Littlewood–Offord
  bound `LittlewoodOfford.littlewood_offord`.
* `LittlewoodOfford.kleitman_sharp` : the bound in Kleitman's theorem is attained by
  `a₁ = ⋯ = aₙ = e` (a unit vector) and suitable open balls of radius `1`.
* `LittlewoodOfford.claim` : the Claim in the proof of Kleitman's theorem.
* `LittlewoodOfford.middleChooseSum_succ` : the binomial identity (1).
-/

@[expose] public section

open Finset Function
open scoped RealInnerProductSpace

namespace LittlewoodOfford

/-! ### Binomial coefficients -/

/-- The sum of the `k` largest binomial coefficients `(n choose i)`, `0 ≤ i ≤ n`: the maximum of
`∑_{i ∈ S} (n choose i)` over all sets `S` of at most `k` indices. -/
def sumLargestChoose (n k : ℕ) : ℕ :=
  ({S ∈ (range (n + 1)).powerset | S.card ≤ k}).sup fun S => ∑ i ∈ S, n.choose i

/-- The explicit form used in the book: `∑_{i=r}^{s} (n choose i)` with
`r = ⌊(n-k+1)/2⌋` and `s = ⌊(n+k-1)/2⌋`. -/
def middleChooseSum (n k : ℕ) : ℕ :=
  ∑ i ∈ Ico ((n + 1 - k) / 2) ((n + k + 1) / 2), n.choose i

lemma middleChooseSum_eq_sum_ite (n k M : ℕ) (hM : n + k + 1 ≤ 2 * M) :
    middleChooseSum n k =
      ∑ i ∈ range M, if n ≤ 2 * i + k ∧ 2 * i < n + k then n.choose i else 0 := by
  rw [← sum_filter, middleChooseSum]
  congr 1
  ext i
  simp only [mem_Ico, mem_filter, mem_range]
  omega

/-- Identity (1) of the book: `∑_{i=r}^{s} (n+1 choose i)` splits as the sum of the `k + 1` and
the `k - 1` middle binomial coefficients of `n`. -/
theorem middleChooseSum_succ (n k : ℕ) (hk : 1 ≤ k) :
    middleChooseSum (n + 1) k = middleChooseSum n (k + 1) + middleChooseSum n (k - 1) := by
  rw [middleChooseSum_eq_sum_ite (n + 1) k (n + k + 3) (by omega),
    middleChooseSum_eq_sum_ite n (k + 1) (n + k + 2) (by omega),
    middleChooseSum_eq_sum_ite n (k - 1) (n + k + 2) (by omega), ← sum_add_distrib,
    sum_range_succ']
  have h1 : ∀ i, (if n + 1 ≤ 2 * (i + 1) + k ∧ 2 * (i + 1) < n + 1 + k then
      (n + 1).choose (i + 1) else 0) =
      (if n + 1 ≤ 2 * (i + 1) + k ∧ 2 * (i + 1) < n + 1 + k then n.choose i else 0) +
      (if n + 1 ≤ 2 * (i + 1) + k ∧ 2 * (i + 1) < n + 1 + k then n.choose (i + 1) else 0) := by
    intro i; rw [Nat.choose_succ_succ']; split_ifs <;> simp
  simp only [h1, sum_add_distrib]
  set f : ℕ → ℕ := fun i => if n + 1 ≤ 2 * i + k ∧ 2 * i < n + 1 + k then n.choose i else 0
    with hf
  have h2 : (∑ i ∈ range (n + k + 2), f (i + 1)) +
      (if n + 1 ≤ 2 * 0 + k ∧ 2 * 0 < n + 1 + k then (n + 1).choose 0 else 0) =
      ∑ i ∈ range (n + k + 2), f i := by
    have : ∑ i ∈ range (n + k + 2), f i = ∑ i ∈ range (n + k + 2 + 1), f i := by
      rw [sum_range_succ _ (n + k + 2)]
      simp [hf, Nat.choose_eq_zero_of_lt (by omega : n < n + k + 2)]
    rw [this, sum_range_succ' _ (n + k + 2)]
    simp [hf]
  rw [add_assoc, h2, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  simp only [hf]
  split_ifs <;> omega

lemma choose_le_choose_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma choose_le_choose_of_min_le {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (h : min j (n - j) ≤ min i (n - i)) : n.choose j ≤ n.choose i := by
  have key : ∀ m, m ≤ n → n.choose m = n.choose (min m (n - m)) := by
    intro m hm
    rcases le_total m (n - m) with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h', Nat.choose_symm hm]
  rw [key i hi, key j hj]
  exact choose_le_choose_of_le_half h (by omega)

lemma middleChooseSum_eq_sum_mid (n k : ℕ) :
    middleChooseSum n k =
      ∑ i ∈ Ico ((n + 1 - k) / 2) (min ((n + k + 1) / 2) (n + 1)), n.choose i := by
  rw [middleChooseSum]
  symm
  apply sum_subset
  · intro i; simp only [mem_Ico]; omega
  · intro i hi hi'
    simp only [mem_Ico] at hi hi'
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- The middle binomial coefficients are indeed the `k` largest ones. -/
theorem sumLargestChoose_eq_middleChooseSum (n k : ℕ) :
    sumLargestChoose n k = middleChooseSum n k := by
  rw [middleChooseSum_eq_sum_mid]
  set M := Ico ((n + 1 - k) / 2) (min ((n + k + 1) / 2) (n + 1)) with hM
  have hMsub : M ⊆ range (n + 1) := by
    intro i; simp only [hM, mem_Ico, mem_range]; omega
  have hMcard : M.card = min k (n + 1) := by
    simp only [hM, Nat.card_Ico]; omega
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    obtain ⟨hSsub, hScard⟩ := hS
    have e1 := sum_sdiff (f := fun i => n.choose i) (inter_subset_left : S ∩ M ⊆ S)
    have e2 := sum_sdiff (f := fun i => n.choose i) (inter_subset_right : S ∩ M ⊆ M)
    rw [sdiff_inter_self_left] at e1
    rw [sdiff_inter_self_right] at e2
    rw [← e1, ← e2]
    gcongr ?_ + _
    rcases (S \ M).eq_empty_or_nonempty with h | ⟨j0, hj0⟩
    · simp [h]
    have hk : M.card = k := by
      rcases le_or_gt k (n + 1) with h | h
      · omega
      · exfalso
        have : M = range (n + 1) := eq_of_subset_of_card_le hMsub (by simp; omega)
        rw [mem_sdiff, this] at hj0
        exact hj0.2 (hSsub hj0.1)
    have hcard : (S \ M).card ≤ (M \ S).card := by
      have a1 := card_sdiff_add_card_inter S M
      have a2 := card_sdiff_add_card_inter M S
      rw [inter_comm] at a2
      omega
    have hne : (M \ S).Nonempty := by
      rw [← card_pos]; have := card_pos.mpr ⟨j0, hj0⟩; omega
    obtain ⟨i0, hi0, hmin⟩ := exists_min_image (M \ S) (fun i => n.choose i) hne
    have hle : ∀ j ∈ S \ M, n.choose j ≤ n.choose i0 := by
      intro j hj
      rw [mem_sdiff] at hj hi0
      have hjn := mem_range.mp (hSsub hj.1)
      have hi0' := hi0.1
      have hj' := hj.2
      simp only [hM, mem_Ico] at hi0' hj'
      apply choose_le_choose_of_min_le (by omega) (by omega)
      omega
    calc ∑ i ∈ S \ M, n.choose i ≤ (S \ M).card • n.choose i0 := sum_le_card_nsmul _ _ _ hle
      _ ≤ (M \ S).card • n.choose i0 := by gcongr
      _ ≤ ∑ i ∈ M \ S, n.choose i := card_nsmul_le_sum _ _ _ hmin
  · apply Finset.le_sup_of_le (b := M)
    · simp only [mem_filter, mem_powerset]
      exact ⟨hMsub, by omega⟩
    · exact le_rfl

/-- For `k = 1` the bound is the middle binomial coefficient. -/
theorem sumLargestChoose_one (n : ℕ) : sumLargestChoose n 1 = n.choose (n / 2) := by
  rw [sumLargestChoose_eq_middleChooseSum, middleChooseSum]
  have : Ico ((n + 1 - 1) / 2) ((n + 1 + 1) / 2) = {n / 2} := by
    ext i; simp only [mem_Ico, mem_singleton]; omega
  rw [this, sum_singleton]

/-! ### Signed sums -/

open Classical in
/-- The number of sign vectors `ε ∈ {1, -1}ⁿ` (encoded as `ε : Fin n → ℤˣ`) such that the linear
combination `∑ εᵢ aᵢ` lies in `S`. -/
noncomputable def numSumsIn {E : Type*} [AddCommGroup E] {n : ℕ} (a : Fin n → E) (S : Set E) :
    ℕ :=
  #{ε : Fin n → ℤˣ | ∑ i, (ε i : ℤ) • a i ∈ S}

/-- Membership in a set-builder set (stated locally so that it is stable across Mathlib
versions). -/
lemma mem_setOf_iff' {α : Type*} {p : α → Prop} {x : α} : x ∈ {y | p y} ↔ p x := Iff.rfl

section numSumsIn

variable {E : Type*} [AddCommGroup E]

lemma numSumsIn_mono {n : ℕ} (a : Fin n → E) {S T : Set E} (h : S ⊆ T) :
    numSumsIn a S ≤ numSumsIn a T := by
  classical
  unfold numSumsIn
  exact card_le_card (monotone_filter_right _ fun ε _ hε => h hε)

lemma numSumsIn_union_le {n : ℕ} (a : Fin n → E) (S T : Set E) :
    numSumsIn a (S ∪ T) ≤ numSumsIn a S + numSumsIn a T := by
  classical
  unfold numSumsIn
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro ε hε
  simp only [mem_filter, mem_union, mem_univ, true_and, Set.mem_union] at hε ⊢
  exact hε

lemma numSumsIn_union_of_disjoint {n : ℕ} (a : Fin n → E) {S T : Set E} (h : Disjoint S T) :
    numSumsIn a (S ∪ T) = numSumsIn a S + numSumsIn a T := by
  classical
  unfold numSumsIn
  rw [← card_union_of_disjoint]
  · congr 1; ext ε; simp
  · exact disjoint_filter.mpr fun ε _ h1 h2 => Set.disjoint_left.mp h h1 h2

lemma numSumsIn_empty {n : ℕ} (a : Fin n → E) : numSumsIn a ∅ = 0 := by
  classical
  simp [numSumsIn]

lemma numSumsIn_congr {n : ℕ} (a : Fin n → E) {S T : Set E}
    (h : ∀ ε : Fin n → ℤˣ, ∑ i, (ε i : ℤ) • a i ∈ S ↔ ∑ i, (ε i : ℤ) • a i ∈ T) :
    numSumsIn a S = numSumsIn a T := by
  classical
  unfold numSumsIn
  congr 1
  exact filter_congr fun ε _ => h ε

lemma numSumsIn_zero_le (a : Fin 0 → E) (S : Set E) : numSumsIn a S ≤ 1 := by
  classical
  unfold numSumsIn
  exact (card_filter_le _ _).trans (by simp)

/-- Splitting off the first vector: the sums with `ε₀ = 1` and those with `ε₀ = -1`. -/
lemma numSumsIn_succ {n : ℕ} (a : Fin (n + 1) → E) (S : Set E) :
    numSumsIn a S = numSumsIn (Fin.tail a) {s | a 0 + s ∈ S} +
      numSumsIn (Fin.tail a) {s | -a 0 + s ∈ S} := by
  classical
  unfold numSumsIn
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => ℤˣ).sum_comp, Fintype.sum_prod_type]
  have hu : (univ : Finset ℤˣ) = {1, -1} := by decide
  rw [hu, sum_pair (by decide)]
  congr 1 <;> refine sum_congr rfl fun ε _ => if_congr ?_ rfl rfl <;>
    simp [Fin.consEquiv, Fin.sum_univ_succ, Fin.tail]

end numSumsIn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Claim** in the proof of Kleitman's theorem (for finite regions, which is all that is
needed in the proof): if `‖v‖ ≥ 1` and each region has all distances `< 2`, then at least one of
the translated regions `Rⱼ - v` is disjoint from all the translated regions `Rᵢ + v`. -/
theorem claim [DecidableEq E] {ι : Type*} [Fintype ι] [Nonempty ι] (R : ι → Finset E)
    (hR : ∀ j, ∀ x ∈ R j, ∀ y ∈ R j, ‖x - y‖ < 2) (v : E) (hv : 1 ≤ ‖v‖) :
    ∃ j, ∀ i, Disjoint ((R j).image (· - v)) ((R i).image (· + v)) := by
  rcases (univ.biUnion R).eq_empty_or_nonempty with hU | hU
  · obtain ⟨j⟩ := ‹Nonempty ι›
    refine ⟨j, fun i => ?_⟩
    have : R j = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have : x ∈ univ.biUnion R := mem_biUnion.mpr ⟨j, mem_univ _, hx⟩
      simp [hU] at this
    simp [this]
  obtain ⟨y, hy, hmin⟩ := exists_min_image _ (fun y => ⟪v, y⟫) hU
  obtain ⟨j, -, hyj⟩ := mem_biUnion.mp hy
  refine ⟨j, fun i => ?_⟩
  rw [disjoint_left]
  rintro _ hx hz
  simp only [mem_image] at hx hz
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨z, hz, hzx⟩ := hz
  have h1 : ⟪v, y⟫ ≤ ⟪v, z⟫ := hmin z (mem_biUnion.mpr ⟨i, mem_univ _, hz⟩)
  have hxz : x - y = (z - y) + (v + v) := by
    rw [eq_sub_iff_add_eq] at hzx; rw [← hzx]; abel
  have h2 : ⟪v, x - y⟫ = ⟪v, z - y⟫ + 2 * ‖v‖ ^ 2 := by
    rw [hxz, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq]; ring
  have h3 := real_inner_le_norm v (x - y)
  have h4 := hR j x hx y hyj
  have h5 : ⟪v, z - y⟫ ≥ 0 := by rw [inner_sub_right]; linarith
  nlinarith [norm_nonneg v, norm_nonneg (x - y)]

lemma kleitman_finset [DecidableEq E] (n : ℕ) : ∀ (a : Fin n → E), (∀ i, 1 ≤ ‖a i‖) →
    ∀ (ι : Type) [Fintype ι] (R : ι → Finset E), Pairwise (Disjoint on R) →
    (∀ j, ∀ x ∈ R j, ∀ y ∈ R j, ‖x - y‖ < 2) →
    numSumsIn a (⋃ j, (R j : Set E)) ≤ middleChooseSum n (Fintype.card ι) := by
  classical
  induction n with
  | zero =>
    intro a ha ι _ R hdisj hR
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · rw [Fintype.card_eq_zero_iff] at h
      simp [Set.iUnion_of_empty, numSumsIn_empty]
    · refine (numSumsIn_zero_le a _).trans ?_
      have h0 : 0 ∈ Ico ((0 + 1 - Fintype.card ι) / 2) ((0 + Fintype.card ι + 1) / 2) := by
        simp only [mem_Ico]; omega
      have := single_le_sum (f := fun i => Nat.choose 0 i) (fun _ _ => Nat.zero_le _) h0
      simpa [middleChooseSum] using this
  | succ n ih =>
    intro a ha ι _ R hdisj hR
    rw [numSumsIn_succ]
    set v := a 0 with hv
    set b := Fin.tail a with hb
    have hb' : ∀ i, 1 ≤ ‖b i‖ := fun i => ha _
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Set.iUnion_of_empty, numSumsIn_empty]
    obtain ⟨j, hj⟩ := claim R hR v (ha 0)
    have hk : 1 ≤ Fintype.card ι := Fintype.card_pos
    let T : Option ι → Finset E :=
      fun o => o.elim ((R j).image (· - v)) (fun i => (R i).image (· + v))
    let T' : {i // i ≠ j} → Finset E := fun i => (R i).image (· - v)
    have hTdiam : ∀ o, ∀ x ∈ T o, ∀ y ∈ T o, ‖x - y‖ < 2 := by
      rintro (_ | i) x hx y hy <;> simp only [T, Option.elim, mem_image] at hx hy <;>
        obtain ⟨x, hx, rfl⟩ := hx <;> obtain ⟨y, hy, rfl⟩ := hy
      · simpa using hR j x hx y hy
      · simpa using hR i x hx y hy
    have hT'diam : ∀ o, ∀ x ∈ T' o, ∀ y ∈ T' o, ‖x - y‖ < 2 := by
      rintro i x hx y hy
      simp only [T', mem_image] at hx hy
      obtain ⟨x, hx, rfl⟩ := hx; obtain ⟨y, hy, rfl⟩ := hy
      simpa using hR i x hx y hy
    have hTdisj : Pairwise (Disjoint on T) := by
      rintro (_ | i) (_ | i') hne
      · exact absurd rfl hne
      · exact hj i'
      · exact (hj i).symm
      · exact (disjoint_image (add_left_injective v)).mpr (hdisj (fun h => hne (by rw [h])))
    have hT'disj : Pairwise (Disjoint on T') := by
      rintro i i' hne
      exact (disjoint_image (sub_left_injective)).mpr (hdisj (fun h => hne (Subtype.ext h)))
    have IH1 := ih b hb' (Option ι) T hTdisj hTdiam
    have IH2 := ih b hb' {i // i ≠ j} T' hT'disj hT'diam
    rw [Fintype.card_option] at IH1
    simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at IH2
    set A := {s | v + s ∈ ⋃ i, (R i : Set E)}
    set B := {s | -v + s ∈ ⋃ i, (R i : Set E)}
    set Aj := {s | v + s ∈ (R j : Set E)}
    have hA : A ⊆ Aj ∪ ⋃ i, (T' i : Set E) := by
      intro s hs
      simp only [A, mem_setOf_iff', Set.mem_iUnion, mem_coe] at hs
      obtain ⟨i, hi⟩ := hs
      by_cases hij : i = j
      · subst hij; exact Or.inl hi
      · right
        simp only [Set.mem_iUnion, T', coe_image, Set.mem_image, mem_coe]
        exact ⟨⟨i, hij⟩, v + s, hi, by abel⟩
    have hBAj : Disjoint B Aj := by
      rw [Set.disjoint_left]
      intro s hsB hsA
      simp only [B, Aj, mem_setOf_iff', Set.mem_iUnion, mem_coe] at hsB hsA
      obtain ⟨i, hi⟩ := hsB
      exact Finset.disjoint_left.mp (hj i)
        (mem_image.mpr ⟨v + s, hsA, show v + s - v = s by abel⟩)
        (mem_image.mpr ⟨-v + s, hi, show -v + s + v = s by abel⟩)
    have hBAjT : B ∪ Aj = ⋃ o, (T o : Set E) := by
      ext s
      simp only [B, Aj, Set.mem_union, mem_setOf_iff', Set.mem_iUnion, mem_coe]
      constructor
      · rintro (⟨i, hi⟩ | h)
        · exact ⟨some i, mem_image.mpr ⟨-v + s, hi, by abel⟩⟩
        · exact ⟨none, mem_image.mpr ⟨v + s, h, by abel⟩⟩
      · rintro ⟨_ | i, h⟩ <;> simp only [T, Option.elim, mem_image] at h <;>
          obtain ⟨x, hx, rfl⟩ := h
        · right; simpa using hx
        · left; exact ⟨i, by simpa using hx⟩
    rw [middleChooseSum_succ n _ hk]
    calc numSumsIn b A + numSumsIn b B
        ≤ numSumsIn b Aj + numSumsIn b (⋃ i, (T' i : Set E)) + numSumsIn b B :=
          by gcongr; exact (numSumsIn_mono b hA).trans (numSumsIn_union_le b _ _)
      _ = numSumsIn b (B ∪ Aj) + numSumsIn b (⋃ i, (T' i : Set E)) := by
          rw [numSumsIn_union_of_disjoint b hBAj]; ring
      _ ≤ _ := by rw [hBAjT]; exact add_le_add IH1 IH2

/-- **Kleitman's theorem.** Let `a₁, …, aₙ` be vectors of length at least `1` in a real inner
product space (e.g. `ℝᵈ`), and let `R₁, …, R_k` be regions such that `‖x - y‖ < 2` whenever
`x, y` lie in the same region. Then the number of linear combinations `∑ εᵢ aᵢ`, `εᵢ ∈ {1, -1}`,
lying in `⋃ Rⱼ` is at most the sum of the `k` largest binomial coefficients `(n choose j)`.
(The book assumes the regions are open; this hypothesis is not needed.) -/
theorem kleitman {n k : ℕ} (a : Fin n → E) (ha : ∀ i, 1 ≤ ‖a i‖) (R : Fin k → Set E)
    (hR : ∀ j, ∀ x ∈ R j, ∀ y ∈ R j, ‖x - y‖ < 2) :
    numSumsIn a (⋃ j, R j) ≤ sumLargestChoose n k := by
  classical
  -- only the finitely many points `∑ εᵢ aᵢ` matter; we also make the regions disjoint
  let P : Finset E := univ.image (fun ε : Fin n → ℤˣ => ∑ i, (ε i : ℤ) • a i)
  let R' : Fin k → Finset E := fun j => P.filter (fun x => x ∈ R j ∧ ∀ i < j, x ∉ R i)
  have hdisj : Pairwise (Disjoint on R') := by
    intro i j hij
    rw [onFun, Finset.disjoint_left]
    intro x hi hj
    simp only [R', mem_filter] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hj.2.2 i h hi.2.1
    · exact hi.2.2 j h hj.2.1
  have hdiam : ∀ j, ∀ x ∈ R' j, ∀ y ∈ R' j, ‖x - y‖ < 2 := fun j x hx y hy =>
    hR j x (mem_filter.mp hx).2.1 y (mem_filter.mp hy).2.1
  have h := kleitman_finset n a ha (Fin k) R' hdisj hdiam
  rw [Fintype.card_fin, ← sumLargestChoose_eq_middleChooseSum] at h
  refine le_of_eq_of_le ?_ h
  apply numSumsIn_congr
  intro ε
  have hP : ∑ i, (ε i : ℤ) • a i ∈ P := mem_image_of_mem _ (mem_univ ε)
  simp only [Set.mem_iUnion, mem_coe, R', mem_filter]
  constructor
  · rintro ⟨j, hj⟩
    have hne : (univ.filter fun j => ∑ i, (ε i : ℤ) • a i ∈ R j).Nonempty := ⟨j, by simp [hj]⟩
    refine ⟨_, hP, (mem_filter.mp (min'_mem _ hne)).2, fun i hi hiR => ?_⟩
    exact absurd hi (not_lt.mpr (min'_le _ i (by simp [hiR])))
  · rintro ⟨j, -, hj, -⟩
    exact ⟨j, hj⟩

/-- Kleitman's theorem for `k = 1` (Erdős' conjecture in Hilbert spaces): at most
`(n choose ⌊n/2⌋)` of the sums `∑ εᵢ aᵢ` lie in any open ball of radius `1`. -/
theorem kleitman_ball {n : ℕ} (a : Fin n → E) (ha : ∀ i, 1 ≤ ‖a i‖) (c : E) :
    numSumsIn a (Metric.ball c 1) ≤ n.choose (n / 2) := by
  have h := kleitman a ha (fun _ : Fin 1 => Metric.ball c 1) (fun _ x hx y hy => by
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x c + dist y c := dist_triangle_right _ _ _
      _ < 1 + 1 := add_lt_add (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy)
      _ = 2 := by norm_num)
  rwa [Set.iUnion_const, sumLargestChoose_one] at h

/-- Erdős' conjecture for complex numbers (Katona, Kleitman): for complex numbers `aᵢ` with
`|aᵢ| ≥ 1`, at most `(n choose ⌊n/2⌋)` of the sums `∑ εᵢ aᵢ` lie in the interior of any circle
of radius `1`. -/
theorem erdos_complex {n : ℕ} (a : Fin n → ℂ) (ha : ∀ i, 1 ≤ ‖a i‖) (c : ℂ) :
    numSumsIn a (Metric.ball c 1) ≤ n.choose (n / 2) :=
  kleitman_ball a ha c

lemma units_mul_aux (u u' : ℤˣ) (x : ℝ) (hx : 1 ≤ |x|)
    (h : 0 < ((u : ℤ) : ℝ) * x → 0 < ((u' : ℤ) : ℝ) * x) :
    ((u : ℤ) : ℝ) * x ≤ ((u' : ℤ) : ℝ) * x ∧
      (0 < ((u' : ℤ) : ℝ) * x → ¬ 0 < ((u : ℤ) : ℝ) * x →
        2 ≤ ((u' : ℤ) : ℝ) * x - ((u : ℤ) : ℝ) * x) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;>
    simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul,
      neg_mul] at h ⊢ <;>
    rcases le_or_gt 0 x with hx0 | hx0 <;>
    simp only [abs_of_nonneg, abs_of_neg, hx0] at hx <;>
    first
    | (constructor <;> intros <;> linarith)
    | (exfalso; linarith [h (by linarith)])

/-- Erdős' argument for real numbers, via Sperner's theorem: if `|aᵢ| ≥ 1` then at most
`(n choose ⌊n/2⌋)` of the sums `∑ εᵢ aᵢ` lie in a set `S` all of whose points have distance
`< 2` (e.g. the interior of an interval of length `2`). -/
theorem erdos_real {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 ≤ |a i|) (S : Set ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, |x - y| < 2) :
    numSumsIn a S ≤ n.choose (n / 2) := by
  classical
  unfold numSumsIn
  set F := ({ε : Fin n → ℤˣ | ∑ i, (ε i : ℤ) • a i ∈ S} : Finset _)
  -- `I(ε) = {i : εᵢ aᵢ > 0}` (the book first normalizes to `aᵢ > 0`, `I = {i : εᵢ = 1}`)
  let f : (Fin n → ℤˣ) → Finset (Fin n) := fun ε => {i | 0 < ((ε i : ℤ) : ℝ) * a i}
  have hsum : ∀ ε : Fin n → ℤˣ, ∑ i, (ε i : ℤ) • a i = ∑ i, ((ε i : ℤ) : ℝ) * a i := by
    intro ε; simp [zsmul_eq_mul]
  have key : ∀ ε ε', f ε ⊆ f ε' → ∀ i, ((ε i : ℤ) : ℝ) * a i ≤ ((ε' i : ℤ) : ℝ) * a i ∧
      (i ∈ f ε' → i ∉ f ε → 2 ≤ ((ε' i : ℤ) : ℝ) * a i - ((ε i : ℤ) : ℝ) * a i) := by
    intro ε ε' hsub i
    have := units_mul_aux (ε i) (ε' i) (a i) (ha i) (fun h => by
      have := hsub (show i ∈ f ε by simp [f, h]); simpa [f] using this)
    refine ⟨this.1, fun h1 h2 => this.2 (by simpa [f] using h1) (by simpa [f] using h2)⟩
  have hinj : Function.Injective f := by
    intro ε ε' h
    funext i
    have h1 := (key ε ε' h.le i).1
    have h2 := (key ε' ε h.ge i).1
    have hai : a i ≠ 0 := by intro h0; have := ha i; rw [h0] at this; norm_num at this
    have : ((ε i : ℤ) : ℝ) = ((ε' i : ℤ) : ℝ) := mul_right_cancel₀ hai (le_antisymm h1 h2)
    exact Units.ext (by exact_mod_cast this)
  -- the sets `I(ε)` form an antichain
  have hanti : IsAntichain (· ⊆ ·)
      ((F.image f : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
    rintro s hs t ht hne hst
    simp only [coe_image, Set.mem_image, mem_coe, F, mem_filter, mem_univ, true_and] at hs ht
    obtain ⟨ε, hε, rfl⟩ := hs
    obtain ⟨ε', hε', rfl⟩ := ht
    obtain ⟨i0, hi0t, hi0s⟩ := exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
    have hdiff : 2 ≤ ∑ i, ((ε' i : ℤ) : ℝ) * a i - ∑ i, ((ε i : ℤ) : ℝ) * a i := by
      rw [← sum_sub_distrib]
      calc (2 : ℝ) ≤ ((ε' i0 : ℤ) : ℝ) * a i0 - ((ε i0 : ℤ) : ℝ) * a i0 :=
            (key ε ε' hst i0).2 hi0t hi0s
        _ ≤ _ := single_le_sum (f := fun i => ((ε' i : ℤ) : ℝ) * a i - ((ε i : ℤ) : ℝ) * a i)
            (fun i _ => sub_nonneg.mpr (key ε ε' hst i).1) (mem_univ i0)
    have := hS _ hε' _ hε
    rw [hsum, hsum] at this
    have := (abs_lt.mp this).2
    linarith
  -- Sperner's theorem
  have := hanti.sperner
  rw [Fintype.card_fin, card_image_of_injective _ hinj] at this
  exact this

lemma centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have key : ((m + 1) * (m + 1).centralBinom) ^ 2 * (3 * (m + 1) + 1) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      rw [h, pow_succ]
      have : (2 * (2 * m + 1)) ^ 2 * (3 * m + 4) ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) := by
        ring_nf; nlinarith
      calc (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (3 * (m + 1) + 1)
          = (2 * (2 * m + 1)) ^ 2 * (3 * m + 4) * m.centralBinom ^ 2 := by ring
        _ ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) * m.centralBinom ^ 2 := by gcongr
        _ = (m + 1) ^ 2 * 16 * (m.centralBinom ^ 2 * (3 * m + 1)) := by ring
        _ ≤ (m + 1) ^ 2 * 16 * 16 ^ m := by gcongr
        _ = (m + 1) ^ 2 * (16 ^ m * 16) := by ring
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    rw [mul_pow, mul_assoc] at key
    exact Nat.le_of_mul_le_mul_left key hpos

lemma choose_half_sq_mul_le (n : ℕ) : n.choose (n / 2) ^ 2 * n ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := centralBinom_sq_mul_le m
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have : 2 * m / 2 = m := by omega
    rw [this, pow_mul]
    norm_num
    calc (2 * m).choose m ^ 2 * (2 * m) ≤ (2 * m).choose m ^ 2 * (3 * m + 1) := by gcongr; omega
      _ ≤ 16 ^ m := h
  · have h := centralBinom_sq_mul_le (m + 1)
    have h2 : (m + 1).centralBinom = 2 * (2 * m + 1).choose m := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Nat.choose_succ_succ', Nat.choose_symm_half]; ring
    have : (2 * m + 1) / 2 = m := by omega
    rw [this]
    rw [h2] at h
    have e : (4:ℕ) ^ (2 * m + 1) * 4 = 16 ^ (m + 1) := by
      rw [pow_succ, pow_succ, pow_mul]; ring
    have : (2 * m + 1).choose m ^ 2 * (2 * m + 1) * 4 ≤ 4 ^ (2 * m + 1) * 4 := by
      rw [e]
      calc (2 * m + 1).choose m ^ 2 * (2 * m + 1) * 4
          = (2 * (2 * m + 1).choose m) ^ 2 * (2 * m + 1) := by ring
        _ ≤ (2 * (2 * m + 1).choose m) ^ 2 * (3 * (m + 1) + 1) := by gcongr <;> omega
        _ ≤ _ := h
    omega

/-- The estimate `(n choose ⌊n/2⌋) ≤ 2ⁿ / √n` (a consequence of Stirling's formula in the book). -/
theorem choose_half_le (n : ℕ) (hn : 1 ≤ n) :
    (n.choose (n / 2) : ℝ) ≤ 2 ^ n / Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  rw [le_div_iff₀ hs]
  have h := choose_half_sq_mul_le n
  have h' : ((n.choose (n / 2) : ℝ) * Real.sqrt n) ^ 2 ≤ (2 ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn'.le, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
    exact_mod_cast h
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h'

/-- Erdős' improvement of the Littlewood–Offord bound: for complex `aᵢ` with `|aᵢ| ≥ 1`, at most
`2ⁿ / √n` of the sums lie in the interior of any circle of radius `1`. -/
theorem erdos_bound {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℂ) (ha : ∀ i, 1 ≤ ‖a i‖) (c : ℂ) :
    (numSumsIn a (Metric.ball c 1) : ℝ) ≤ 2 ^ n / Real.sqrt n :=
  (Nat.cast_le.mpr (erdos_complex a ha c)).trans (choose_half_le n hn)

/-- **The lemma of Littlewood and Offord** (1943): there is a constant `C > 0` such that for
complex `aᵢ` with `|aᵢ| ≥ 1`, at most `C 2ⁿ log n / √n` of the sums `∑ εᵢ aᵢ` lie in the interior
of any circle of radius `1`. -/
theorem littlewood_offord : ∃ C > (0 : ℝ), ∀ n ≥ 2, ∀ a : Fin n → ℂ, (∀ i, 1 ≤ ‖a i‖) →
    ∀ c : ℂ, (numSumsIn a (Metric.ball c 1) : ℝ) ≤ C * 2 ^ n / Real.sqrt n * Real.log n := by
  refine ⟨1 / Real.log 2, by positivity, fun n hn a ha c => ?_⟩
  have h := erdos_bound (by omega) a ha c
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc (numSumsIn a (Metric.ball c 1) : ℝ) ≤ 2 ^ n / Real.sqrt n := h
    _ = 1 / Real.log 2 * 2 ^ n / Real.sqrt n * Real.log 2 := by field_simp
    _ ≤ _ := by gcongr

lemma card_signs_pos_eq (n p : ℕ) :
    #{ε : Fin n → ℤˣ | #{i | ε i = 1} = p} = n.choose p := by
  classical
  have h := card_powersetCard p (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at h
  rw [← h]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  apply card_nbij' (fun ε => ({i | ε i = 1} : Finset (Fin n)))
    (fun s i => if i ∈ s then 1 else -1)
  · intro ε hε
    simp only [coe_filter, mem_univ, true_and, mem_setOf_iff'] at hε
    simp [mem_powersetCard, hε]
  · intro s hs
    simp only [mem_coe, mem_powersetCard] at hs
    simp only [coe_filter, mem_univ, true_and, mem_setOf_iff']
    convert hs.2 using 2
    ext i; by_cases h : i ∈ s <;> simp [h, hne]
  · intro ε _
    funext i
    rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h, hne]
  · intro s _
    ext i; by_cases h : i ∈ s <;> simp [h, hne]

lemma sum_signs_eq (n : ℕ) (ε : Fin n → ℤˣ) :
    ∑ i, (ε i : ℤ) = 2 * (#{i | ε i = 1} : ℕ) - n := by
  classical
  have : ∀ i, (ε i : ℤ) = 2 * (if ε i = 1 then 1 else 0) - 1 := by
    intro i; rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
  simp_rw [this]
  rw [sum_sub_distrib, ← mul_sum, sum_boole]
  simp

lemma sum_Ico_choose_eq_min (n r t : ℕ) :
    ∑ i ∈ Ico r t, n.choose i = ∑ i ∈ Ico r (min t (n + 1)), n.choose i := by
  symm
  apply sum_subset
  · intro i; simp only [mem_Ico]; omega
  · intro i hi hi'
    simp only [mem_Ico] at hi hi'
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- The bound in Kleitman's theorem is sharp: for `a₁ = ⋯ = aₙ = e` with `‖e‖ = 1` there are `k`
open balls of radius `1` containing exactly as many sums as the sum of the `k` largest binomial
coefficients. -/
theorem kleitman_sharp (e : E) (he : ‖e‖ = 1) (n k : ℕ) :
    ∃ R : Fin k → Set E, (∀ j, ∃ c, R j = Metric.ball c 1) ∧
      numSumsIn (fun _ : Fin n => e) (⋃ j, R j) = sumLargestChoose n k := by
  classical
  set r := (n + 1 - k) / 2 with hr
  refine ⟨fun j => Metric.ball (((2 * (r + (j : ℕ) : ℕ) : ℤ) - n) • e) 1, fun j => ⟨_, rfl⟩, ?_⟩
  have key : ∀ m : ℤ, ‖(m : ℝ)‖ < 1 ↔ m = 0 := by
    intro m
    rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff]
  have hmem : ∀ ε : Fin n → ℤˣ, (∑ i, (ε i : ℤ) • (fun _ : Fin n => e) i ∈
      ⋃ j : Fin k, Metric.ball (((2 * (r + (j : ℕ) : ℕ) : ℤ) - n) • e) 1) ↔
      #{i | ε i = 1} ∈ Ico r (r + k) := by
    intro ε
    rw [← sum_smul, sum_signs_eq]
    simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm, ← sub_smul, norm_zsmul ℝ, he,
      mul_one, key, mem_Ico]
    constructor
    · rintro ⟨j, hj⟩
      have := j.isLt
      omega
    · intro h
      exact ⟨⟨#{i | ε i = 1} - r, by omega⟩, by simp only; omega⟩
  unfold numSumsIn
  rw [filter_congr (fun ε _ => hmem ε)]
  rw [card_eq_sum_card_fiberwise (f := fun ε : Fin n → ℤˣ => #{i | ε i = 1})
    (t := Ico r (r + k)) (by intro ε hε; simpa using hε)]
  have hfib : ∀ p ∈ Ico r (r + k), #{ε ∈ ({ε : Fin n → ℤˣ | #{i | ε i = 1} ∈ Ico r (r + k)} :
      Finset _) | #{i | ε i = 1} = p} = n.choose p := by
    intro p hp
    rw [filter_filter, ← card_signs_pos_eq n p]
    congr 1
    apply filter_congr
    intro ε _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hp, h⟩
  rw [sum_congr rfl hfib, sumLargestChoose_eq_middleChooseSum, middleChooseSum,
    sum_Ico_choose_eq_min, sum_Ico_choose_eq_min n _ ((n + k + 1) / 2)]
  congr 2
  omega

end LittlewoodOfford
