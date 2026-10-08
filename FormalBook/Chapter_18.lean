module

public import Mathlib

/-!
# Chapter 18: Borsuk's conjecture
Single-file consolidation and repair of the supplied development.
Checked with Lean 4.35.0-rc3 and Mathlib commit
25730c7c759d108ef87ab70af2342a196760f79d.
Source: Aigner and Ziegler, Proofs from THE BOOK, Chapter 18 (2018), pp. 117–123.
No proof placeholders or new axioms are introduced.
The all-dimensions 1.2 bound remains explicitly conditional.
The 560-dimensional refinement and introductory survey results are not proved here.
-/

set_option maxHeartbeats 2000000


/-! ## Defs -/

@[expose] public section

open Metric

namespace Borsuk

/-- `S` admits a partition into (at most) `k` parts, each of smaller diameter than `S`. -/
def HasDiamReducingPartition {X : Type*} [PseudoMetricSpace X] (S : Set X) (k : ℕ) : Prop :=
  ∃ c : X → Fin k, ∀ i, diam (S ∩ c ⁻¹' {i}) < diam S

/-- **Borsuk's conjecture** in dimension `d`: every bounded set `S ⊆ ℝᵈ` with `diam S > 0`
can be partitioned into at most `d + 1` sets of smaller diameter. -/
def BorsukConjecture (d : ℕ) : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded S → 0 < diam S →
    HasDiamReducingPartition S (d + 1)

/-- The book's `f(d)`: the smallest number `k` such that every bounded set `S ⊆ ℝᵈ` with
`diam S > 0` has a diameter-reducing partition into `k` parts. -/
noncomputable def borsukNumber (d : ℕ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∀ S : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded S → 0 < diam S →
    HasDiamReducingPartition S k), (k : ℕ∞)

/-- A single bounded set with positive diameter needing `≥ N` parts gives `f(d) ≥ N`. -/
theorem le_borsukNumber {d N : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded S) (hd : 0 < diam S)
    (h : ∀ k, HasDiamReducingPartition S k → N ≤ k) : (N : ℕ∞) ≤ borsukNumber d :=
  le_iInf₂ fun k hk => Nat.cast_le.2 (h k (hk S hb hd))

/-- Borsuk's conjecture in dimension `d` holds iff `f(d) ≤ d + 1`. -/
theorem borsukConjecture_iff (d : ℕ) : BorsukConjecture d ↔ borsukNumber d ≤ d + 1 := by
  constructor
  · intro h
    exact iInf₂_le (d + 1) h
  · intro h S hb hd
    by_contra hS
    have : ((d + 2 : ℕ) : ℕ∞) ≤ borsukNumber d := by
      refine le_borsukNumber hb hd fun k hk => ?_
      by_contra hk'
      apply hS
      obtain ⟨c, hc⟩ := hk
      refine ⟨fun x => Fin.castLE (by omega) (c x), fun i => ?_⟩
      by_cases hi : (i : ℕ) < k
      · have : S ∩ (fun x => Fin.castLE (by omega) (c x)) ⁻¹' {i} =
            S ∩ c ⁻¹' {⟨i, hi⟩} := by
          ext x; simp [Fin.ext_iff]
        rw [this]; exact hc _
      · have : S ∩ (fun x => Fin.castLE (by omega) (c x) : _ → Fin (d + 1)) ⁻¹' {i} = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro _ h'
          rw [Fin.ext_iff] at h'
          simp only [Fin.val_castLE] at h'
          exact hi (h' ▸ (c x).2)
        rw [this, diam_empty]; exact hd
    have h2 := this.trans h
    norm_cast at h2
    omega

/-- A counterexample set refutes Borsuk's conjecture in dimension `d`. -/
theorem not_borsukConjecture_of {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded S) (hd : 0 < diam S)
    (h : ∀ k, HasDiamReducingPartition S k → d + 1 < k) : ¬ BorsukConjecture d :=
  fun hB => (h (d + 1) (hB S hb hd)).false

/-! ### Equilateral sets -/

/-- If `v : Fin N → X` (with `N ≥ 2`) has all mutual distances equal to `r > 0`, then the set
`S = range v` satisfies `diam S = r`, and every diameter-reducing partition of `S` has at least
`N` parts (no part can contain two of the points). -/
theorem equilateral_partition_bound {X : Type*} [MetricSpace X] {N : ℕ} (hN : 2 ≤ N)
    (v : Fin N → X) {r : ℝ} (hr : 0 < r) (hv : ∀ i j, i ≠ j → dist (v i) (v j) = r) :
    Bornology.IsBounded (Set.range v) ∧ diam (Set.range v) = r ∧
      ∀ k, HasDiamReducingPartition (Set.range v) k → N ≤ k := by
  have hb : Bornology.IsBounded (Set.range v) := (Set.finite_range v).isBounded
  have hdiam : diam (Set.range v) = r := by
    apply le_antisymm
    · apply diam_le_of_forall_dist_le hr.le
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      by_cases h : i = j
      · subst h; simp [hr.le]
      · exact (hv i j h).le
    · have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      rw [← hv _ _ h01]
      exact dist_le_diam_of_mem hb ⟨_, rfl⟩ ⟨_, rfl⟩
  refine ⟨hb, hdiam, fun k ⟨c, hc⟩ => ?_⟩
  have hinj : Function.Injective (c ∘ v) := by
    intro i j hij
    by_contra h
    have hbi : Bornology.IsBounded (Set.range v ∩ c ⁻¹' {c (v i)}) :=
      hb.subset Set.inter_subset_left
    have h1 : dist (v i) (v j) ≤ diam (Set.range v ∩ c ⁻¹' {c (v i)}) :=
      dist_le_diam_of_mem hbi ⟨⟨i, rfl⟩, rfl⟩ ⟨⟨j, rfl⟩, by simp [Function.comp] at hij; simp [hij]⟩
    have h2 := hc (c (v i))
    rw [hv i j h, hdiam] at *
    linarith
  simpa using Fintype.card_le_of_injective _ hinj

/-- The vertices of a regular simplex in `ℝᵈ` (`d ≥ 1`): `e₁, …, e_d` and `t·(1, …, 1)` with
`t = (1 + √(d+1)) / d`.  All mutual distances equal `√2`. -/
noncomputable def simplexVertex (d : ℕ) (i : Fin (d + 1)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j => if i = Fin.last d then (1 + Real.sqrt (d + 1)) / d
    else if j.castSucc = i then 1 else 0

theorem sum_ite_eq_fin {d : ℕ} (hd : 1 ≤ d) (a : Fin d) (A B : ℝ) :
    ∑ x : Fin d, (if x = a then A else B) = A + (d - 1) * B := by
  rw [Finset.sum_ite, Finset.filter_eq', ite_eq_left (Finset.mem_univ _), Finset.filter_ne',
    Finset.sum_singleton, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hd, Nat.cast_one]

theorem simplexVertex_dist (d : ℕ) (hd : 1 ≤ d) (i j : Fin (d + 1)) (hij : i ≠ j) :
    dist (simplexVertex d i) (simplexVertex d j) = Real.sqrt 2 := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp only [simplexVertex, Real.dist_eq, sq_abs, PiLp.toLp_apply]
  set t : ℝ := (1 + Real.sqrt (d + 1)) / d with ht
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt (d + 1) ^ 2 = d + 1 := Real.sq_sqrt (by positivity)
  have key : (t - 1) ^ 2 + (d - 1) * t ^ 2 = 2 := by
    have : (d : ℝ) * t ^ 2 - 2 * t = 1 := by
      rw [ht]; field_simp; nlinarith [hs]
    nlinarith
  have hcs : ∀ (x b : Fin d), (x.castSucc = b.castSucc) ↔ x = b := fun x b =>
    Fin.castSucc_inj
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact absurd rfl hij
    | cast b =>
      simp only [ite_true, Fin.castSucc_ne_last, ite_false, hcs]
      rw [Finset.sum_congr rfl (fun x _ => show (t - if x = b then 1 else 0) ^ 2 =
        (if x = b then (t - 1) ^ 2 else t ^ 2) by split_ifs <;> simp)]
      rw [sum_ite_eq_fin hd]; linarith
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [ite_true, Fin.castSucc_ne_last, ite_false, hcs]
      rw [Finset.sum_congr rfl (fun x _ => show ((if x = a then 1 else 0) - t) ^ 2 =
        (if x = a then (t - 1) ^ 2 else t ^ 2) by split_ifs <;> ring)]
      rw [sum_ite_eq_fin hd]; linarith
    | cast b =>
      have hab : a ≠ b := fun h => hij (h ▸ rfl)
      simp only [Fin.castSucc_ne_last, ite_false, hcs]
      rw [Finset.sum_congr rfl (fun x _ => show
        ((if x = a then (1 : ℝ) else 0) - (if x = b then 1 else 0)) ^ 2 =
        (if x = a then 1 else 0) + (if x = b then 1 else 0) by
          by_cases h1 : x = a <;> by_cases h2 : x = b
          · exact absurd (h1.symm.trans h2) hab
          · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
          · rw [ite_eq_right h1, ite_eq_left h2]; norm_num
          · rw [ite_eq_right h1, ite_eq_right h2]; norm_num)]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp; norm_num

theorem simplexVertex_injective (d : ℕ) (hd : 1 ≤ d) : Function.Injective (simplexVertex d) := by
  intro i j h
  by_contra hij
  have := simplexVertex_dist d hd i j hij
  rw [h, dist_self] at this
  exact absurd this.symm (by positivity)

/-- **The regular simplex shows `f(d) ≥ d + 1`.**  The `d + 1` vertices of a regular simplex
in `ℝᵈ` (`d ≥ 1`) form a bounded set of positive diameter, no diameter-reducing partition of
which has fewer than `d + 1` parts. -/
theorem simplex_lower_bound (d : ℕ) (hd : 1 ≤ d) :
    let S := Set.range (simplexVertex d)
    Bornology.IsBounded S ∧ 0 < diam S ∧ ∀ k, HasDiamReducingPartition S k → d + 1 ≤ k := by
  obtain ⟨h1, h2, h3⟩ := equilateral_partition_bound (by omega) (simplexVertex d)
    (by positivity : (0 : ℝ) < Real.sqrt 2) (simplexVertex_dist d hd)
  exact ⟨h1, h2 ▸ by positivity, h3⟩

/-- `f(d) ≥ d + 1` for every `d ≥ 1`. -/
theorem succ_le_borsukNumber (d : ℕ) (hd : 1 ≤ d) : ((d + 1 : ℕ) : ℕ∞) ≤ borsukNumber d := by
  obtain ⟨h1, h2, h3⟩ := simplex_lower_bound d hd
  exact le_borsukNumber h1 h2 h3

/-! ### Monotonicity: lower bounds transfer to higher dimensions -/

/-- The standard isometric embedding `ℝᵈ → ℝ^{d'}` for `d ≤ d'` (pad with zeros). -/
noncomputable def padEmb (d d' : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d') :=
  WithLp.toLp 2 fun j => if h : (j : ℕ) < d then x ⟨j, h⟩ else 0

theorem padEmb_isometry {d d' : ℕ} (hdd : d ≤ d') : Isometry (padEmb d d') := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdd
  apply Isometry.of_dist_eq
  intro x y
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [padEmb, PiLp.toLp_apply, Real.dist_eq, sq_abs]
  have : ∀ j : Fin (d + e), ((if h : (j : ℕ) < d then x ⟨j, h⟩ else 0) -
      (if h : (j : ℕ) < d then y ⟨j, h⟩ else 0)) ^ 2 =
      if h : (j : ℕ) < d then (x ⟨j, h⟩ - y ⟨j, h⟩) ^ 2 else 0 := by
    intro j; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => this j), Fin.sum_univ_add]
  simp

/-- A diameter-reducing partition of an isometric image pulls back. -/
theorem HasDiamReducingPartition.of_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Isometry f) {S : Set X} {k : ℕ}
    (h : HasDiamReducingPartition (f '' S) k) : HasDiamReducingPartition S k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c ∘ f, fun i => ?_⟩
  have := hc i
  rw [← Set.image_inter_preimage, hf.diam_image, hf.diam_image] at this
  exact this

/-- Lower bounds for the Borsuk problem transfer from dimension `d` to any `d' ≥ d`. -/
theorem lowerBound_mono {d d' N : ℕ} (hdd : d ≤ d') {S : Set (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded S) (hd : 0 < diam S)
    (h : ∀ k, HasDiamReducingPartition S k → N ≤ k) :
    ∃ S' : Set (EuclideanSpace ℝ (Fin d')), Bornology.IsBounded S' ∧ 0 < diam S' ∧
      ∀ k, HasDiamReducingPartition S' k → N ≤ k := by
  have hf := padEmb_isometry hdd
  refine ⟨padEmb d d' '' S, hf.lipschitzWith.isBounded_image hb, by rwa [hf.diam_image],
    fun k hk => h k (hk.of_isometry hf)⟩

/-- `f(d)` is monotone: `f(d) ≤ f(d')` for `d ≤ d'`. -/
theorem borsukNumber_mono {d d' : ℕ} (hdd : d ≤ d') : borsukNumber d ≤ borsukNumber d' := by
  have hf := padEmb_isometry hdd
  refine le_iInf₂ fun k hk => iInf₂_le k fun S hb hd => ?_
  exact (hk _ (hf.lipschitzWith.isBounded_image hb) (by rwa [hf.diam_image])).of_isometry hf

end Borsuk

end


/-! ## Binomial -/

@[expose] public section
open Polynomial Finset
namespace Borsuk
/-- Lower base-p digits are unchanged by reduction modulo p^m. -/
theorem digit_mod_pow (p m N i : ℕ) (hi : i < m) : N % p ^ m / p ^ i % p = N / p ^ i % p := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow p hi)]
theorem choose_modEq_choose_mod_primePow {p : ℕ} [Fact p.Prime] (m N K : ℕ) (hK : K < p ^ m) :
    (N.choose K : ℤ) ≡ ((N % p ^ m).choose K : ℤ) [ZMOD p] := by
  have h1 := Choose.choose_modEq_choose_mul_prod_range_choose (n := N) (k := K) (p := p) m
  have h2 := Choose.choose_modEq_choose_mul_prod_range_choose (n := N % p ^ m) (k := K) (p := p) m
  have hp : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  rw [Nat.div_eq_of_lt hK] at h1 h2
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ hp)] at h2
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1 h2
  refine h1.trans (h2.trans ?_).symm
  rw [prod_congr rfl (fun i hi => by rw [digit_mod_pow p m N i (mem_range.1 hi)])]
theorem dvd_choose_iff {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (N : ℕ) :
    (p : ℤ) ∣ (N.choose (p ^ m - 2) : ℤ) ↔ ¬ (p ^ m ∣ N + 2 ∨ p ^ m ∣ N + 1) := by
  have := Fact.mk hp
  set q := p ^ m with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ q := Nat.pow_le_pow_right hp.pos hm
  have hpq : p ∣ q := dvd_pow_self p hm.ne'
  rw [(choose_modEq_choose_mod_primePow m N (q - 2) (by omega)).dvd_iff]
  have hN := Nat.div_add_mod N q
  set r := N % q
  have hr : r < q := Nat.mod_lt _ (by omega)
  have e2 : q ∣ N + 2 ↔ q ∣ r + 2 := by
    rw [← hN, add_assoc]; exact (Nat.dvd_add_right (dvd_mul_right q _))
  have e1 : q ∣ N + 1 ↔ q ∣ r + 1 := by
    rw [← hN, add_assoc]; exact (Nat.dvd_add_right (dvd_mul_right q _))
  rw [e1, e2]
  have hnot : ¬ (p : ℤ) ∣ 1 := by
    rw [Int.natCast_dvd_ofNat]; exact hp.not_dvd_one
  rcases lt_trichotomy r (q - 2) with h | h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp only [Nat.cast_zero, dvd_zero, true_iff]
    rintro (h' | h') <;> have := Nat.le_of_dvd (by omega) h' <;> omega
  · rw [h, Nat.choose_self, Nat.cast_one]
    simp only [hnot, false_iff, not_not]
    left; rw [show q - 2 + 2 = q by omega]
  · have hr' : r = q - 1 := by omega
    rw [hr', Nat.choose_symm_of_eq_add (show q - 1 = (q - 2) + 1 by omega), Nat.choose_one_right]
    simp only [show q - 1 + 1 = q by omega, dvd_refl, or_true, not_true_eq_false, iff_false]
    intro hd
    have : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpq
    have h3 := dvd_sub this hd
    rw [Nat.cast_sub (by omega)] at h3
    simp at h3
    exact hnot (by simpa using h3)
/-- Divisibility part of the chapter's polynomial lemma, for every integer z. -/
theorem lemma_P_dvd_iff {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (z : ℤ) :
    (p : ℤ) ∣ Ring.choose (z - 2) (p ^ m - 2) ↔
      ¬ (z ≡ 0 [ZMOD (p ^ m : ℕ)] ∨ z ≡ 1 [ZMOD (p ^ m : ℕ)]) := by
  have hq2 : 2 ≤ p ^ m := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  simp only [Int.modEq_iff_dvd]
  rcases le_or_gt 2 z with hz | hz
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, z - 2 = N := ⟨(z - 2).toNat, by omega⟩
    rw [hN, Ring.choose_natCast, dvd_choose_iff hp hm]
    have a1 : z = (N : ℤ) + 2 := by omega
    subst a1
    rw [← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast]
    push_cast
    constructor <;> rintro h1 (h2 | h2) <;> apply h1
    · left; rw [← dvd_neg]; convert h2 using 1; ring
    · right; rw [← dvd_neg]; convert h2 using 1; ring
    · left; rw [← dvd_neg]; convert h2 using 1; ring
    · right; rw [← dvd_neg]; convert h2 using 1; ring
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, z - 2 = -(M : ℤ) := ⟨(2 - z).toNat, by omega⟩
    rw [hM, Ring.choose_neg]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (M : ℤ) + ((p ^ m - 2 : ℕ) : ℤ) - 1 = N :=
      ⟨M + (p ^ m - 2) - 1, by omega⟩
    rw [hN, Ring.choose_natCast, Units.smul_def, smul_eq_mul, Units.dvd_mul_left,
      dvd_choose_iff hp hm]
    rw [← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast]
    have e1 : ((N + 2 : ℕ) : ℤ) = (p ^ m : ℕ) + (1 - z) := by omega
    have e2 : ((N + 1 : ℕ) : ℤ) = (p ^ m : ℕ) + (0 - z) := by omega
    rw [e1, e2, dvd_add_right (dvd_refl _), dvd_add_right (dvd_refl _), or_comm]
/-- The chapter's polynomial `P(z) = (z - 2)(z - 3) ⋯ (z - (q - 1)) / (q - 2)!`. -/
noncomputable def bookP (q : ℕ) : ℚ[X] :=
  (((q - 2).factorial : ℚ)⁻¹) • (descPochhammer ℚ (q - 2)).comp (X - C 2)
theorem bookP_natDegree (q : ℕ) : (bookP q).natDegree = q - 2 := by
  unfold bookP
  rw [natDegree_smul _ (inv_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')),
    natDegree_comp, descPochhammer_natDegree, natDegree_X_sub_C, mul_one]
theorem descPochhammer_eval_intCast (k : ℕ) (r : ℤ) :
    (descPochhammer ℚ k).eval (r : ℚ) = (k.factorial * Ring.choose r k : ℤ) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose r k
  rw [← Polynomial.eval_eq_smeval, nsmul_eq_mul] at h1
  rw [← descPochhammer_map (Int.castRingHom ℚ), eval_map, ← h1, eval₂_at_intCast]
  simp
theorem bookP_eval_intCast (q : ℕ) (z : ℤ) :
    (bookP q).eval (z : ℚ) = ((Ring.choose (z - 2) (q - 2) : ℤ) : ℚ) := by
  unfold bookP
  rw [eval_smul, eval_comp, eval_sub, eval_X, eval_C, show (z : ℚ) - 2 = ((z - 2 : ℤ) : ℚ) by
    push_cast; ring, descPochhammer_eval_intCast, smul_eq_mul]
  have : ((q - 2).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [Int.cast_mul, Int.cast_natCast]
  field_simp
/-- The polynomial is nonzero: it has value one at z = (q-2)+2. -/
theorem bookP_ne_zero (q : ℕ) : bookP q ≠ 0 := by
  have he := bookP_eval_intCast q (((q - 2 : ℕ) : ℤ) + 2)
  simp only [add_sub_cancel_right, Ring.choose_natCast, Nat.choose_self,
    Nat.cast_one, Int.cast_one] at he
  intro h
  rw [h, Polynomial.eval_zero] at he
  exact zero_ne_one he

/-- The degree claim includes nonvanishing, including the constant case q = 2. -/
theorem bookP_degree (q : ℕ) : (bookP q).degree = (q - 2 : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (bookP_ne_zero q), bookP_natDegree]

end Borsuk
end


/-! ## Claims -/

@[expose] public section

open Finset Polynomial

namespace Borsuk

variable {n : ℕ} [NeZero n]

/-- The set `Q ⊆ {+1,-1}ⁿ` of the book: first coordinate `1`, an even number of `-1`'s. -/
def Q (n : ℕ) [NeZero n] : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ => ({1, -1} : Finset ℤ)).filter
    (fun x => x 0 = 1 ∧ Even (univ.filter (fun i => x i = -1)).card)

/-- Two vectors are *nearly orthogonal* if `|⟨x, y⟩| = 2`. -/
def NearlyOrthogonal (x y : Fin n → ℤ) : Prop := |x ⬝ᵥ y| = 2

theorem mem_Q {x : Fin n → ℤ} :
    x ∈ Q n ↔ (∀ i, x i = 1 ∨ x i = -1) ∧ x 0 = 1 ∧
      Even (univ.filter (fun i => x i = -1)).card := by
  simp [Q, Fintype.mem_piFinset]

/-- The number of coordinates in which `x` and `y` differ. -/
def hammingDist' (x y : Fin n → ℤ) : ℕ := (univ.filter (fun i => x i ≠ y i)).card

omit [NeZero n] in
theorem prod_pm_one {x : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1) :
    ∏ i, x i = (-1) ^ (univ.filter (fun i => x i = -1)).card := by
  rw [← prod_filter_mul_prod_filter_not univ (fun i => x i = -1)]
  rw [prod_congr rfl (fun i hi => (mem_filter.1 hi).2), prod_const,
    prod_congr rfl (fun i hi => ((hx i).resolve_right (mem_filter.1 hi).2)), prod_const_one,
    mul_one]

theorem prod_eq_one_of_mem_Q {x : Fin n → ℤ} (hx : x ∈ Q n) : ∏ i, x i = 1 := by
  rw [mem_Q] at hx
  rw [prod_pm_one hx.1, hx.2.2.neg_one_pow]

omit [NeZero n] in
theorem dotProduct_eq_of_pm {x y : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    x ⬝ᵥ y = n - 2 * (hammingDist' x y : ℤ) := by
  have : ∀ i, x i * y i = 1 - 2 * (if x i ≠ y i then 1 else 0) := by
    intro i; rcases hx i with h | h <;> rcases hy i with h' | h' <;> simp [h, h']
  simp only [dotProduct, this, sum_sub_distrib, ← mul_sum, sum_boole, hammingDist']
  simp

omit [NeZero n] in
theorem prod_mul_eq_of_pm {x y : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    ∏ i, (x i * y i) = (-1) ^ hammingDist' x y := by
  have : ∀ i, x i * y i = if x i ≠ y i then -1 else 1 := by
    intro i; rcases hx i with h | h <;> rcases hy i with h' | h' <;> simp [h, h']
  simp only [this, prod_ite, prod_const, one_pow, mul_one, hammingDist']

theorem even_hammingDist {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n) :
    Even (hammingDist' x y) := by
  have h := prod_mul_eq_of_pm (mem_Q.1 hx).1 (mem_Q.1 hy).1
  rw [prod_mul_distrib, prod_eq_one_of_mem_Q hx, prod_eq_one_of_mem_Q hy, one_mul] at h
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h.symm

omit [NeZero n] in
theorem hammingDist_pos {x y : Fin n → ℤ} (hxy : x ≠ y) : 0 < hammingDist' x y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  exact card_pos.2 ⟨i, by simp [hi]⟩

theorem hammingDist_lt {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n) :
    hammingDist' x y < n := by
  have h0 : (0 : Fin n) ∉ univ.filter (fun i => x i ≠ y i) := by
    simp [(mem_Q.1 hx).2.1, (mem_Q.1 hy).2.1]
  calc hammingDist' x y < (univ : Finset (Fin n)).card :=
        card_lt_card ⟨subset_univ _, fun h => h0 (h (mem_univ _))⟩
    _ = n := by simp

/-- For `x, y ∈ Q` and `n = 4q - 2`, `⟨x, y⟩ + 2 = 4 (q - e)` where `2e` is the number of
coordinates in which `x` and `y` differ. -/
theorem dotProduct_add_two {q : ℕ} (hn : n = 4 * q - 2) {x y : Fin n → ℤ} (hx : x ∈ Q n)
    (hy : y ∈ Q n) :
    x ⬝ᵥ y + 2 = 4 * ((q : ℤ) - (hammingDist' x y / 2 : ℕ)) := by
  rw [dotProduct_eq_of_pm (mem_Q.1 hx).1 (mem_Q.1 hy).1]
  obtain ⟨e, he⟩ := even_hammingDist hx hy
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [he, show (e + e) / 2 = e by omega]
  push_cast
  have : (n : ℤ) = 4 * q - 2 := by omega
  rw [this]; ring

/-- **Claim 1.** If `x, y ∈ Q` are distinct, then `¼(⟨x, y⟩ + 2)` is an integer `k` with
`-(q - 2) ≤ k ≤ q - 1`. -/
theorem claim1 {q : ℕ} (hn : n = 4 * q - 2) {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n)
    (hxy : x ≠ y) :
    ∃ k : ℤ, x ⬝ᵥ y + 2 = 4 * k ∧ -((q : ℤ) - 2) ≤ k ∧ k ≤ (q : ℤ) - 1 := by
  refine ⟨(q : ℤ) - (hammingDist' x y / 2 : ℕ), dotProduct_add_two hn hx hy, ?_⟩
  have h1 := hammingDist_pos hxy
  have h2 := hammingDist_lt hx hy
  obtain ⟨e, he⟩ := even_hammingDist hx hy
  rw [he] at h1 h2 ⊢
  rw [show (e + e) / 2 = e by omega]
  omega

/-- The integer `F_y(x) = P(¼(⟨x, y⟩ + 2)) = C(¼(⟨x, y⟩ + 2) - 2, q - 2)` of Claim 2. -/
def F (q : ℕ) (y x : Fin n → ℤ) : ℤ := Ring.choose ((x ⬝ᵥ y + 2) / 4 - 2) (q - 2)

omit [NeZero n] in
theorem hammingDist_self (x : Fin n → ℤ) : hammingDist' x x = 0 := by
  simp [hammingDist']

theorem F_self {q : ℕ} (hn : n = 4 * q - 2) (hq : 2 ≤ q) {y : Fin n → ℤ} (hy : y ∈ Q n) :
    F q y y = 1 := by
  unfold F
  rw [dotProduct_add_two hn hy hy, hammingDist_self]
  simp only [Nat.zero_div, Nat.cast_zero, sub_zero]
  rw [Int.mul_ediv_cancel_left _ (by norm_num), show (q : ℤ) - 2 = ((q - 2 : ℕ) : ℤ) by omega,
    Ring.choose_natCast, Nat.choose_self, Nat.cast_one]

/-- **Claim 2.** Let `q = p ^ m` (`m ≥ 1`), `n = 4q - 2`, and let `Q' ⊆ Q` contain no
nearly-orthogonal pair.  For `y ∈ Q'`, the integer `F_y(x)` is divisible by `p` for every
`x ∈ Q' \ {y}`, but not for `x = y` (indeed `F_y(y) = 1`). -/
theorem claim2 {p m q : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m) (hn : n = 4 * q - 2)
    {Q' : Finset (Fin n → ℤ)} (hQ'Q : Q' ⊆ Q n)
    (hQ' : ∀ x ∈ Q', ∀ y ∈ Q', ¬ NearlyOrthogonal x y) {y : Fin n → ℤ} (hy : y ∈ Q') :
    (∀ x ∈ Q', x ≠ y → (p : ℤ) ∣ F q y x) ∧ ¬ (p : ℤ) ∣ F q y y := by
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  refine ⟨fun x hx hxy => ?_, ?_⟩
  · obtain ⟨k, hk, hk1, hk2⟩ := claim1 hn (hQ'Q hx) (hQ'Q hy) hxy
    unfold F
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num), hq, lemma_P_dvd_iff hp hm, ← hq]
    have hno := hQ' x hx y hy
    unfold NearlyOrthogonal at hno
    rintro (h | h)
    · have : k = 0 := Int.eq_zero_of_abs_lt_dvd (Int.ModEq.dvd h.symm |>.trans (by simp))
        (by rw [abs_lt]; omega)
      apply hno; rw [show x ⬝ᵥ y = -2 by omega]; norm_num
    · have : k - 1 = 0 := Int.eq_zero_of_abs_lt_dvd (by simpa using (Int.ModEq.dvd h.symm))
        (by rw [abs_lt]; omega)
      apply hno; rw [show x ⬝ᵥ y = 2 by omega]; norm_num
  · rw [F_self hn hq2 (hQ'Q hy)]
    rw [Int.natCast_dvd_ofNat]; exact hp.not_dvd_one

/-! ### Claim 3: reduction to squarefree polynomials in `x₂, …, xₙ` -/

/-- The squarefree monomial `∏_{i ∈ S} xᵢ`, as a (rational-valued) function on `Q`. -/
def monoFun (S : Finset (Fin n)) : ↥(Q n) → ℚ := fun x => ∏ i ∈ S, ((x : Fin n → ℤ) i : ℚ)

/-- The squarefree monomials of degree `≤ k` in the variables `x₂, …, xₙ`, indexed by their
sets of variables: subsets of `Fin n \ {0}` with at most `k` elements. -/
def monoIdx (n k : ℕ) [NeZero n] : Finset (Finset (Fin n)) :=
  (univ.erase (0 : Fin n)).powerset.filter (fun S => S.card ≤ k)

/-- The space of functions on `Q` given by squarefree polynomials of degree `≤ k` in
`x₂, …, xₙ`. -/
def W (n k : ℕ) [NeZero n] : Submodule ℚ (↥(Q n) → ℚ) :=
  Submodule.span ℚ (monoFun '' (monoIdx n k : Set (Finset (Fin n))))

theorem W_mono {k k' : ℕ} (h : k ≤ k') : W n k ≤ W n k' := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro S hS
  simp only [monoIdx, coe_filter, Set.mem_ofPred_eq] at hS ⊢
  exact ⟨hS.1, hS.2.trans h⟩

theorem one_mem_W : (1 : ↥(Q n) → ℚ) ∈ W n 0 := by
  apply Submodule.subset_span
  refine ⟨∅, by simp [monoIdx], ?_⟩
  ext x; simp [monoFun]

theorem mul_coord_mem_W {k : ℕ} {f : ↥(Q n) → ℚ} (hf : f ∈ W n k) (i : Fin n) :
    (fun x : ↥(Q n) => f x * ((x : Fin n → ℤ) i : ℚ)) ∈ W n (k + 1) := by
  let c : ↥(Q n) → ℚ := fun x => ((x : Fin n → ℤ) i : ℚ)
  let L : (↥(Q n) → ℚ) →ₗ[ℚ] (↥(Q n) → ℚ) := LinearMap.mulRight ℚ c
  change L f ∈ W n (k + 1)
  suffices W n k ≤ (W n (k + 1)).comap L from this hf
  rw [W, Submodule.span_le]
  rintro _ ⟨S, hS, rfl⟩
  simp only [monoIdx, coe_filter, Set.mem_ofPred_eq, mem_powerset] at hS
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  have hsq : ∀ x : ↥(Q n), ((x : Fin n → ℤ) i : ℚ) * ((x : Fin n → ℤ) i : ℚ) = 1 := by
    intro x
    rcases (mem_Q.1 x.2).1 i with h | h <;> simp [h]
  by_cases hi0 : i = 0
  · have : L (monoFun S) = monoFun S := by
      ext x
      simp [L, c, LinearMap.mulRight_apply, hi0, (mem_Q.1 x.2).2.1, monoFun]
    rw [this]
    exact W_mono (Nat.le_succ k) (Submodule.subset_span ⟨S, by simp [monoIdx, hS.1, hS.2], rfl⟩)
  by_cases hiS : i ∈ S
  · have : L (monoFun S) = monoFun (S.erase i) := by
      ext x
      simp only [L, c, LinearMap.mulRight_apply, monoFun, Pi.mul_apply]
      rw [← mul_prod_erase S _ hiS, mul_comm, ← mul_assoc, hsq, one_mul]
    rw [this]
    apply Submodule.subset_span
    refine ⟨S.erase i, ?_, rfl⟩
    simp only [monoIdx, coe_filter, Set.mem_ofPred_eq, mem_powerset]
    exact ⟨(erase_subset _ _).trans hS.1, by rw [card_erase_of_mem hiS]; omega⟩
  · have : L (monoFun S) = monoFun (insert i S) := by
      ext x
      simp only [L, c, LinearMap.mulRight_apply, monoFun, Pi.mul_apply]
      rw [prod_insert hiS, mul_comm]
    rw [this]
    apply Submodule.subset_span
    refine ⟨insert i S, ?_, rfl⟩
    simp only [monoIdx, coe_filter, Set.mem_ofPred_eq, mem_powerset]
    refine ⟨insert_subset (by simp [hi0]) hS.1, by rw [card_insert_of_notMem hiS]; omega⟩

theorem dot_pow_mem_W (y : Fin n → ℤ) (j : ℕ) :
    (fun x : ↥(Q n) => (((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) ^ j) ∈ W n j := by
  induction j with
  | zero => simpa only [pow_zero, Pi.one_def] using (one_mem_W (n := n))
  | succ j ih =>
    have : (fun x : ↥(Q n) => (((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) ^ (j + 1)) =
        ∑ i, (y i : ℚ) • (fun x : ↥(Q n) =>
          (((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) ^ j * ((x : Fin n → ℤ) i : ℚ)) := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
      simp_rw [mul_left_comm _ (_ ^ j)]
      rw [← mul_sum]
      congr 1
      simp only [dotProduct]; push_cast
      exact sum_congr rfl (fun i _ => mul_comm _ _)
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (mul_coord_mem_W ih i))

/-- On `Q`, `F_y(x)` is the value of the book's polynomial `P` at `¼(⟨x, y⟩ + 2)`. -/
theorem F_eq_eval {q : ℕ} (hn : n = 4 * q - 2) {x y : Fin n → ℤ} (hx : x ∈ Q n)
    (hy : y ∈ Q n) :
    (F q y x : ℚ) = (bookP q).eval ((((x ⬝ᵥ y : ℤ) : ℚ) + 2) / 4) := by
  have h := dotProduct_add_two hn hx hy
  set k : ℤ := (q : ℤ) - (hammingDist' x y / 2 : ℕ)
  unfold F
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num),
    show (((x ⬝ᵥ y : ℤ) : ℚ) + 2) / 4 = ((k : ℤ) : ℚ) by
      rw [show ((x ⬝ᵥ y : ℤ) : ℚ) + 2 = ((x ⬝ᵥ y + 2 : ℤ) : ℚ) by push_cast; ring, h]
      push_cast; ring,
    bookP_eval_intCast]

/-- The function `x ↦ F_y(x)` on `Q` is given by a squarefree polynomial of degree `≤ q - 2`
in `x₂, …, xₙ`. -/
theorem F_mem_W {q : ℕ} (hn : n = 4 * q - 2) {y : Fin n → ℤ} (hy : y ∈ Q n) :
    (fun x : ↥(Q n) => (F q y (x : Fin n → ℤ) : ℚ)) ∈ W n (q - 2) := by
  set R : ℚ[X] := (bookP q).comp (C (1 / 4 : ℚ) * (X + C 2))
  have hR : R.natDegree < q - 2 + 1 := by
    have h1 : R.natDegree ≤ (bookP q).natDegree * (C (1 / 4 : ℚ) * (X + C 2)).natDegree :=
      natDegree_comp_le
    have h2 : (C (1 / 4 : ℚ) * (X + C 2)).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (natDegree_X_add_C (2 : ℚ)).le
    rw [bookP_natDegree] at h1
    have : R.natDegree ≤ q - 2 := h1.trans ((Nat.mul_le_mul_left _ h2).trans (mul_one _).le)
    omega
  have : (fun x : ↥(Q n) => (F q y (x : Fin n → ℤ) : ℚ)) =
      ∑ j ∈ range (q - 2 + 1), R.coeff j •
        (fun x : ↥(Q n) => (((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) ^ j) := by
    ext x
    rw [F_eq_eval hn x.2 hy, Finset.sum_apply]
    have := eval_eq_sum_range' hR (((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ)
    rw [eval_comp] at this
    simp only [eval_mul, eval_C, eval_add, eval_X] at this
    rw [show ((((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) + 2) / 4 =
      1 / 4 * ((((x : Fin n → ℤ) ⬝ᵥ y : ℤ) : ℚ) + 2) by ring, this]
    simp [smul_eq_mul]
  rw [this]
  refine Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _ ?_)
  exact W_mono (by simp at hj; omega) (dot_pow_mem_W y j)

/-- **Claim 3.** For `y ∈ Q` there is a squarefree polynomial `F̄_y` of degree `≤ q - 2` in the
`n - 1` variables `x₂, …, xₙ` — i.e. a rational linear combination of the monomials
`∏_{i ∈ S} xᵢ` with `S ⊆ {x₂,…,xₙ}`, `|S| ≤ q - 2` — which agrees with `F_y` on `Q`. -/
theorem claim3 {q : ℕ} (hn : n = 4 * q - 2) {y : Fin n → ℤ} (hy : y ∈ Q n) :
    ∃ c : Finset (Fin n) → ℚ, ∀ x ∈ Q n,
      (F q y x : ℚ) = ∑ S ∈ monoIdx n (q - 2), c S * ∏ i ∈ S, (x i : ℚ) := by
  have h := F_mem_W hn hy
  rw [W, Fintype.mem_span_image_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨fun S => if hS : S ∈ monoIdx n (q - 2) then c ⟨S, hS⟩ else 0, fun x hx => ?_⟩
  have := congrFun hc ⟨x, hx⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [← this, ← Finset.sum_coe_sort (monoIdx n (q - 2))]
  refine Fintype.sum_congr _ _ (fun S => ?_)
  simp [monoFun]

/-! ### Claims 4 and 5 -/

/-- **Claim 4.** The functions `F̄_y` (`y ∈ Q'`) on `Q` are linearly independent over `ℚ`
(for `Q' ⊆ Q` without nearly-orthogonal pairs).  In particular they are distinct. -/
theorem claim4 {p m q : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m) (hn : n = 4 * q - 2)
    {Q' : Finset (Fin n → ℤ)} (hQ'Q : Q' ⊆ Q n)
    (hQ' : ∀ x ∈ Q', ∀ y ∈ Q', ¬ NearlyOrthogonal x y) :
    LinearIndependent ℚ
      (fun y : ↥Q' => fun x : ↥(Q n) => (F q (y : Fin n → ℤ) (x : Fin n → ℤ) : ℚ)) := by
  have := Fact.mk hp
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  rw [Fintype.linearIndependent_iff]
  intro g hg y0
  let M : Matrix ↥Q' ↥Q' ℤ := fun x y => F q (y : Fin n → ℤ) (x : Fin n → ℤ)
  have hmap : (Int.castRingHom (ZMod p)).mapMatrix M = 1 := by
    ext x y
    change ((F q (y : Fin n → ℤ) (x : Fin n → ℤ) : ℤ) : ZMod p) = if x = y then 1 else 0
    split_ifs with h
    · subst h; rw [F_self hn hq2 (hQ'Q x.2)]; simp
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (claim2 hp hm hq hn hQ'Q hQ' y.2).1 x x.2 (fun h' => h (Subtype.ext h'))
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (Int.castRingHom (ZMod p)) M
    rw [hmap, Matrix.det_one, h0, map_zero] at this
    exact zero_ne_one this
  have hdetQ : ((Int.castRingHom ℚ).mapMatrix M).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa using hdet
  have hmul : ((Int.castRingHom ℚ).mapMatrix M).mulVec g = 0 := by
    ext x
    have := congrFun hg ⟨(x : Fin n → ℤ), hQ'Q x.2⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    change (∑ y : ↥Q', (F q (y : Fin n → ℤ) (x : Fin n → ℤ) : ℚ) * g y) = 0
    rw [← this]
    exact sum_congr rfl (fun _ _ => mul_comm _ _)
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetQ hmul) y0

/-- The number of squarefree monomials of degree `≤ k` in `n - 1` variables is
`∑_{i=0}^{k} C(n-1, i)`. -/
theorem card_monoIdx (k : ℕ) : (monoIdx n k).card = ∑ i ∈ range (k + 1), (n - 1).choose i := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))
    (fun S hS => by
      simp only [monoIdx, coe_filter, Set.mem_ofPred_eq] at hS
      simp only [coe_range, Set.mem_Iio]; omega)]
  refine sum_congr rfl (fun i hi => ?_)
  rw [show (monoIdx n k).filter (fun S => S.card = i) = powersetCard i (univ.erase (0 : Fin n)) by
    ext S
    simp only [monoIdx, mem_filter, mem_powerset, mem_powersetCard]
    simp only [mem_range] at hi
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩]
  rw [card_powersetCard, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- **Claim 5.** Let `q = p ^ m` (`m ≥ 1`) and `n = 4q - 2`.  If `Q' ⊆ Q` contains no two
nearly-orthogonal vectors, then `|Q'| ≤ ∑_{i=0}^{q-2} C(n-1, i)`, the number of squarefree
monomials of degree at most `q - 2` in `n - 1` variables. -/
theorem claim5 {p m q : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m) (hn : n = 4 * q - 2)
    {Q' : Finset (Fin n → ℤ)} (hQ'Q : Q' ⊆ Q n)
    (hQ' : ∀ x ∈ Q', ∀ y ∈ Q', ¬ NearlyOrthogonal x y) :
    Q'.card ≤ ∑ i ∈ range (q - 1), (n - 1).choose i := by
  classical
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  have hli := claim4 hp hm hq hn hQ'Q hQ'
  let w : Finset (↥(Q n) → ℚ) := (monoIdx n (q - 2)).image monoFun
  have hspan : Set.range (fun y : ↥Q' => fun x : ↥(Q n) =>
      (F q (y : Fin n → ℤ) (x : Fin n → ℤ) : ℚ)) ≤ Submodule.span ℚ (w : Set (↥(Q n) → ℚ)) := by
    rintro _ ⟨y, rfl⟩
    have := F_mem_W hn (hQ'Q y.2)
    rw [W] at this
    simpa [w, coe_image] using this
  have h := linearIndependent_le_span' _ hli (w : Set (↥(Q n) → ℚ)) hspan
  rw [Cardinal.mk_fintype, Nat.cast_le] at h
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at h
  calc Q'.card ≤ w.card := h
    _ ≤ (monoIdx n (q - 2)).card := card_image_le
    _ = _ := by rw [card_monoIdx, show q - 2 + 1 = q - 1 by omega]

/-! ### The size of `Q` -/

theorem card_even_powerset {α : Type*} [DecidableEq α] (s : Finset α) {a : α} (ha : a ∈ s) :
    (s.powerset.filter (fun T => Even T.card)).card = 2 ^ (s.card - 1) := by
  set t : Finset α → Finset α := fun T => if a ∈ T then T.erase a else insert a T with ht
  have tt : ∀ T, t (t T) = T := by
    intro T
    by_cases h : a ∈ T <;> simp [ht, h]
  have tsub : ∀ T, T ⊆ s → t T ⊆ s := by
    intro T hT
    by_cases h : a ∈ T
    · simp only [ht, h, ite_true]; exact (erase_subset _ _).trans hT
    · simp only [ht, h, ite_false]; exact insert_subset ha hT
  have tpar : ∀ T, Even (t T).card ↔ ¬ Even T.card := by
    intro T
    by_cases h : a ∈ T
    · simp only [ht, h, ite_true]
      have := card_erase_add_one h
      rw [← this, Nat.even_add_one, not_not]
    · simp only [ht, h, ite_false]
      rw [card_insert_of_notMem h, Nat.even_add_one]
  have hEO : (s.powerset.filter (fun T => Even T.card)).card =
      (s.powerset.filter (fun T => ¬ Even T.card)).card := by
    apply card_nbij' t t
    · intro T hT
      simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hT ⊢
      exact ⟨tsub T hT.1, by rw [← tpar]; simpa [tt] using hT.2⟩
    · intro T hT
      simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hT ⊢
      exact ⟨tsub T hT.1, by rw [tpar]; exact hT.2⟩
    · intro T _; exact tt T
    · intro T _; exact tt T
  have htot := card_filter_add_card_filter_not (s := s.powerset) (fun T => Even T.card)
  rw [card_powerset, ← hEO] at htot
  have hs : s.card = s.card - 1 + 1 := by
    have := card_pos.2 ⟨a, ha⟩; omega
  rw [hs, pow_succ] at htot
  omega

/-- `|Q| = 2^(n-2)` (for `n ≥ 2`). -/
theorem card_Q (hn : 2 ≤ n) : (Q n).card = 2 ^ (n - 2) := by
  set E := (univ.erase (0 : Fin n)).powerset.filter (fun T => Even T.card)
  have hE : E.card = 2 ^ (n - 2) := by
    rw [card_even_powerset _ (a := ⟨1, by omega⟩) (by simp [Fin.ext_iff]),
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    rfl
  have key : ∀ T : Finset (Fin n),
      univ.filter (fun i => (if i ∈ T then (-1 : ℤ) else 1) = -1) = T := by
    intro T; ext i; by_cases h : i ∈ T <;> simp [h]
  rw [← hE]
  symm
  apply card_nbij' (fun T => fun i => if i ∈ T then (-1 : ℤ) else 1)
    (fun x => univ.filter (fun i => x i = -1))
  · intro T hT
    simp only [E, coe_filter, mem_powerset, Set.mem_ofPred_eq] at hT
    simp only [mem_coe, mem_Q]
    refine ⟨fun i => by by_cases h : i ∈ T <;> simp [h], ?_, by rw [key]; exact hT.2⟩
    have : (0 : Fin n) ∉ T := fun h => by simpa using hT.1 h
    simp [this]
  · intro x hx
    simp only [mem_coe, mem_Q] at hx
    simp only [E, coe_filter, mem_powerset, Set.mem_ofPred_eq]
    refine ⟨fun i hi => ?_, hx.2.2⟩
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_erase, mem_univ, and_true]
    rintro rfl; rw [hx.2.1] at hi; norm_num at hi
  · intro T _; exact key T
  · intro x hx
    simp only [mem_coe, mem_Q] at hx
    funext i
    rcases hx.1 i with h | h <;> simp [h]

end Borsuk

end


/-! ## Construction -/

@[expose] public section

open Finset Metric

namespace Borsuk

variable {n : ℕ}

/-! ### Step (2) -/

/-- The rank-one matrix `M(x) = x xᵀ`. -/
def M (x : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ := Matrix.vecMulVec x x

/-- The scalar product of matrices viewed as vectors of length `n²`. -/
def frob (A B : Matrix (Fin n) (Fin n) ℤ) : ℤ := ∑ i, ∑ j, A i j * B i j

/-- Step (2): the first column of `M(x)` is `x`, so `x ↦ M(x)` is injective on `Q`. -/
theorem step2_M_injOn [NeZero n] {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n)
    (h : M x = M y) : x = y := by
  funext i
  have := congrFun (congrFun h i) 0
  simpa [M, Matrix.vecMulVec_apply, (mem_Q.1 hx).2.1, (mem_Q.1 hy).2.1] using this

/-- Step (2): `⟨M(x), M(y)⟩ = ⟨x, y⟩²`. -/
theorem step2_frob (x y : Fin n → ℤ) : frob (M x) (M y) = (x ⬝ᵥ y) ^ 2 := by
  simp only [frob, M, Matrix.vecMulVec_apply, dotProduct, sq, sum_mul_sum]
  refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))

/-- Step (2): for `x, y ∈ Q` (with `n = 4q - 2`, `q ≥ 1`), `⟨M(x), M(y)⟩ ≥ 4`, with equality
iff `x` and `y` are nearly orthogonal. -/
theorem step2_frob_ge [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) {x y : Fin n → ℤ}
    (hx : x ∈ Q n) (hy : y ∈ Q n) :
    4 ≤ frob (M x) (M y) ∧ (frob (M x) (M y) = 4 ↔ NearlyOrthogonal x y) := by
  rw [step2_frob]
  have h := dotProduct_add_two hn hx hy
  set k : ℤ := (q : ℤ) - (hammingDist' x y / 2 : ℕ)
  have hxy : x ⬝ᵥ y = 4 * k - 2 := by linarith
  have hk : 0 ≤ k * (k - 1) := by rcases le_or_gt k 0 with h | h <;> nlinarith
  refine ⟨by rw [hxy]; nlinarith, ?_⟩
  unfold NearlyOrthogonal
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, sq_eq_sq_iff_abs_eq_abs]
  simp

/-! ### Step (3) -/

/-- Indices of the subdiagonal entries of an `n × n` matrix. -/
abbrev SubDiag (n : ℕ) := {p : Fin n × Fin n // p.2 < p.1}

/-- `U(x)`: the subdiagonal entries `xᵢ xⱼ` (`j < i`) of `M(x)`. -/
def U (x : Fin n → ℤ) (p : SubDiag n) : ℝ := ((x p.1.1 * x p.1.2 : ℤ) : ℝ)

theorem sum_subDiag (f : Fin n × Fin n → ℝ) :
    ∑ p : SubDiag n, f p.1 = ∑ i, ∑ j, if j < i then f (i, j) else 0 := by
  rw [← Finset.sum_subtype (univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) (by simp),
    sum_filter, Fintype.sum_prod_type]

/-- `2 ∑_{j<i} zᵢ zⱼ = (∑ zᵢ)² - ∑ zᵢ²`. -/
theorem pair_sum (z : Fin n → ℝ) :
    2 * ∑ p : SubDiag n, z p.1.1 * z p.1.2 = (∑ i, z i) ^ 2 - ∑ i, z i ^ 2 := by
  rw [sum_subDiag (fun p => z p.1 * z p.2), sq, sum_mul_sum]
  have split : ∀ i j : Fin n, z i * z j = (if j < i then z i * z j else 0) +
      (if i < j then z i * z j else 0) + (if i = j then z i * z j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h, ite_eq_right h.ne]; ring
    · subst h; simp only [lt_irrefl, ite_false, ite_true, zero_add]
    · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le), ite_eq_right h.ne']; ring
  rw [sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => split i j))]
  simp only [sum_add_distrib]
  have hswap : ∑ i, ∑ j, (if i < j then z i * z j else 0) =
      ∑ i, ∑ j, (if j < i then z i * z j else 0) := by
    rw [sum_comm]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by rw [mul_comm]))
  rw [hswap]
  simp only [sum_ite_eq, mem_univ, ite_true]
  simp only [sq]
  ring

theorem card_subDiag (n : ℕ) : Fintype.card (SubDiag n) = n.choose 2 := by
  have h := pair_sum (n := n) (fun _ => 1)
  simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow] at h
  have h2 : (2 * Fintype.card (SubDiag n) : ℝ) = (n * (n - 1) : ℕ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h ⊢
    · push_cast [Nat.cast_sub h0]; linarith
  have h3 : 2 * Fintype.card (SubDiag n) = n * (n - 1) := by exact_mod_cast h2
  rw [Nat.choose_two_right]; omega

theorem U_sq {x : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1) (p : SubDiag n) : U x p ^ 2 = 1 := by
  unfold U
  rcases hx p.1.1 with h | h <;> rcases hx p.1.2 with h' | h' <;> simp [h, h']

theorem U_pm {x : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1) (p : SubDiag n) :
    U x p = 1 ∨ U x p = -1 := by
  unfold U
  rcases hx p.1.1 with h | h <;> rcases hx p.1.2 with h' | h' <;> simp [h, h']

/-- Step (3): `⟨M(x), M(y)⟩ = 2⟨U(x), U(y)⟩ + n` for `x, y ∈ {+1,-1}ⁿ`. -/
theorem step3_inner {x y : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    (frob (M x) (M y) : ℝ) = 2 * ∑ p, U x p * U y p + n := by
  rw [step2_frob]
  have h := pair_sum (n := n) (fun i => ((x i * y i : ℤ) : ℝ))
  have h1 : ∑ p : SubDiag n, U x p * U y p =
      ∑ p : SubDiag n, ((x p.1.1 * y p.1.1 : ℤ) : ℝ) * ((x p.1.2 * y p.1.2 : ℤ) : ℝ) := by
    refine sum_congr rfl (fun p _ => ?_)
    simp only [U]; push_cast; ring
  have h2 : ∑ i, ((x i * y i : ℤ) : ℝ) ^ 2 = n := by
    rw [sum_congr rfl (fun i _ => show ((x i * y i : ℤ) : ℝ) ^ 2 = 1 by
      rcases hx i with h | h <;> rcases hy i with h' | h' <;> simp [h, h'])]
    simp
  rw [h1, h, h2]
  simp [dotProduct]

/-- Step (3): all vectors `U(x)` have the same length: `⟨U(x), U(x)⟩ = C(n, 2)`. -/
theorem step3_norm {x : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1) :
    ∑ p, U x p * U x p = n.choose 2 := by
  rw [sum_congr rfl (fun p _ => by rw [← sq, U_sq hx p])]
  simp [card_subDiag]

/-- Step (3): `|U(x) - U(y)|² = n² - ⟨x, y⟩²` for `x, y ∈ {+1,-1}ⁿ`. -/
theorem step3_dist_sq {x y : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    ∑ p, (U x p - U y p) ^ 2 = (n : ℝ) ^ 2 - ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2 := by
  have e : ∀ p, (U x p - U y p) ^ 2 = 2 - 2 * (U x p * U y p) := by
    intro p; have := U_sq hx p; have := U_sq hy p; nlinarith
  rw [sum_congr rfl (fun p _ => e p), sum_sub_distrib, ← mul_sum]
  have h := step3_inner hx hy
  rw [step2_frob] at h
  push_cast at h
  simp only [sum_const, card_univ, card_subDiag, nsmul_eq_mul]
  have hc : ((n.choose 2 : ℕ) : ℝ) * 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    rcases Nat.even_mul_pred_self n with ⟨r, hr⟩
    rw [hr, show (r + r) / 2 = r by omega]
    have : ((n * (n - 1) : ℕ) : ℝ) = r + r := by exact_mod_cast hr
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hr ⊢; omega
    · rw [Nat.cast_mul, Nat.cast_sub h0] at this; push_cast at this; linarith
  linarith

/-- A fixed bijection between `Fin (C(n,2))` and the subdiagonal positions. -/
noncomputable def subDiagEquiv (n : ℕ) : Fin (n.choose 2) ≃ SubDiag n :=
  (Fintype.equivFinOfCardEq (card_subDiag n)).symm

/-- The point `U(x) ∈ {+1,-1}^d ⊆ ℝ^d`, `d = C(n, 2)`. -/
noncomputable def V (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin (n.choose 2)) :=
  WithLp.toLp 2 fun k => U x (subDiagEquiv n k)

theorem V_pm {x : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1) (k : Fin (n.choose 2)) :
    V x k = 1 ∨ V x k = -1 := U_pm hx _

theorem dist_V {x y : Fin n → ℤ} (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    dist (V x) (V y) = Real.sqrt ((n : ℝ) ^ 2 - ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2) := by
  rw [EuclideanSpace.dist_eq, ← step3_dist_sq hx hy]
  congr 1
  simp only [V, PiLp.toLp_apply, Real.dist_eq, sq_abs]
  exact Equiv.sum_comp (subDiagEquiv n) (fun p => (U x p - U y p) ^ 2)

/-- Step (3): `x ↦ U(x)` is injective on `Q`. -/
theorem V_injOn [NeZero n] {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n) (h : V x = V y) :
    x = y := by
  have hU : U x = U y := by
    funext p
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (n.choose 2)) => v ((subDiagEquiv n).symm p)) h
    simpa [V] using this
  funext i
  by_cases hi : i = 0
  · rw [hi, (mem_Q.1 hx).2.1, (mem_Q.1 hy).2.1]
  · have hpos : (0 : Fin n) < i := by
      rcases Fin.pos_iff_ne_zero.2 hi with h; exact Fin.pos_iff_ne_zero.2 hi
    have := congrFun hU ⟨(i, 0), hpos⟩
    simp only [U, (mem_Q.1 hx).2.1, (mem_Q.1 hy).2.1, mul_one] at this
    exact_mod_cast this

/-- The set `S = {U(x) : x ∈ Q} ⊆ {+1,-1}^d ⊆ ℝ^d` of the book. -/
noncomputable def bookS (n : ℕ) [NeZero n] : Finset (EuclideanSpace ℝ (Fin (n.choose 2))) :=
  (Q n).image V

theorem card_bookS [NeZero n] (hn : 2 ≤ n) : (bookS n).card = 2 ^ (n - 2) := by
  rw [bookS, card_image_of_injOn (fun x hx y hy h => V_injOn hx hy h), card_Q hn]

theorem dist_V_le [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) {x y : Fin n → ℤ}
    (hx : x ∈ Q n) (hy : y ∈ Q n) :
    dist (V x) (V y) ≤ Real.sqrt ((n : ℝ) ^ 2 - 4) ∧
      (dist (V x) (V y) = Real.sqrt ((n : ℝ) ^ 2 - 4) ↔ NearlyOrthogonal x y) := by
  have h := step2_frob_ge hn hx hy
  rw [step2_frob] at h
  have hnn : 0 ≤ (n : ℝ) ^ 2 - ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2 := by
    rw [← step3_dist_sq (mem_Q.1 hx).1 (mem_Q.1 hy).1]; positivity
  have h4 : (4 : ℝ) ≤ ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2 := by exact_mod_cast h.1
  rw [dist_V (mem_Q.1 hx).1 (mem_Q.1 hy).1]
  refine ⟨Real.sqrt_le_sqrt (by linarith), ?_⟩
  rw [Real.sqrt_inj hnn (by linarith), ← h.2]
  constructor
  · intro h'; have : ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2 = 4 := by linarith
    exact_mod_cast this
  · intro h'; rw [show ((x ⬝ᵥ y : ℤ) : ℝ) ^ 2 = (((x ⬝ᵥ y) ^ 2 : ℤ) : ℝ) by push_cast; ring, h']
    norm_num

theorem diam_bookS_le [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) :
    diam (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) ≤ Real.sqrt ((n : ℝ) ^ 2 - 4) := by
  apply diam_le_of_forall_dist_le (Real.sqrt_nonneg _)
  intro a ha b hb
  simp only [bookS, coe_image, Set.mem_image, mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact (dist_V_le hn hx hy).1

/-- **The Theorem of Chapter 18** (Kahn–Kalai, in the version of Nilli, Raigorodskii and
Weißbach).  Let `q = p ^ m` be a prime power (`m ≥ 1`), `n = 4q - 2` and `d = C(n, 2)`.
Then there is a set `S ⊆ {+1,-1}^d ⊆ ℝ^d` of `2^(n-2)` points such that every partition of
`S` whose parts have smaller diameter than `S` has at least `2^(n-2) / ∑_{i=0}^{q-2} C(n-1, i)`
parts. -/
theorem borsuk_theorem {p m q n d : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m)
    (hn : n = 4 * q - 2) (hd : d = n.choose 2) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S.card = 2 ^ (n - 2) ∧ (∀ s ∈ S, ∀ i, s i = 1 ∨ s i = -1) ∧
      0 < diam (S : Set (EuclideanSpace ℝ (Fin d))) ∧
      ∀ k : ℕ, HasDiamReducingPartition (S : Set (EuclideanSpace ℝ (Fin d))) k →
        (2 ^ (n - 2) : ℝ) / (∑ i ∈ range (q - 1), (n - 1).choose i : ℕ) ≤ k := by
  subst hd
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
  have : NeZero n := ⟨by omega⟩
  set B := ∑ i ∈ range (q - 1), (n - 1).choose i
  have hB : 0 < B := by
    apply sum_pos (fun i _ => Nat.choose_pos (by simp at *; omega)) ⟨0, by simp; omega⟩
  have hbd : Bornology.IsBounded (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) :=
    (bookS n).finite_toSet.isBounded
  refine ⟨bookS n, card_bookS (by omega), ?_, ?_, ?_⟩
  · intro s hs i
    simp only [bookS, mem_image] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact V_pm (mem_Q.1 hx).1 i
  · -- two distinct points
    have h2 : 1 < (Q n).card := by
      rw [card_Q (by omega)]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 h2
    have hV : V x ≠ V y := fun h => hxy (V_injOn hx hy h)
    calc 0 < dist (V x) (V y) := dist_pos.2 hV
      _ ≤ _ := dist_le_diam_of_mem hbd (by simp [bookS]; exact ⟨x, hx, rfl⟩)
          (by simp [bookS]; exact ⟨y, hy, rfl⟩)
  · rintro k ⟨c, hc⟩
    -- each colour class pulls back to a nearly-orthogonal-free subset of `Q`
    have hclass : ∀ i : Fin k, ((Q n).filter (fun x => c (V x) = i)).card ≤ B := by
      intro i
      refine claim5 hp hm hq hn (filter_subset _ _) ?_
      intro x hx y hy hxy
      simp only [mem_filter] at hx hy
      have heq := ((dist_V_le hn hx.1 hy.1).2).2 hxy
      have hpart : Bornology.IsBounded
          ((bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) ∩ c ⁻¹' {i}) :=
        hbd.subset Set.inter_subset_left
      have hxS : V x ∈ (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) ∩ c ⁻¹' {i} :=
        ⟨by simp only [bookS, coe_image, Set.mem_image, mem_coe]; exact ⟨x, hx.1, rfl⟩, hx.2⟩
      have hyS : V y ∈ (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) ∩ c ⁻¹' {i} :=
        ⟨by simp only [bookS, coe_image, Set.mem_image, mem_coe]; exact ⟨y, hy.1, rfl⟩, hy.2⟩
      have h1 := dist_le_diam_of_mem hpart hxS hyS
      have h2 := hc i
      have h3 := diam_bookS_le hn
      linarith
    have hcount : (Q n).card ≤ k * B := by
      rw [card_eq_sum_card_fiberwise (f := fun x => c (V x)) (t := univ)
        (fun _ _ => mem_coe.2 (mem_univ _))]
      calc _ ≤ ∑ _i : Fin k, B := sum_le_sum (fun i _ => hclass i)
        _ = k * B := by simp
    rw [card_Q (by omega)] at hcount
    rw [div_le_iff₀ (by exact_mod_cast hB)]
    exact_mod_cast hcount

/-! ### The diameter of `S` is attained exactly at nearly-orthogonal pairs -/

/-- `Q` contains a nearly-orthogonal pair (for `n = 4q - 2`, `q ≥ 1`): the all-ones vector
and the vector with `-1` exactly in positions `2, …, 2q - 1`. -/
theorem exists_nearlyOrthogonal [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) (hq : 1 ≤ q) :
    ∃ x ∈ Q n, ∃ y ∈ Q n, NearlyOrthogonal x y := by
  set T := univ.filter (fun i : Fin n => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * q - 2)
  have hT : T.card = 2 * q - 2 := by
    have : T.map Fin.valEmbedding = Icc 1 (2 * q - 2) := by
      ext a
      simp only [T, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
    rw [← card_map Fin.valEmbedding, this, Nat.card_Icc]; omega
  set y : Fin n → ℤ := fun i => if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * q - 2 then -1 else 1
  have hyT : univ.filter (fun i => y i = -1) = T := by
    ext i; simp only [y, T, mem_filter, mem_univ, true_and]; split_ifs with h <;> simp [h]
  have hy : y ∈ Q n := by
    rw [mem_Q]
    refine ⟨fun i => by simp only [y]; split_ifs <;> simp, by simp [y], ?_⟩
    rw [hyT, hT]; exact ⟨q - 1, by omega⟩
  have hx : (fun _ => (1 : ℤ)) ∈ Q n := by
    rw [mem_Q]; simp
  refine ⟨_, hx, y, hy, ?_⟩
  unfold NearlyOrthogonal
  rw [dotProduct_eq_of_pm (mem_Q.1 hx).1 (mem_Q.1 hy).1]
  have : hammingDist' (fun _ => (1 : ℤ)) y = 2 * q - 2 := by
    rw [← hT, hammingDist', ← hyT]
    congr 1; ext i; simp only [y, mem_filter, mem_univ, true_and]; split_ifs <;> simp
  rw [this]
  have h1 : ((2 * q - 2 : ℕ) : ℤ) = 2 * q - 2 := by omega
  rw [h1, show (n : ℤ) = 4 * q - 2 by omega]
  ring_nf; norm_num

/-- The diameter of `S` is `√(n² - 4)`. -/
theorem diam_bookS [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) (hq : 1 ≤ q) :
    diam (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) = Real.sqrt ((n : ℝ) ^ 2 - 4) := by
  refine le_antisymm (diam_bookS_le hn) ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_nearlyOrthogonal hn hq
  rw [← ((dist_V_le hn hx hy).2).2 hxy]
  exact dist_le_diam_of_mem (bookS n).finite_toSet.isBounded
    (by simp only [bookS, coe_image, Set.mem_image, mem_coe]; exact ⟨x, hx, rfl⟩)
    (by simp only [bookS, coe_image, Set.mem_image, mem_coe]; exact ⟨y, hy, rfl⟩)

/-- Step (3): the maximal distance between points `U(x), U(y)` of `S` is achieved exactly when
`x` and `y` are nearly orthogonal. -/
theorem step3_dist_eq_diam_iff [NeZero n] {q : ℕ} (hn : n = 4 * q - 2) (hq : 1 ≤ q)
    {x y : Fin n → ℤ} (hx : x ∈ Q n) (hy : y ∈ Q n) :
    dist (V x) (V y) = diam (bookS n : Set (EuclideanSpace ℝ (Fin (n.choose 2)))) ↔
      NearlyOrthogonal x y := by
  rw [diam_bookS hn hq]; exact (dist_V_le hn hx hy).2

end Borsuk

end


/-! ## Estimates -/

@[expose] public section
open Finset Metric Real Filter
namespace Borsuk
/-- The ratio of the counterexample's cardinality to the bound on a smaller-diameter part. -/
noncomputable def g (q : ℕ) : ℝ :=
  (2 ^ (4 * q - 4) : ℝ) / (∑ i ∈ range (q - 1), (4 * q - 3).choose i : ℕ)
theorem choose_two_eq (q : ℕ) (hq : 1 ≤ q) : (4 * q - 2).choose 2 = (2 * q - 1) * (4 * q - 3) := by
  rw [Nat.choose_two_right]
  have : (4 * q - 2) * (4 * q - 2 - 1) = 2 * ((2 * q - 1) * (4 * q - 3)) := by
    rw [show 4 * q - 2 = 2 * (2 * q - 1) by omega, show 2 * (2 * q - 1) - 1 = 4 * q - 3 by omega]
    ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
theorem isPrimePow_two_le {p m : ℕ} (hp : p.Prime) (hm : 0 < m) : 2 ≤ p ^ m :=
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
theorem exists_set_g {p m q : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m) :
    ∃ S : Set (EuclideanSpace ℝ (Fin ((2 * q - 1) * (4 * q - 3)))),
      Bornology.IsBounded S ∧ 0 < diam S ∧ ∀ k, HasDiamReducingPartition S k → g q ≤ k := by
  have hq2 := isPrimePow_two_le hp hm
  rw [← hq] at hq2
  obtain ⟨S, -, -, hd, hk⟩ := borsuk_theorem hp hm hq rfl (choose_two_eq q (by omega)).symm
  refine ⟨S, S.finite_toSet.isBounded, hd, fun k hk' => ?_⟩
  have := hk k hk'
  rwa [show 4 * q - 2 - 2 = 4 * q - 4 by omega, show 4 * q - 2 - 1 = 4 * q - 3 by omega] at this
theorem borsukNumber_ge_max {p m q : ℕ} (hp : p.Prime) (hm : 0 < m) (hq : q = p ^ m) :
    ((max ⌈g q⌉₊ ((2 * q - 1) * (4 * q - 3) + 1) : ℕ) : ℕ∞) ≤
      borsukNumber ((2 * q - 1) * (4 * q - 3)) := by
  have hq2 := isPrimePow_two_le hp hm
  rw [← hq] at hq2
  have h1 : ((2 * q - 1) * (4 * q - 3) + 1 : ℕ) ≤ borsukNumber ((2 * q - 1) * (4 * q - 3)) :=
    succ_le_borsukNumber _ (Nat.mul_pos (by omega) (by omega))
  obtain ⟨S, hb, hd, hk⟩ := exists_set_g hp hm hq
  have h2 : (⌈g q⌉₊ : ℕ∞) ≤ borsukNumber ((2 * q - 1) * (4 * q - 3)) :=
    le_borsukNumber hb hd fun k hk' => Nat.ceil_le.2 (hk k hk')
  rcases max_choice ⌈g q⌉₊ ((2 * q - 1) * (4 * q - 3) + 1) with h | h <;> rw [h] <;> assumption
theorem g_nine : (758 : ℝ) < g 9 := by
  have : ∑ i ∈ range (9 - 1), (4 * 9 - 3).choose i = 5663890 := by decide
  rw [g, this]; norm_num
/-- The bounded finite counterexample in dimension 561 needs at least 759 parts. -/
theorem counterexample_561 :
    ∃ S : Set (EuclideanSpace ℝ (Fin 561)), Bornology.IsBounded S ∧ 0 < diam S ∧
      ∀ k, HasDiamReducingPartition S k → 759 ≤ k := by
  obtain ⟨S, hb, hd, hk⟩ := exists_set_g (p := 3) (m := 2) Nat.prime_three (by norm_num) rfl
  refine ⟨S, hb, hd, fun k hk' => ?_⟩
  have h1 : g 9 ≤ k := by simpa using hk k hk'
  have : (758 : ℝ) < k := lt_of_lt_of_le g_nine h1
  exact_mod_cast this
theorem borsukNumber_561 : (759 : ℕ∞) ≤ borsukNumber 561 := by
  obtain ⟨S, hb, hd, hk⟩ := counterexample_561
  exact_mod_cast le_borsukNumber hb hd hk
theorem not_borsukConjecture_561 : ¬ BorsukConjecture 561 := by
  obtain ⟨S, hb, hd, hk⟩ := counterexample_561
  exact not_borsukConjecture_of hb hd fun k h => by have := hk k h; omega
theorem choose_four_mul_le (q : ℕ) : ((4 * q).choose q : ℝ) ≤ (256 / 27 : ℝ) ^ q := by
  have h := add_pow (1 / 4 : ℝ) (3 / 4) (4 * q)
  rw [show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num, one_pow] at h
  have hterm : (1 / 4 : ℝ) ^ q * (3 / 4) ^ (4 * q - q) * ((4 * q).choose q) ≤ 1 := by
    calc _ ≤ ∑ m ∈ range (4 * q + 1), (1 / 4 : ℝ) ^ m * (3 / 4) ^ (4 * q - m) *
          ((4 * q).choose m : ℝ) :=
          single_le_sum (f := fun m => (1 / 4 : ℝ) ^ m * (3 / 4) ^ (4 * q - m) *
            ((4 * q).choose m : ℝ)) (fun i _ => by positivity)
            (mem_range.2 (show q < 4 * q + 1 by omega))
      _ = 1 := h.symm
  rw [show 4 * q - q = 3 * q by omega] at hterm
  have hpos : (0 : ℝ) < (1 / 4) ^ q * (3 / 4) ^ (3 * q) := by positivity
  have : ((4 * q).choose q : ℝ) ≤ 1 / ((1 / 4) ^ q * (3 / 4) ^ (3 * q)) := by
    rw [le_div_iff₀ hpos]; linarith
  refine this.trans (le_of_eq ?_)
  rw [pow_mul, ← mul_pow, one_div, ← inv_pow]
  norm_num
theorem choose_le_choose_of_le_half {N i j : ℕ} (hij : i ≤ j) (hj : j ≤ N / 2) :
    N.choose i ≤ N.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
theorem sum_choose_le (q : ℕ) :
    ∑ i ∈ range (q - 1), (4 * q - 3).choose i ≤ (q - 1) * (4 * q).choose q := by
  calc ∑ i ∈ range (q - 1), (4 * q - 3).choose i ≤ ∑ _i ∈ range (q - 1), (4 * q).choose q :=
        sum_le_sum fun i hi => by
          simp only [mem_range] at hi
          exact (Nat.choose_le_choose i (by omega)).trans
            (choose_le_choose_of_le_half (by omega) (by omega))
    _ = (q - 1) * (4 * q).choose q := by simp
theorem sum_choose_pos (q : ℕ) (hq : 2 ≤ q) : 0 < ∑ i ∈ range (q - 1), (4 * q - 3).choose i :=
  sum_pos (fun i hi => Nat.choose_pos (by simp at hi; omega)) ⟨0, by simp; omega⟩
theorem g_ge (q : ℕ) (hq : 2 ≤ q) : (27 / 16 : ℝ) ^ q / (16 * (q - 1)) ≤ g q := by
  have hB := sum_choose_pos q hq
  have h1 : ((∑ i ∈ range (q - 1), (4 * q - 3).choose i : ℕ) : ℝ) ≤
      (q - 1) * (256 / 27 : ℝ) ^ q := by
    have := sum_choose_le q
    have h' : ((∑ i ∈ range (q - 1), (4 * q - 3).choose i : ℕ) : ℝ) ≤
        ((q - 1 : ℕ) : ℝ) * ((4 * q).choose q : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega), Nat.cast_one] at h'
    exact h'.trans (mul_le_mul_of_nonneg_left (choose_four_mul_le q)
      (by have : (2 : ℝ) ≤ q := by exact_mod_cast hq
          linarith))
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  unfold g
  have hBpos : (0 : ℝ) < ((∑ i ∈ range (q - 1), (4 * q - 3).choose i : ℕ) : ℝ) := by
    exact_mod_cast hB
  rw [div_le_div_iff₀ (by linarith) hBpos]
  have h2 : (2 : ℝ) ^ (4 * q - 4) * 16 = 16 ^ q := by
    rw [show (16 : ℝ) ^ q = 2 ^ (4 * q) by rw [pow_mul]; norm_num,
      show 4 * q = 4 * q - 4 + 4 by omega, pow_add]
    norm_num
  calc (27 / 16 : ℝ) ^ q * ((∑ i ∈ range (q - 1), (4 * q - 3).choose i : ℕ) : ℝ)
      ≤ (27 / 16 : ℝ) ^ q * ((q - 1) * (256 / 27 : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ (4 * q - 4) * (16 * (q - 1)) := by
        rw [show (2 : ℝ) ^ (4 * q - 4) * (16 * (q - 1)) = (2 ^ (4 * q - 4) * 16) * (q - 1) by ring,
          h2, show (27 / 16 : ℝ) ^ q * ((q - 1) * (256 / 27) ^ q) =
            ((27 / 16) * (256 / 27)) ^ q * (q - 1) by rw [mul_pow]; ring]
        norm_num
theorem g_gt_book (q : ℕ) (hq : 2 ≤ q) : exp 1 / (64 * q ^ 2) * (27 / 16 : ℝ) ^ q < g q := by
  refine lt_of_lt_of_le ?_ (g_ge q hq)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by linarith)]
  have h27 : (0 : ℝ) < (27 / 16) ^ q := by positivity
  have : exp 1 * (16 * (q - 1)) < 64 * q ^ 2 := by nlinarith [exp_pos 1]
  nlinarith
end Borsuk
end


/-! ## Asymptotics -/

@[expose] public section

open Finset Metric Real Filter

namespace Borsuk

theorem eventually_lt_rpow {r : ℝ} (hr : 1 < r) : ∃ D : ℝ, ∀ s ≥ D, 16 * s < r ^ s := by
  have hL : 0 < Real.log r := Real.log_pos hr
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hL)
  have h2 := h.eventually (gt_mem_nhds (show (0 : ℝ) < Real.log r / 16 by positivity))
  rw [eventually_atTop] at h2
  obtain ⟨D, hD⟩ := h2
  refine ⟨D, fun s hs => ?_⟩
  have h3 := hD s hs
  simp only [Function.comp, id, pow_one] at h3
  rw [Real.rpow_def_of_pos (by linarith)]
  have he := Real.exp_pos (Real.log r * s)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ he] at h3
  have : Real.log r * (16 * s) < Real.log r * Real.exp (Real.log r * s) := by nlinarith
  exact lt_of_mul_lt_mul_left this hL.le

/-- The analytic core of step (4): if `c < (27/16)^θ`, then `c^s < g(q)` whenever `s` is large,
`2 ≤ q ≤ s` and `θ s ≤ q`. -/
theorem key_asymptotic {θ c : ℝ} (hc : 0 < c) (hcθ : c < (27 / 16 : ℝ) ^ θ) :
    ∃ D : ℝ, ∀ (s : ℝ) (q : ℕ), D ≤ s → 2 ≤ q → (q : ℝ) ≤ s → θ * s ≤ q → c ^ s < g q := by
  set r := (27 / 16 : ℝ) ^ θ / c with hr
  have hr1 : 1 < r := by rw [hr, one_lt_div hc]; exact hcθ
  obtain ⟨D, hD⟩ := eventually_lt_rpow hr1
  refine ⟨max D 1, fun s q hs hq hqs hθs => ?_⟩
  have hs1 : 1 ≤ s := le_of_max_le_right hs
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 := g_ge q hq
  have h2 : (27 / 16 : ℝ) ^ (θ * s) ≤ (27 / 16 : ℝ) ^ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hθs
  have h3 : (27 / 16 : ℝ) ^ (θ * s) = r ^ s * c ^ s := by
    rw [Real.rpow_mul (by norm_num), ← Real.mul_rpow (by positivity) hc.le, hr,
      div_mul_cancel₀ _ hc.ne']
  have h4 := hD s (le_of_max_le_left hs)
  have hcs : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  have h5 : (27 / 16 : ℝ) ^ q / (16 * s) ≤ (27 / 16 : ℝ) ^ q / (16 * (q - 1)) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have h6 : c ^ s < (27 / 16 : ℝ) ^ q / (16 * s) := by
    rw [lt_div_iff₀ (by linarith)]
    calc c ^ s * (16 * s) < c ^ s * r ^ s := mul_lt_mul_of_pos_left h4 hcs
      _ = (27 / 16 : ℝ) ^ (θ * s) := by rw [h3]; ring
      _ ≤ _ := h2
  linarith

/-- Turning a real lower bound into a lower bound on `f(d)`. -/
theorem le_borsukNumber_of_real {d : ℕ} {x : ℝ} (hx : 0 ≤ x)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hb : Bornology.IsBounded S) (hd : 0 < diam S)
    (h : ∀ k, HasDiamReducingPartition S k → x < k) :
    ((⌊x⌋₊ + 1 : ℕ) : ℕ∞) ≤ borsukNumber d :=
  le_borsukNumber hb hd fun k hk => Nat.succ_le_of_lt ((Nat.floor_lt hx).2 (h k hk))

/-- Real lower bounds transfer to higher dimensions. -/
theorem lowerBound_mono_real {d d' : ℕ} (hdd : d ≤ d') {x : ℝ} (hx : 0 ≤ x)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hb : Bornology.IsBounded S) (hd : 0 < diam S)
    (h : ∀ k, HasDiamReducingPartition S k → x < k) :
    ∃ S' : Set (EuclideanSpace ℝ (Fin d')), Bornology.IsBounded S' ∧ 0 < diam S' ∧
      ∀ k, HasDiamReducingPartition S' k → x < k := by
  obtain ⟨S', hb', hd', h'⟩ := lowerBound_mono (N := ⌊x⌋₊ + 1) hdd hb hd
    fun k hk => Nat.succ_le_of_lt ((Nat.floor_lt hx).2 (h k hk))
  exact ⟨S', hb', hd', fun k hk => (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast h' k hk)⟩

theorem dim_bounds (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ^ 2 ≤ ((2 * q - 1) * (4 * q - 3) : ℕ) ∧
      (((2 * q - 1) * (4 * q - 3) : ℕ) : ℝ) ≤ 8 * q ^ 2 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  constructor <;> nlinarith

theorem six_fifths_lt : (6 / 5 : ℝ) < (27 / 16 : ℝ) ^ (7 / 20 : ℝ) := by
  have h : ((27 / 16 : ℝ) ^ (7 / 20 : ℝ)) ^ (20 : ℕ) = (27 / 16) ^ (7 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hpos : 0 ≤ (27 / 16 : ℝ) ^ (7 / 20 : ℝ) := by positivity
  by_contra hle
  push Not at hle
  have := pow_le_pow_left₀ hpos hle 20
  rw [h] at this
  norm_num at this

theorem onehundrednine_lt : (109 / 100 : ℝ) < (27 / 16 : ℝ) ^ (1 / 6 : ℝ) := by
  have h : ((27 / 16 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = 27 / 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hpos : 0 ≤ (27 / 16 : ℝ) ^ (1 / 6 : ℝ) := by positivity
  by_contra hle
  push Not at hle
  have := pow_le_pow_left₀ hpos hle 6
  rw [h] at this
  norm_num at this

/-- **`f(d) > 1.2^√d` for `d = (2q-1)(4q-3)` and all large prime powers `q`.**  More precisely,
for all sufficiently large prime powers `q` there is a bounded set `S ⊆ ℝ^d` of positive
diameter such that every diameter-reducing partition of `S` has more than `1.2^√d` parts. -/
theorem borsuk_asymptotic_primePow : ∃ Q₀ : ℕ, ∀ p m q : ℕ, p.Prime → 0 < m → q = p ^ m →
    Q₀ ≤ q → ∃ S : Set (EuclideanSpace ℝ (Fin ((2 * q - 1) * (4 * q - 3)))),
      Bornology.IsBounded S ∧ 0 < diam S ∧ ∀ k, HasDiamReducingPartition S k →
        (6 / 5 : ℝ) ^ Real.sqrt ((2 * q - 1) * (4 * q - 3) : ℕ) < k := by
  obtain ⟨D, hD⟩ := key_asymptotic (θ := 7 / 20) (c := 6 / 5) (by norm_num)
    six_fifths_lt
  refine ⟨max 2 ⌈D⌉₊, fun p m q hp hm hq hQ => ?_⟩
  have hq2 : 2 ≤ q := le_of_max_le_left hQ
  obtain ⟨S, hb, hd, hk⟩ := exists_set_g hp hm hq
  refine ⟨S, hb, hd, fun k hk' => lt_of_lt_of_le ?_ (hk k hk')⟩
  set d := (2 * q - 1) * (4 * q - 3)
  obtain ⟨hd1, hd2⟩ := dim_bounds q (by omega)
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqs : (q : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le hd1
  apply hD _ q _ hq2 hqs
  · -- `0.35 √d ≤ q` since `0.35² · d ≤ 0.35² · 8 q² ≤ q²`
    have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hss : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith
  · calc D ≤ ⌈D⌉₊ := Nat.le_ceil D
      _ ≤ q := by exact_mod_cast le_of_max_le_right hQ
      _ ≤ _ := hqs

/-- The ℕ∞-valued form: `f(d) ≥ ⌊1.2^√d⌋ + 1 > 1.2^√d` for `d = (2q-1)(4q-3)`, `q` a large
prime power. -/
theorem borsukNumber_asymptotic_primePow : ∃ Q₀ : ℕ, ∀ p m q : ℕ, p.Prime → 0 < m →
    q = p ^ m → Q₀ ≤ q →
      ((⌊(6 / 5 : ℝ) ^ Real.sqrt ((2 * q - 1) * (4 * q - 3) : ℕ)⌋₊ + 1 : ℕ) : ℕ∞) ≤
        borsukNumber ((2 * q - 1) * (4 * q - 3)) := by
  obtain ⟨Q₀, h⟩ := borsuk_asymptotic_primePow
  refine ⟨Q₀, fun p m q hp hm hq hQ => ?_⟩
  obtain ⟨S, hb, hd, hk⟩ := h p m q hp hm hq hQ
  exact le_borsukNumber_of_real (by positivity) hb hd hk

/-- Common step for the all-dimensions bounds: a prime `q` with `8q² ≤ d`, `θ√d ≤ q` (and `√d`
large) gives a set in `ℝ^d` needing more than `c^√d` parts. -/
theorem lowerBound_of_prime {θ c : ℝ} (hc : 0 < c) (hcθ : c < (27 / 16 : ℝ) ^ θ) :
    ∃ D : ℝ, ∀ d q : ℕ, q.Prime → D ≤ Real.sqrt d → 8 * q ^ 2 ≤ d → θ * Real.sqrt d ≤ q →
      ∃ S : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded S ∧ 0 < diam S ∧
        ∀ k, HasDiamReducingPartition S k → c ^ Real.sqrt d < k := by
  obtain ⟨D, hD⟩ := key_asymptotic hc hcθ
  refine ⟨D, fun d q hq hDd h8 hθ => ?_⟩
  have hq2 := hq.two_le
  obtain ⟨S, hb, hd, hk⟩ := exists_set_g (p := q) (m := 1) hq one_pos (pow_one q).symm
  obtain ⟨hd1, hd2⟩ := dim_bounds q (by omega)
  have h8R : (8 * (q : ℝ) ^ 2) ≤ d := by exact_mod_cast h8
  have hdd : (2 * q - 1) * (4 * q - 3) ≤ d := by
    have : (((2 * q - 1) * (4 * q - 3) : ℕ) : ℝ) ≤ d := hd2.trans h8R
    exact_mod_cast this
  have hqs : (q : ℝ) ≤ Real.sqrt d :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (q : ℝ)])
  have hlt := hD _ q hDd hq2 hqs hθ
  exact lowerBound_mono_real hdd (Real.rpow_pos_of_pos hc _).le hb hd
    fun k hk' => hlt.trans_le (hk k hk')

/-- **Unconditional asymptotic bound for all dimensions:** `f(d) > 1.09^√d` for all
sufficiently large `d`.  (Uses Bertrand's postulate to find a prime `q` with
`√d/6 < q ≤ √d/3`.) -/
theorem borsuk_asymptotic_all_weak : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
    ∃ S : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded S ∧ 0 < diam S ∧
      ∀ k, HasDiamReducingPartition S k → (109 / 100 : ℝ) ^ Real.sqrt d < k := by
  obtain ⟨D, hD⟩ := lowerBound_of_prime (θ := 1 / 6) (by norm_num) onehundrednine_lt
  refine ⟨⌈(max D 6) ^ 2⌉₊, fun d hd => ?_⟩
  have hdR : (max D 6) ^ 2 ≤ (d : ℝ) := (Nat.ceil_le.1 hd)
  have hs : max D 6 ≤ Real.sqrt d := Real.le_sqrt_of_sq_le hdR
  have hs6 : (6 : ℝ) ≤ Real.sqrt d := (le_max_right _ _).trans hs
  set Q := ⌊Real.sqrt d / 3⌋₊ with hQ
  have hQle : (Q : ℝ) ≤ Real.sqrt d / 3 := Nat.floor_le (by positivity)
  have hQlt : Real.sqrt d / 3 < Q + 1 := Nat.lt_floor_add_one _
  have hQ2 : 2 ≤ Q := Nat.le_floor (by norm_num; linarith)
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (Q / 2) (by omega)
  have hqQ : q ≤ Q := by omega
  have h2q : Q + 1 ≤ 2 * q := by omega
  have hss : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  refine hD d q hq ((le_max_left _ _).trans hs) ?_ ?_
  · have : (q : ℝ) ≤ Real.sqrt d / 3 := (by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQle
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have : 8 * (q : ℝ) ^ 2 ≤ d := by nlinarith
    exact_mod_cast this
  · have : ((Q + 1 : ℕ) : ℝ) ≤ 2 * q := by exact_mod_cast h2q
    push_cast at this
    linarith

/-- The ℕ∞-valued form of `borsuk_asymptotic_all_weak`. -/
theorem borsukNumber_asymptotic_all_weak : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
    ((⌊(109 / 100 : ℝ) ^ Real.sqrt d⌋₊ + 1 : ℕ) : ℕ∞) ≤ borsukNumber d := by
  obtain ⟨D, h⟩ := borsuk_asymptotic_all_weak
  refine ⟨D, fun d hd => ?_⟩
  obtain ⟨S, hb, hdS, hk⟩ := h d hd
  exact le_borsukNumber_of_real (by positivity) hb hdS hk

/-- Primes in short intervals: for every `ε > 0`, every sufficiently large real `x` has a prime
in `[(1 - ε) x, x]`.  This is a well-known consequence of the prime number theorem; it is
**not proved here** and is only used as an explicit hypothesis. -/
def ShortIntervalPrimes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∃ p : ℕ, p.Prime ∧ (1 - ε) * x ≤ p ∧ (p : ℝ) ≤ x

/-- **Conditional theorem:** assuming `ShortIntervalPrimes`, `f(d) > 1.2^√d` for *all*
sufficiently large `d` (the book's statement). -/
theorem borsuk_asymptotic_all_conditional (H : ShortIntervalPrimes) : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
    ∃ S : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded S ∧ 0 < diam S ∧
      ∀ k, HasDiamReducingPartition S k → (6 / 5 : ℝ) ^ Real.sqrt d < k := by
  obtain ⟨D, hD⟩ := lowerBound_of_prime (θ := 7 / 20) (by norm_num) six_fifths_lt
  obtain ⟨X, hX⟩ := H (1 / 200) (by norm_num)
  set M := max (max D (X * 2000 / 707)) 0 with hM
  refine ⟨⌈M ^ 2⌉₊, fun d hd => ?_⟩
  have hdR : M ^ 2 ≤ (d : ℝ) := Nat.ceil_le.1 hd
  have hs : M ≤ Real.sqrt d := Real.le_sqrt_of_sq_le hdR
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hss : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hXs : X ≤ 707 / 2000 * Real.sqrt d := by
    have : X * 2000 / 707 ≤ Real.sqrt d := (le_max_right _ _).trans ((le_max_left _ _).trans hs)
    linarith
  obtain ⟨q, hq, hq1, hq2⟩ := hX _ hXs
  refine hD d q hq ((le_max_left _ _).trans ((le_max_left _ _).trans hs)) ?_ (by linarith)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have : 8 * (q : ℝ) ^ 2 ≤ d := by nlinarith
  exact_mod_cast this

end Borsuk

end
