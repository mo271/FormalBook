/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic
/-!
# Cotangent and the Herglotz trick

A formalization of Chapter 26 of *Proofs from THE BOOK* (Aigner–Ziegler).

## Part 1: Euler's partial fraction expansion of the cotangent

For `x ∈ ℝ \ ℤ` put `f(x) = π cot(π x)` and `g(x) = lim_{N→∞} ∑_{n=-N}^{N} 1/(x+n)`
(`Chapter26.f`, `Chapter26.gN`, `Chapter26.g`, `Chapter26.tendsto_gN`).

* (A) `f_continuousAt`, `g_continuousAt` (via uniform convergence, `S_continuousOn`);
* (B) `f_add_one`, `g_add_one`;
* (C) `f_neg`, `g_neg`;
* (D) `f_duplication`, `g_duplication`;
* (E) `h` (`= f - g`, extended by `0` on `ℤ`) is continuous (`h_continuous`) and satisfies
  (B), (C), (D) on all of `ℝ` (`h_add_one`, `h_neg`, `h_duplication`);
* the Herglotz trick `herglotz_trick`, giving `f_eq_g`;
* the main results `pi_cot_eq_lim` (formula (1)), `euler_cot` (Euler's form) and
  `euler_cot'` (formula (2)).

## Part 2: the values `ζ(2k)`

* formula (5): `y_cot_eq_zeta_series`;
* formula (6): `y_cot_eq_exp`;
* formula (7): `bernoulli_generating_function` (Mathlib's `bernoulli`, with `B₁ = -1/2`);
* formula (8): `bernoulli_recursion`; vanishing of odd Bernoulli numbers:
  `bernoulli_odd_eq_zero`;
* the expansion `y cot y = ∑ (-1)^k 2^{2k} B_{2k}/(2k)! y^{2k}`: `y_cot_eq_bernoulli_series`;
* comparing coefficients: `bernoulli_coeff_eq_zeta`;
* Euler's formula (9): `euler_zeta_even`;
* the table of Bernoulli numbers `bernoulli_four`, …, `bernoulli_twelve` and the values
  `zeta_two`, …, `zeta_twelve`;
* the growth of the Bernoulli numbers: `abs_bernoulli_ge`.
-/

@[expose] public section

open Real Filter Topology

namespace Chapter26

/-! ## Part 1: the partial fraction expansion of the cotangent (Herglotz trick) -/

/-- The symmetric partial sums `g_N(x) = ∑_{n=-N}^{N} 1/(x+n)`. -/
noncomputable def gN (N : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc (-(N : ℤ)) N, 1 / (x + n)

/-- `f(x) = π cot(π x)`. -/
noncomputable def f (x : ℝ) : ℝ := π * cot (π * x)

/-- The `n`-th term `2x / ((n+1)² - x²)` of the series in (2). -/
noncomputable def St (x : ℝ) (n : ℕ) : ℝ := 2 * x / (((n : ℝ) + 1) ^ 2 - x ^ 2)

/-- `S(x) = ∑_{n ≥ 1} 2x/(n² - x²)`. -/
noncomputable def S (x : ℝ) : ℝ := ∑' n : ℕ, St x n

/-- `g(x) = 1/x - ∑_{n ≥ 1} 2x/(n² - x²)`; by `tendsto_gN` this is `lim_{N→∞} g_N(x)`. -/
noncomputable def g (x : ℝ) : ℝ := 1 / x - S x

lemma gN_zero (x : ℝ) : gN 0 x = 1 / x := by simp [gN]

lemma gN_succ (N : ℕ) (x : ℝ) :
    gN (N + 1) x = gN N x + (1 / (x + (N + 1)) + 1 / (x - (N + 1))) := by
  have hI : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
      insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
    ext k; simp; omega
  rw [gN, hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), gN]
  push_cast
  ring_nf

lemma gN_eq (N : ℕ) (x : ℝ) :
    gN N x = 1 / x + ∑ n ∈ Finset.range N, (1 / (x + (n + 1)) + 1 / (x - (n + 1))) := by
  induction N with
  | zero => simp [gN_zero]
  | succ N ih => rw [gN_succ, ih, Finset.sum_range_succ]; ring

lemma notInt_ne_zero {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : x ≠ 0 := by
  simpa using hx 0

/-- The identity `1/(x+n) + 1/(x-n) = -2x/(n²-x²)`. -/
lemma pair_eq {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) (n : ℕ) :
    1 / (x + (n + 1)) + 1 / (x - (n + 1)) = -St x n := by
  have h1 : x + (n + 1) ≠ 0 := by
    have := hx (-((n : ℤ) + 1)); push_cast at this; intro h; apply this; linarith
  have h2 : x - (n + 1) ≠ 0 := by
    have := hx ((n : ℤ) + 1); push_cast at this; intro h; apply this; linarith
  have h3 : ((n : ℝ) + 1) ^ 2 - x ^ 2 ≠ 0 := by
    have : ((n : ℝ) + 1) ^ 2 - x ^ 2 = -((x + (n + 1)) * (x - (n + 1))) := by ring
    rw [this, neg_ne_zero]; exact mul_ne_zero h1 h2
  rw [St]; field_simp; ring

lemma gN_eq_sub {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) (N : ℕ) :
    gN N x = 1 / x - ∑ n ∈ Finset.range N, St x n := by
  rw [gN_eq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [pair_eq hx]

lemma summable_inv_succ_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact_mod_cast this

/-- The bound on the summands used in (A). -/
lemma abs_St_le {x R : ℝ} (n : ℕ) (hxR : |x| ≤ R) (hn : 2 * R ^ 2 ≤ ((n : ℝ) + 1) ^ 2) :
    |St x n| ≤ 4 * R / ((n : ℝ) + 1) ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg x).trans hxR
  have hx2 : x ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hxR 2
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hd : ((n : ℝ) + 1) ^ 2 / 2 ≤ ((n : ℝ) + 1) ^ 2 - x ^ 2 := by nlinarith
  have hdpos : 0 < ((n : ℝ) + 1) ^ 2 - x ^ 2 := by linarith
  rw [St, abs_div, abs_of_pos hdpos, div_le_div_iff₀ hdpos hpos]
  have : |2 * x| = 2 * |x| := by rw [abs_mul]; norm_num
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ 4 * R),
    mul_le_mul_of_nonneg_right hxR hpos.le]

lemma summable_St (x : ℝ) : Summable (St x) := by
  refine Summable.of_norm_bounded_eventually_nat (summable_inv_succ_sq.mul_left (4 * |x|)) ?_
  filter_upwards [eventually_ge_atTop ⌈2 * |x| ^ 2⌉₊] with n hn
  rw [Real.norm_eq_abs]
  have h0 : 2 * |x| ^ 2 ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have h1 : 2 * |x| ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  calc |St x n| ≤ 4 * |x| / ((n : ℝ) + 1) ^ 2 := abs_St_le n le_rfl h1
    _ = 4 * |x| * (1 / ((n : ℝ) + 1) ^ 2) := by ring

lemma St_continuousOn (n : ℕ) {K : Set ℝ} (hK : ∀ y ∈ K, ∀ n : ℕ, y ^ 2 ≠ ((n : ℝ) + 1) ^ 2) :
    ContinuousOn (fun y => St y n) K := by
  unfold St
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro y hy; exact sub_ne_zero.mpr (Ne.symm (hK y hy n))

/-- Uniform convergence on compact sets avoiding the poles gives continuity. -/
lemma S_continuousOn {K : Set ℝ} (hKc : IsCompact K)
    (hK : ∀ y ∈ K, ∀ n : ℕ, y ^ 2 ≠ ((n : ℝ) + 1) ^ 2) : ContinuousOn S K := by
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hC : ∀ n, ∃ C, ∀ y ∈ K, ‖St y n‖ ≤ C := fun n =>
    hKc.exists_bound_of_continuousOn (St_continuousOn n hK)
  choose C hC using hC
  classical
  let u : ℕ → ℝ := fun n =>
    (if ((n : ℝ) + 1) ^ 2 < 2 * R ^ 2 then C n else 0) + 4 * R * (1 / ((n : ℝ) + 1) ^ 2)
  refine continuousOn_tsum (f := fun n y => St y n) (u := u) (fun n => St_continuousOn n hK) ?_ ?_
  · refine Summable.add ?_ (summable_inv_succ_sq.mul_left _)
    apply summable_of_ne_finset_zero (s := Finset.range (⌈2 * R ^ 2⌉₊ + 1))
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have : 2 * R ^ 2 ≤ (n : ℝ) := Nat.ceil_le.mp (by omega)
    rw [ite_eq_right]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · intro n y hy
    have hyR : |y| ≤ R := by simpa using hR y hy
    have hR0 : 0 ≤ R := (abs_nonneg y).trans hyR
    by_cases hn : ((n : ℝ) + 1) ^ 2 < 2 * R ^ 2
    · simp only [u, ite_eq_left hn]
      have := hC n y hy
      have : 0 ≤ 4 * R * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
      linarith
    · simp only [u, ite_eq_right hn, zero_add]
      rw [Real.norm_eq_abs]
      calc _ ≤ _ := abs_St_le n hyR (not_lt.mp hn)
        _ = _ := by ring

lemma S_continuousAt {V : Set ℝ} (hV : IsOpen V)
    (hVn : ∀ y ∈ V, ∀ n : ℕ, y ^ 2 ≠ ((n : ℝ) + 1) ^ 2) {x : ℝ} (hx : x ∈ V) :
    ContinuousAt S x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV x hx
  have hsub : Metric.closedBall x (ε / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  exact (S_continuousOn (isCompact_closedBall x (ε / 2)) (fun y hy => hVn y (hsub hy))).continuousAt
    (Metric.closedBall_mem_nhds x (by linarith))

lemma isOpen_notInt : IsOpen {x : ℝ | ∀ n : ℤ, x ≠ n} := by
  have : {x : ℝ | ∀ n : ℤ, x ≠ n} = (Set.range ((↑) : ℤ → ℝ))ᶜ := by
    ext x; simp [eq_comm]
  rw [this]; exact Int.isClosedEmbedding_coe_real.isClosed_range.isOpen_compl

lemma S_continuousAt_of_notInt {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ContinuousAt S x := by
  refine S_continuousAt isOpen_notInt ?_ hx
  intro y hy n hn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hn with h | h
  · exact hy ((n : ℤ) + 1) (by push_cast; exact h)
  · exact hy (-((n : ℤ) + 1)) (by push_cast; exact h)

lemma S_continuousAt_zero : ContinuousAt S 0 := by
  refine S_continuousAt isOpen_Ioo (fun y hy n hn => ?_) (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
  have : y ^ 2 < 1 := by obtain ⟨h1, h2⟩ := hy; nlinarith
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  linarith

lemma S_zero : S 0 = 0 := by simp [S, St]

/-- `g` is the limit of the symmetric partial sums `g_N`. -/
theorem tendsto_gN {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (fun N => gN N x) atTop (𝓝 (g x)) := by
  have h1 := (summable_St x).hasSum.tendsto_sum_nat
  have : (fun N => gN N x) = fun N => 1 / x - ∑ n ∈ Finset.range N, St x n :=
    funext (gN_eq_sub hx)
  rw [this]; exact h1.const_sub _

/-! ### (A) continuity -/

lemma sin_pi_mul_ne_zero {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : sin (π * x) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  exact hx n (mul_left_cancel₀ Real.pi_ne_zero (by linarith [hn] : π * x = π * (n : ℝ)))

theorem f_continuousAt {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ContinuousAt f x := by
  have hs := sin_pi_mul_ne_zero hx
  have : f = fun y => π * (cos (π * y) / sin (π * y)) :=
    funext fun y => by rw [f, Real.cot_eq_cos_div_sin]
  rw [this]
  exact continuousAt_const.mul
    ((by fun_prop : ContinuousAt (fun y => cos (π * y)) x).div (by fun_prop) hs)

theorem g_continuousAt {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ContinuousAt g x := by
  show ContinuousAt (fun y => 1 / y - S y) x
  exact (continuousAt_const.div continuousAt_id (notInt_ne_zero hx)).sub
    (S_continuousAt_of_notInt hx)

/-! ### (B) periodicity -/

lemma notInt_add_one {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ∀ n : ℤ, x + 1 ≠ n := by
  intro n h; apply hx (n - 1); push_cast; linarith

theorem f_add_one (x : ℝ) : f (x + 1) = f x := by
  rw [f, f, mul_add, mul_one, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, cos_add_pi,
    sin_add_pi, neg_div_neg_eq]

lemma gN_add_one (N : ℕ) (x : ℝ) :
    gN N (x + 1) = gN N x + 1 / ((x + 1) + N) - 1 / (x - N) := by
  induction N with
  | zero => rw [gN_zero, gN_zero]; push_cast; ring
  | succ N ih => rw [gN_succ, gN_succ, ih]; push_cast; ring_nf

lemma tendsto_one_div_add_nat (c : ℝ) : Tendsto (fun N : ℕ => 1 / (c + N)) atTop (𝓝 0) := by
  have : Tendsto (fun N : ℕ => c + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp this

lemma tendsto_one_div_sub_nat (c : ℝ) : Tendsto (fun N : ℕ => 1 / (c - N)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_nat (-c)).neg
  rw [neg_zero] at this
  refine this.congr fun N => ?_
  rw [show c - (N : ℝ) = -(-c + N) by ring, one_div_neg_eq_neg_one_div]

theorem g_add_one {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : g (x + 1) = g x := by
  have h1 := tendsto_gN (notInt_add_one hx)
  have h2 : Tendsto (fun N => gN N (x + 1)) atTop (𝓝 (g x + 0 - 0)) := by
    simp_rw [gN_add_one]
    exact ((tendsto_gN hx).add (tendsto_one_div_add_nat (x + 1))).sub (tendsto_one_div_sub_nat x)
  rw [add_zero, sub_zero] at h2
  exact tendsto_nhds_unique h1 h2

/-! ### (C) oddness -/

theorem f_neg (x : ℝ) : f (-x) = -f x := by
  rw [f, f, mul_neg, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg,
    mul_neg]

theorem gN_neg (N : ℕ) (x : ℝ) : gN N (-x) = -gN N x := by
  induction N with
  | zero => rw [gN_zero, gN_zero, one_div_neg_eq_neg_one_div]
  | succ N ih =>
    rw [gN_succ, gN_succ, ih, show -x + ((N : ℝ) + 1) = -(x - (N + 1)) by ring,
      show -x - ((N : ℝ) + 1) = -(x + (N + 1)) by ring, one_div_neg_eq_neg_one_div,
      one_div_neg_eq_neg_one_div]
    ring

theorem g_neg (x : ℝ) : g (-x) = -g x := by
  have hS : S (-x) = -S x := by
    simp only [S]; rw [← tsum_neg]; congr 1; funext n; simp only [St]; rw [neg_sq]; ring
  simp only [g]; rw [hS, one_div_neg_eq_neg_one_div]; ring

/-! ### (D) the functional equation -/

theorem f_duplication {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    f (x / 2) + f ((x + 1) / 2) = 2 * f x := by
  have hs := sin_pi_mul_ne_zero hx
  set θ := π * x / 2 with hθ
  have h2 : π * x = 2 * θ := by rw [hθ]; ring
  rw [h2, sin_two_mul] at hs
  have hsθ : sin θ ≠ 0 := fun h => hs (by rw [h]; ring)
  have hcθ : cos θ ≠ 0 := fun h => hs (by rw [h]; ring)
  simp only [f]
  rw [show π * (x / 2) = θ by rw [hθ]; ring, show π * ((x + 1) / 2) = θ + π / 2 by rw [hθ]; ring,
    h2, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    cos_add_pi_div_two, sin_add_pi_div_two, cos_two_mul, sin_two_mul]
  field_simp
  linear_combination (-1 : ℝ) * sin_sq_add_cos_sq θ

lemma gN_duplication (N : ℕ) (x : ℝ) :
    gN N (x / 2) + gN N ((x + 1) / 2) = 2 * gN (2 * N) x + 2 / (x + 2 * N + 1) := by
  have k1 : ∀ c : ℝ, 1 / (x / 2 + c) = 2 / (x + 2 * c) := fun c => by
    rw [show x / 2 + c = (x + 2 * c) / 2 by ring, one_div_div]
  have k2 : ∀ c : ℝ, 1 / (x / 2 - c) = 2 / (x - 2 * c) := fun c => by
    rw [show x / 2 - c = (x - 2 * c) / 2 by ring, one_div_div]
  have k3 : ∀ c : ℝ, 1 / ((x + 1) / 2 + c) = 2 / (x + (2 * c + 1)) := fun c => by
    rw [show (x + 1) / 2 + c = (x + (2 * c + 1)) / 2 by ring, one_div_div]
  have k4 : ∀ c : ℝ, 1 / ((x + 1) / 2 - c) = 2 / (x - (2 * c - 1)) := fun c => by
    rw [show (x + 1) / 2 - c = (x - (2 * c - 1)) / 2 by ring, one_div_div]
  induction N with
  | zero => simp only [mul_zero, gN_zero]; push_cast; rw [one_div_div, one_div_div]; ring
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, gN_succ (2 * N + 1), gN_succ (2 * N),
      gN_succ N (x / 2), gN_succ N ((x + 1) / 2), k1, k2, k3, k4]
    have : gN N (x / 2) = 2 * gN (2 * N) x + 2 / (x + 2 * N + 1) - gN N ((x + 1) / 2) := by
      linarith [ih]
    rw [this]
    push_cast
    ring_nf

lemma notInt_half {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ∀ n : ℤ, x / 2 ≠ n := by
  intro n h; apply hx (2 * n); push_cast; linarith

lemma notInt_half_add {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ∀ n : ℤ, (x + 1) / 2 ≠ n := by
  intro n h; apply hx (2 * n - 1); push_cast; linarith

theorem g_duplication {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    g (x / 2) + g ((x + 1) / 2) = 2 * g x := by
  have hA := tendsto_gN (notInt_half hx)
  have hB := tendsto_gN (notInt_half_add hx)
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b, by omega⟩)
  have hC : Tendsto (fun N : ℕ => gN (2 * N) x) atTop (𝓝 (g x)) := (tendsto_gN hx).comp h2N
  have hD : Tendsto (fun N : ℕ => 2 / (x + 2 * N + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => x + 2 * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_left _ x
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
    have := h1.inv_tendsto_atTop.const_mul 2
    rw [mul_zero] at this
    exact this.congr fun N => by simp [div_eq_mul_inv]
  have h1 := hA.add hB
  have h2 := (hC.const_mul 2).add hD
  rw [add_zero] at h2
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  rw [gN_duplication]

/-! ### (E) the difference `h = f - g` extends continuously to `ℝ` -/

/-- The estimate `|cot x - 1/x| ≤ 2x` for `0 < x ≤ 1`. -/
lemma abs_cot_sub_inv_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : |cot x - 1 / x| ≤ 2 * x := by
  have hs := Real.sin_bound (by rw [abs_of_pos hx0]; exact hx1)
  have hc := Real.cos_bound (by rw [abs_of_pos hx0]; exact hx1)
  rw [abs_of_pos hx0] at hs hc
  rw [abs_le] at hs hc
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hc1, hc2⟩ := hc
  have hx3 : x ^ 3 ≤ x := by nlinarith
  have hx4 : x ^ 4 ≤ x ^ 3 := by nlinarith
  have hx5 : x ^ 5 ≤ x ^ 4 := by nlinarith
  have hsin : x / 2 ≤ sin x := by nlinarith
  have hsinpos : 0 < sin x := by linarith
  rw [Real.cot_eq_cos_div_sin, div_sub_div _ _ hsinpos.ne' hx0.ne', abs_div,
    abs_of_pos (by positivity : 0 < sin x * x), div_le_iff₀ (by positivity), abs_le]
  have e1 := mul_le_mul_of_nonneg_left hc1 hx0.le
  have e2 := mul_le_mul_of_nonneg_left hc2 hx0.le
  have e3 := mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ 2 * x * x)
  constructor <;> nlinarith

lemma abs_cot_sub_inv_le' {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |cot x - 1 / x| ≤ 2 * |x| := by
  rcases lt_or_gt_of_ne hx0 with h | h
  · have := abs_cot_sub_inv_le (neg_pos.2 h) (by rw [abs_of_neg h] at hx1; exact hx1)
    rw [Real.cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg, one_div_neg_eq_neg_one_div,
      ← neg_add', abs_neg, ← sub_eq_add_neg, ← Real.cot_eq_cos_div_sin] at this
    rw [abs_of_neg h]; exact this
  · rw [abs_of_pos h] at hx1 ⊢; exact abs_cot_sub_inv_le h hx1

/-- `lim_{x → 0} (cot x - 1/x) = 0`. -/
theorem tendsto_cot_sub_inv : Tendsto (fun x => cot x - 1 / x) (𝓝[≠] 0) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x => 2 * |x|) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with x hx0 hx1
    rw [Real.norm_eq_abs]
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx1
    exact abs_cot_sub_inv_le' hx0 hx1
  · have : Tendsto (fun x : ℝ => 2 * |x|) (𝓝 0) (𝓝 (2 * |0|)) :=
      ((continuous_const.mul continuous_abs).tendsto 0)
    rw [abs_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_f_sub_inv : Tendsto (fun x => f x - 1 / x) (𝓝[≠] 0) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => π * x) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => π * x) (𝓝 0) (𝓝 (π * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero pi_ne_zero hx
  have h2 := (tendsto_cot_sub_inv.comp h1).const_mul π
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  simp only [Function.comp, f]
  field_simp

open Classical in
/-- `h = f - g`, extended by `0` at the integers. -/
noncomputable def h (x : ℝ) : ℝ := if ∀ n : ℤ, x ≠ n then f x - g x else 0

lemma h_of_notInt {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : h x = f x - g x := by
  simp [h, hx]

lemma h_intCast (m : ℤ) : h m = 0 := by
  simp [h]

lemma notInt_neg {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : ∀ n : ℤ, -x ≠ n := by
  intro n h; apply hx (-n); push_cast; linarith

theorem h_add_one (x : ℝ) : h (x + 1) = h x := by
  by_cases hx : ∀ n : ℤ, x ≠ n
  · rw [h_of_notInt hx, h_of_notInt (notInt_add_one hx), f_add_one, g_add_one hx]
  · push Not at hx
    obtain ⟨n, rfl⟩ := hx
    rw [show (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) by push_cast; ring, h_intCast, h_intCast]

theorem h_neg (x : ℝ) : h (-x) = -h x := by
  by_cases hx : ∀ n : ℤ, x ≠ n
  · rw [h_of_notInt hx, h_of_notInt (notInt_neg hx), f_neg, g_neg]; ring
  · push Not at hx
    obtain ⟨n, rfl⟩ := hx
    rw [show -(n : ℝ) = ((-n : ℤ) : ℝ) by push_cast; ring, h_intCast, h_intCast, neg_zero]

theorem h_continuousAt_zero : ContinuousAt h 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h0 : h 0 = 0 := by exact_mod_cast h_intCast 0
  rw [h0]
  have hS : Tendsto S (𝓝[≠] 0) (𝓝 0) := by
    have := S_continuousAt_zero.tendsto
    rw [S_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := tendsto_f_sub_inv.add hS
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)] with x hx0 hx1
  have hx : ∀ n : ℤ, x ≠ n := by
    intro n hn
    subst hn
    obtain ⟨h1, h2⟩ := hx1
    have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    have : n = 0 := by omega
    subst this
    simp at hx0
  rw [h_of_notInt hx]
  simp only [g]
  ring

theorem h_continuous : Continuous h := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : ∀ n : ℤ, x ≠ n
  · have : h =ᶠ[𝓝 x] fun y => f y - g y := by
      filter_upwards [isOpen_notInt.mem_nhds hx] with y hy
      exact h_of_notInt hy
    exact ((f_continuousAt hx).sub (g_continuousAt hx)).congr this.symm
  · push Not at hx
    obtain ⟨m, rfl⟩ := hx
    have hp : Function.Periodic h 1 := h_add_one
    have e : h = fun y => h (y - m) :=
      funext fun y => by simpa using (hp.sub_int_mul_eq m (x := y)).symm
    have : ContinuousAt h ((m : ℝ) - m) := by rw [sub_self]; exact h_continuousAt_zero
    have hc : ContinuousAt (fun y => h (y - m)) m :=
      ContinuousAt.comp (g := h) (f := fun y => y - (m : ℝ)) this (by fun_prop)
    exact hc.congr (Filter.Eventually.of_forall fun y => (congrFun e y).symm)

theorem h_duplication (x : ℝ) : h (x / 2) + h ((x + 1) / 2) = 2 * h x := by
  have hd : Dense {x : ℝ | ∀ n : ℤ, x ≠ n} := by
    have := (Set.countable_range ((↑) : ℤ → ℝ)).dense_compl ℝ
    convert this using 1
    ext x
    simp [eq_comm]
  have hc1 : Continuous fun x => h (x / 2) + h ((x + 1) / 2) :=
    (h_continuous.comp (by fun_prop)).add (h_continuous.comp (by fun_prop))
  have hc2 : Continuous fun x => 2 * h x := continuous_const.mul h_continuous
  have := Continuous.ext_on hd hc1 hc2 (fun x (hx : ∀ n : ℤ, x ≠ n) => by
    rw [h_of_notInt hx, h_of_notInt (notInt_half hx), h_of_notInt (notInt_half_add hx)]
    linarith [f_duplication hx, g_duplication hx])
  exact congrFun this x

/-- The Herglotz trick: a continuous, `1`-periodic, odd function satisfying
`φ(x/2) + φ((x+1)/2) = 2 φ(x)` vanishes identically. -/
theorem herglotz_trick {φ : ℝ → ℝ} (hc : Continuous φ) (hp : ∀ x, φ (x + 1) = φ x)
    (hodd : ∀ x, φ (-x) = -φ x) (hD : ∀ x, φ (x / 2) + φ ((x + 1) / 2) = 2 * φ x) :
    ∀ x, φ x = 0 := by
  have hp' : Function.Periodic φ 1 := hp
  obtain ⟨m, ⟨x0, rfl⟩, hmax⟩ :=
    (hp'.compact_of_continuous one_ne_zero hc).exists_isGreatest (Set.range_nonempty φ)
  have hle : ∀ y, φ y ≤ φ x0 := fun y => hmax ⟨y, rfl⟩
  have hiter : ∀ n : ℕ, φ (x0 / 2 ^ n) = φ x0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hD (x0 / 2 ^ n)
      rw [ih] at this
      have h1 := hle ((x0 / 2 ^ n + 1) / 2)
      have h2 := hle (x0 / 2 ^ n / 2)
      rw [pow_succ, ← div_div]
      linarith
  have hlim : Tendsto (fun n : ℕ => x0 / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul x0
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    rw [div_pow, one_pow, mul_one_div]
  have h0 : φ 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    linarith
  have hmax0 : φ x0 = 0 := by
    have h1 := (hc.tendsto 0).comp hlim
    have h2 : Tendsto (fun n : ℕ => φ (x0 / 2 ^ n)) atTop (𝓝 (φ x0)) := by
      simp_rw [hiter]; exact tendsto_const_nhds
    rw [← h0]
    exact tendsto_nhds_unique h2 h1
  intro x
  have a := hle x
  have b := hle (-x)
  rw [hodd] at b
  linarith

theorem f_eq_g {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : f x = g x := by
  have := herglotz_trick h_continuous h_add_one h_neg h_duplication x
  rw [h_of_notInt hx] at this
  linarith

/-- **Euler's partial fraction expansion of the cotangent**, in the form (1):
`π cot(π x) = lim_{N→∞} ∑_{n=-N}^{N} 1/(x+n)` for `x ∈ ℝ \ ℤ`. -/
theorem pi_cot_eq_lim {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, 1 / (x + n)) atTop
      (𝓝 (π * cot (π * x))) := by
  have := tendsto_gN hx
  rw [← f_eq_g hx] at this
  exact this

/-- Euler's formula in the original form:
`π cot(π x) = 1/x + ∑_{n ≥ 1} (1/(x+n) + 1/(x-n))` for `x ∈ ℝ \ ℤ`. -/
theorem euler_cot {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    HasSum (fun n : ℕ => 1 / (x + (n + 1)) + 1 / (x - (n + 1))) (π * cot (π * x) - 1 / x) := by
  have e : π * cot (π * x) - 1 / x = -S x := by
    have := f_eq_g hx; simp only [f, g] at this; linarith
  rw [e]
  have : (fun n : ℕ => 1 / (x + (n + 1)) + 1 / (x - (n + 1))) = fun n => -St x n :=
    funext (pair_eq hx)
  rw [this]; exact (summable_St x).hasSum.neg

/-- Euler's formula in the form (2):
`π cot(π x) = 1/x - ∑_{n ≥ 1} 2x/(n² - x²)` for `x ∈ ℝ \ ℤ`. -/
theorem euler_cot' {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    HasSum (fun n : ℕ => 2 * x / (((n : ℝ) + 1) ^ 2 - x ^ 2)) (1 / x - π * cot (π * x)) := by
  have e : 1 / x - π * cot (π * x) = S x := by
    have := f_eq_g hx; simp only [f, g] at this; linarith
  rw [e]; exact (summable_St x).hasSum

/-! ## Part 2: the values `ζ(2k)` -/

open Nat in
/-- `ζ(2k) = ∑_{n ≥ 1} 1 / n^{2k}`. -/
noncomputable def zetaEven (k : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * k)

lemma summable_zetaEven_terms {k : ℕ} (hk : k ≠ 0) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k) := by
  have h : 1 < 2 * k := by omega
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr h)
  exact_mod_cast this

/-- Formula (5), in the form
`y cot y = 1 - 2 ∑_{k ≥ 1} ζ(2k) (y/π)^{2k}` for `0 < |y| < π`. -/
theorem y_cot_eq_zeta_series {y : ℝ} (hy0 : y ≠ 0) (hy : |y| < π) :
    HasSum (fun k : ℕ => 2 * zetaEven (k + 1) * (y / π) ^ (2 * (k + 1))) (1 - y * cot y) := by
  have hπ := Real.pi_pos
  set x := y / π with hxdef
  have hx0 : x ≠ 0 := div_ne_zero hy0 pi_ne_zero
  have hx1 : |x| < 1 := by
    rw [hxdef, abs_div, abs_of_pos hπ, div_lt_one hπ]; exact hy
  have hxi : ∀ n : ℤ, x ≠ n := by
    intro n hn
    have h1 : |(n : ℝ)| < 1 := hn ▸ hx1
    have h2 : |n| < 1 := by exact_mod_cast h1
    have : n = 0 := by rw [abs_lt] at h2; omega
    subst this
    simp at hn
    exact hx0 hn
  have hπx : π * x = y := by rw [hxdef]; field_simp
  have hx2 : x ^ 2 < 1 := by
    have := sq_lt_one_iff_abs_lt_one x |>.mpr hx1; exact this
  have h3 := (euler_cot' hxi).mul_left x
  have hv : x * (1 / x - π * cot (π * x)) = 1 - y * cot y := by
    rw [mul_sub, mul_one_div_cancel hx0, hπx, ← hπx]; ring
  rw [hv] at h3
  set F : ℕ × ℕ → ℝ := fun p => 2 * (x ^ 2 / ((p.1 : ℝ) + 1) ^ 2) ^ (p.2 + 1) with hF
  have hrow : ∀ n : ℕ, HasSum (fun k => F (n, k))
      (x * (2 * x / (((n : ℝ) + 1) ^ 2 - x ^ 2))) := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hq0 : 0 ≤ x ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
    have hq1 : x ^ 2 / ((n : ℝ) + 1) ^ 2 < 1 := by rw [div_lt_one hpos]; linarith
    have hd : ((n : ℝ) + 1) ^ 2 - x ^ 2 ≠ 0 := by
      have : 0 < ((n : ℝ) + 1) ^ 2 - x ^ 2 := by linarith
      exact this.ne'
    have hd' : 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2 ≠ 0 := by
      have : 0 < 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2 := by linarith
      exact this.ne'
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * (x ^ 2 / ((n : ℝ) + 1) ^ 2))
    convert hg using 1
    · funext k; simp only [hF]; ring
    · field_simp
  have hF0 : 0 ≤ F := fun p => by simp only [hF, Pi.zero_apply]; positivity
  have hFs : Summable F := (summable_prod_of_nonneg hF0).2
    ⟨fun n => (hrow n).summable, h3.summable.congr (fun n => ((hrow n).tsum_eq).symm)⟩
  have htot : HasSum F (1 - y * cot y) := by
    have := hFs.hasSum.prod_fiberwise (fun n => hrow n)
    rw [h3.unique this]
    exact hFs.hasSum
  have hcol : ∀ k : ℕ, HasSum (fun n => F (n, k)) (2 * zetaEven (k + 1) * x ^ (2 * (k + 1))) := by
    intro k
    have := (summable_zetaEven_terms (k := k + 1) (by omega)).hasSum.mul_left
      (2 * x ^ (2 * (k + 1)))
    convert this using 1
    · funext n; simp only [hF]; rw [div_pow, ← pow_mul, ← pow_mul]; ring
    · simp only [zetaEven]; ring
  have hswap := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr htot
  exact hswap.prod_fiberwise hcol

open Nat

/-- Formula (8): `∑_{k=0}^{n-1} B_k / (k! (n-k)!) = [n = 1]`. -/
theorem bernoulli_recursion (n : ℕ) :
    ∑ k ∈ Finset.range n, bernoulli k / (k ! * (n - k)! : ℚ) = if n = 1 then 1 else 0 := by
  have h := sum_bernoulli n
  calc ∑ k ∈ Finset.range n, bernoulli k / (k ! * (n - k)! : ℚ)
      = (∑ k ∈ Finset.range n, (n.choose k : ℚ) * bernoulli k) / n ! := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ n := (Finset.mem_range.mp hk).le
        rw [Nat.cast_choose ℚ hk']
        field_simp
    _ = _ := by rw [h]; split_ifs with h1 <;> simp [h1]

lemma sum_inv_factorial_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℚ) / (i + 2)! ≤ 1 - 1 / (N + 1)! := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have e : ((N + 2)! : ℚ) = (N + 2) * (N + 1)! := by
      rw [show N + 2 = (N + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [e]
    have hF : (0 : ℚ) < (N + 1)! := by positivity
    have h1 : 1 / (((N : ℚ) + 2) * (N + 1)!) ≤ 1 / (2 * (N + 1)!) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : 1 / (2 * ((N + 1)! : ℚ)) + 1 / (2 * (N + 1)!) = 1 / (N + 1)! := by
      field_simp; ring
    linarith

/-- A crude bound `|B_n| ≤ n!`, enough to see that `∑ B_n zⁿ/n!` converges for `|z| < 1`. -/
theorem abs_bernoulli_div_factorial_le (n : ℕ) : |bernoulli n / (n ! : ℚ)| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp
    · have hrec := bernoulli_recursion (m + 2)
      rw [ite_eq_right (by omega), Finset.sum_range_succ] at hrec
      have e : m + 2 - (m + 1) = 1 := by omega
      rw [e, Nat.factorial_one, Nat.cast_one, mul_one] at hrec
      have key : bernoulli (m + 1) / ((m + 1)! : ℚ) =
          -∑ k ∈ Finset.range (m + 1), bernoulli k / (k ! * (m + 2 - k)! : ℚ) := by linarith
      rw [key, abs_neg]
      calc |∑ k ∈ Finset.range (m + 1), bernoulli k / (k ! * (m + 2 - k)! : ℚ)|
          ≤ ∑ k ∈ Finset.range (m + 1), |bernoulli k / (k ! * (m + 2 - k)! : ℚ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (m + 1), (1 : ℚ) / ((m - k) + 2)! := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' := Finset.mem_range.mp hk
            have e2 : m + 2 - k = (m - k) + 2 := by omega
            rw [e2, ← div_div, div_eq_mul_one_div (bernoulli k / (k ! : ℚ)), abs_mul,
              abs_of_pos (by positivity : (0 : ℚ) < 1 / ((m - k) + 2)!)]
            exact mul_le_of_le_one_left (by positivity) (ih k (by omega))
        _ = ∑ i ∈ Finset.range (m + 1), (1 : ℚ) / (i + 2)! := by
            rw [← Finset.sum_range_reflect]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' := Finset.mem_range.mp hi
            rw [show m + 1 - 1 - i = m - i by omega, show m - (m - i) = i by omega]
        _ ≤ 1 - 1 / (m + 1 + 1)! := sum_inv_factorial_le _
        _ ≤ 1 := by
            have : (0 : ℚ) ≤ 1 / (m + 1 + 1)! := by positivity
            linarith

lemma norm_bernoulli_div_factorial_le (n : ℕ) : ‖(bernoulli n : ℂ) / (n ! : ℂ)‖ ≤ 1 := by
  have h := abs_bernoulli_div_factorial_le n
  have : (bernoulli n : ℂ) / (n ! : ℂ) = ((bernoulli n / n ! : ℚ) : ℂ) := by push_cast; rfl
  rw [this, Complex.norm_ratCast, ← Rat.cast_abs]
  exact_mod_cast h

lemma bernoulli_recursion_complex (n : ℕ) :
    ∑ k ∈ Finset.range n, (bernoulli k : ℂ) / (k ! * (n - k)! : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) (bernoulli_recursion n)
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast] at h
  rw [h]
  split_ifs <;> simp

/-- Formula (7): the Bernoulli numbers are the coefficients of `z / (e^z - 1)`
(here for `0 < |z| < 1`). -/
theorem bernoulli_generating_function {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun n => (bernoulli n : ℂ) / n ! * z ^ n) (z / (Complex.exp z - 1)) := by
  set f : ℕ → ℂ := fun n => (bernoulli n : ℂ) / n ! * z ^ n with hf
  set g : ℕ → ℂ := fun n => (if n = 0 then 0 else 1 / (n ! : ℂ)) * z ^ n with hg
  have hfn : Summable fun n => ‖f n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg z) hz)
    simp only [hf]
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (norm_bernoulli_div_factorial_le n)
  have hgn : Summable fun n => ‖g n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (Real.summable_pow_div_factorial ‖z‖)
    simp only [hg]
    split_ifs with h
    · simp [h]
    · rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_natCast, one_div_mul_eq_div]
  have hgsum : HasSum g (Complex.exp z - 1) := by
    have he : HasSum (fun n : ℕ => z ^ n / n !) (Complex.exp z) := by
      rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp z
    have := he.sub (hasSum_ite_eq 0 (1 : ℂ))
    convert this using 1
    funext n
    simp only [hg]
    split_ifs with h
    · simp [h]
    · simp [div_eq_mul_inv, mul_comm]
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
  have hinner : ∀ n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) = if n = 1 then z else 0 := by
    intro n
    rw [Finset.sum_range_succ]
    simp only [hf, hg, Nat.sub_self, ite_true, zero_mul, mul_zero, add_zero]
    have : ∀ k ∈ Finset.range n, (bernoulli k : ℂ) / k ! * z ^ k *
        ((if n - k = 0 then 0 else 1 / ((n - k)! : ℂ)) * z ^ (n - k)) =
        z ^ n * ((bernoulli k : ℂ) / (k ! * (n - k)! : ℂ)) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [ite_eq_right (by omega)]
      have : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, bernoulli_recursion_complex]
    split_ifs with h <;> simp [h]
  simp_rw [hinner] at hprod
  rw [tsum_ite_eq, hgsum.tsum_eq] at hprod
  have hne : Complex.exp z - 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact hz0 hprod.symm
  have : ∑' n, f n = z / (Complex.exp z - 1) := by rw [eq_div_iff hne]; exact hprod
  rw [← this]
  exact hfn.of_norm.hasSum

/-- Formula (6): `y cot y = z/2 + z/(e^z - 1)` with `z = 2iy`. -/
theorem y_cot_eq_exp {y : ℝ} (hy : sin y ≠ 0) :
    ((y * cot y : ℝ) : ℂ) = 2 * Complex.I * y / 2 + 2 * Complex.I * y /
      (Complex.exp (2 * Complex.I * y) - 1) := by
  have hs : Complex.sin y ≠ 0 := by rw [← Complex.ofReal_sin]; exact_mod_cast hy
  push_cast
  rw [Complex.cot_eq_cos_div_sin]
  set w := Complex.exp (y * Complex.I) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-y * Complex.I) = w⁻¹ := by
    rw [show -(y : ℂ) * Complex.I = -(y * Complex.I) by ring, Complex.exp_neg]
  have hcos : Complex.cos y = (w + w⁻¹) / 2 := by
    have := Complex.two_cos (y : ℂ); rw [hneg] at this; linear_combination this / 2
  have hsin : Complex.sin y = (w⁻¹ - w) * Complex.I / 2 := by
    have := Complex.two_sin (y : ℂ); rw [hneg] at this; linear_combination this / 2
  have h2 : Complex.exp (2 * Complex.I * y) = w ^ 2 := by
    rw [show 2 * Complex.I * (y : ℂ) = y * Complex.I + y * Complex.I by ring, Complex.exp_add, sq]
  rw [hsin] at hs
  have hd : 1 - w ^ 2 ≠ 0 := by
    intro h; apply hs
    field_simp
    linear_combination (Complex.I) * h
  have hd' : w ^ 2 - 1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  rw [hcos, hsin, h2]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Bernoulli numbers of odd index `n ≥ 3` vanish. -/
theorem bernoulli_odd_eq_zero {n : ℕ} (hn : Odd n) (h1 : 1 < n) : bernoulli n = 0 :=
  bernoulli_eq_zero_of_odd hn h1

/-- The power series expansion `y cot y = ∑_{k ≥ 0} (-1)^k 2^{2k} B_{2k} / (2k)! · y^{2k}`
(here for `0 < |y| < 1/2`). -/
theorem y_cot_eq_bernoulli_series {y : ℝ} (hy0 : y ≠ 0) (hy : |y| < 1 / 2) :
    HasSum (fun k : ℕ => (-1) ^ k * 2 ^ (2 * k) * (bernoulli (2 * k) : ℝ) / (2 * k)! * y ^ (2 * k))
      (y * cot y) := by
  have hπ3 := Real.pi_gt_three
  have hsin : sin y ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have h1 : |(n : ℝ) * π| < π := by rw [hn]; linarith
    rw [abs_mul, abs_of_pos pi_pos] at h1
    have h2 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left pi_pos).mp h1
    have h3 : |n| < 1 := by exact_mod_cast h2
    have : n = 0 := by rw [abs_lt] at h3; omega
    subst this
    simp at hn
    exact hy0 hn.symm
  have hz0 : (2 * Complex.I * y : ℂ) ≠ 0 := by simp [hy0, Complex.I_ne_zero]
  have hz1 : ‖(2 * Complex.I * y : ℂ)‖ < 1 := by
    simp [Complex.norm_real]
    linarith
  have H := (bernoulli_generating_function hz0 hz1).add
    (hasSum_ite_eq 1 ((2 * Complex.I * y : ℂ) / 2))
  rw [add_comm, ← y_cot_eq_exp hsin] at H
  set d : ℕ → ℂ := fun n => if Even n then
    (((-1) ^ (n / 2) * 2 ^ n * (bernoulli n : ℝ) / n ! * y ^ n : ℝ) : ℂ) else 0 with hd
  have hterm : ∀ n, (bernoulli n : ℂ) / n ! * (2 * Complex.I * y) ^ n +
      (if n = 1 then 2 * Complex.I * y / 2 else 0) = d n := by
    intro n
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
    · have hm : m + m ≠ 1 := by omega
      have hev : Even (m + m) := ⟨m, rfl⟩
      rw [ite_eq_right hm, add_zero]
      simp only [hd]
      rw [ite_eq_left hev, show (m + m) / 2 = m by omega]
      push_cast
      rw [show m + m = 2 * m by ring]
      simp only [mul_pow, pow_mul, Complex.I_sq]
      ring
    · have hnd : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
      simp only [hd, ite_eq_right hnd]
      by_cases h1 : n = 1
      · subst h1; simp [bernoulli_one]; ring
      · rw [ite_eq_right h1, add_zero,
          bernoulli_eq_zero_of_odd hodd (by obtain ⟨k, rfl⟩ := hodd; omega)]
        simp
  have H2 : HasSum d ((y * cot y : ℝ) : ℂ) := by
    convert H using 1
    funext n
    exact (hterm n).symm
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have H3 := (hinj.hasSum_iff (f := d) (fun n hn => by
    simp only [hd]; rw [ite_eq_right]; rintro ⟨m, rfl⟩; exact hn ⟨m, by ring⟩)).mpr H2
  rw [← Complex.hasSum_ofReal]
  convert H3 using 1
  funext k
  simp only [Function.comp, hd, ite_eq_left (even_two_mul k), show 2 * k / 2 = k by omega]

/-- Uniqueness of power series coefficients. -/
lemma powerSeries_coeff_eq_zero {a : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hs : Summable fun n => |a n| * r ^ n) (h : ∀ y, |y| < r → ∑' n, a n * y ^ n = 0) (n : ℕ) :
    a n = 0 := by
  set R : NNReal := NNReal.mk r hr.le with hR
  have hsum : ∀ y : ℝ, |y| < r → Summable fun n => a n * y ^ n := fun y hy =>
    Summable.of_norm_bounded hs (fun n => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy.le n) (abs_nonneg _))
  have hp : HasFPowerSeriesOnBall (fun y => ∑' n, a n * y ^ n)
      (FormalMultilinearSeries.ofScalars ℝ a) 0 R := by
    refine ⟨?_, ?_, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [FormalMultilinearSeries.ofScalars_norm, hR, NNReal.coe_mk] using hs
    · rw [ENNReal.coe_pos]; exact hr
    · intro y hy
      have hy' : |y| < r := by
        rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist] at hy
        simpa [Real.dist_eq, hR, NNReal.coe_mk] using hy
      simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
      exact (hsum y hy').hasSum
  have h0 : (fun y => ∑' n, a n * y ^ n) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with y hy
    exact h y (by simpa [Metric.mem_ball, Real.dist_eq] using hy)
  have := hp.hasFPowerSeriesAt.eq_zero_of_eventually h0
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero] at this
  exact congrFun this n

/-- Uniqueness of coefficients for even power series. -/
lemma evenSeries_coeff_eq {a b : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (ha : Summable fun k => |a k| * r ^ (2 * k)) (hb : Summable fun k => |b k| * r ^ (2 * k))
    (h0 : a 0 = b 0)
    (h : ∀ y, y ≠ 0 → |y| < r → ∑' k, a k * y ^ (2 * k) = ∑' k, b k * y ^ (2 * k)) (k : ℕ) :
    a k = b k := by
  set α : ℕ → ℝ := fun n => if Even n then a (n / 2) - b (n / 2) else 0 with hα
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun x y h => by simpa using h
  have hodd0 : ∀ n ∉ Set.range (fun k : ℕ => 2 * k), α n = 0 := by
    intro n hn
    simp only [hα]
    rw [ite_eq_right]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, by ring⟩
  have hαeven : ∀ k, α (2 * k) = a k - b k := by
    intro k
    simp only [hα, ite_eq_left (even_two_mul k), show 2 * k / 2 = k by omega]
  have hs : Summable fun n => |α n| * r ^ n := by
    rw [← hinj.summable_iff (f := fun n => |α n| * r ^ n)
      (fun n hn => by rw [hodd0 n hn, abs_zero, zero_mul])]
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _)) (fun k => ?_) (ha.add hb)
    simp only [Function.comp, hαeven]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub _ _) (pow_nonneg hr.le _)
  have hsa : ∀ y : ℝ, |y| < r → Summable fun k => a k * y ^ (2 * k) := fun y hy =>
    Summable.of_norm_bounded ha (fun k => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy.le _) (abs_nonneg _))
  have hsb : ∀ y : ℝ, |y| < r → Summable fun k => b k * y ^ (2 * k) := fun y hy =>
    Summable.of_norm_bounded hb (fun k => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy.le _) (abs_nonneg _))
  have hzero := powerSeries_coeff_eq_zero hr hs (fun y hy => ?_) (2 * k)
  · rw [hαeven] at hzero; linarith
  · by_cases hy0 : y = 0
    · subst hy0
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
      simp [hα, h0]
    · rw [← hinj.tsum_eq (f := fun n => α n * y ^ n) (fun n hn => by
        by_contra hc; exact hn (by simp only; rw [hodd0 n hc, zero_mul]))]
      simp only [hαeven, sub_mul]
      rw [((hsa y hy).hasSum.sub (hsb y hy).hasSum).tsum_eq, h y hy0 hy, sub_self]

/-- Comparing coefficients in (5) and in the Bernoulli expansion of `y cot y`. -/
theorem bernoulli_coeff_eq_zeta (k : ℕ) :
    (-1) ^ (k + 1) * 2 ^ (2 * (k + 1)) * (bernoulli (2 * (k + 1)) : ℝ) / (2 * (k + 1))! =
      -2 * zetaEven (k + 1) / π ^ (2 * (k + 1)) := by
  set c : ℕ → ℝ := fun j => (-1) ^ j * 2 ^ (2 * j) * (bernoulli (2 * j) : ℝ) / (2 * j)! with hc
  set e : ℕ → ℝ := fun j => if j = 0 then 1 else -2 * zetaEven j / π ^ (2 * j) with he
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hπ3 := Real.pi_gt_three
  have hcb : ∀ j, |(bernoulli j : ℝ) / j !| ≤ 1 := fun j => by
    have := abs_bernoulli_div_factorial_le j; exact_mod_cast this
  have ha : Summable fun j => |c j| * (1 / 4) ^ (2 * j) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1))
    have hb := hcb (2 * j)
    have : |c j| = 2 ^ (2 * j) * |(bernoulli (2 * j) : ℝ) / (2 * j)!| := by
      simp only [hc]
      rw [mul_div_assoc, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
        abs_two]
    rw [this]
    calc 2 ^ (2 * j) * |(bernoulli (2 * j) : ℝ) / (2 * j)!| * (1 / 4) ^ (2 * j)
        ≤ 2 ^ (2 * j) * 1 * (1 / 4) ^ (2 * j) := by gcongr
      _ = (1 / 4) ^ j := by rw [mul_one, ← mul_pow, pow_mul]; norm_num
  have hζ0 : ∀ j, 0 ≤ zetaEven j := fun j => tsum_nonneg fun n => by positivity
  have hb : Summable fun j => |e j| * (1 / 4) ^ (2 * j) := by
    have h5 := y_cot_eq_zeta_series (y := 1 / 4) (by norm_num)
      (by rw [abs_of_pos hr]; linarith)
    rw [← summable_nat_add_iff 1]
    refine h5.summable.congr (fun j => ?_)
    simp only [he, ite_eq_right (Nat.succ_ne_zero j)]
    rw [abs_div, abs_mul, abs_neg, abs_two, abs_of_nonneg (hζ0 _),
      abs_of_pos (pow_pos pi_pos _), div_pow]
    ring
  have h0 : c 0 = e 0 := by simp [hc, he]
  have h : ∀ y, y ≠ 0 → |y| < 1 / 4 →
      ∑' j, c j * y ^ (2 * j) = ∑' j, e j * y ^ (2 * j) := by
    intro y hy0 hy
    have hA := y_cot_eq_bernoulli_series hy0 (by linarith)
    have hB : HasSum (fun j => e j * y ^ (2 * j)) (y * cot y) := by
      have h5 := y_cot_eq_zeta_series hy0 (by linarith)
      rw [← hasSum_nat_add_iff' 1]
      have := h5.neg
      convert this using 1
      · funext j
        simp only [he, ite_eq_right (Nat.succ_ne_zero j)]
        rw [div_pow]
        ring
      · simp [he]
    rw [hA.tsum_eq, hB.tsum_eq]
  have := evenSeries_coeff_eq hr ha hb h0 h (k + 1)
  simp only [hc, he, ite_eq_right (Nat.succ_ne_zero k)] at this
  exact this

/-- **Euler's formula** (9): for `k ≥ 1`,
`∑_{n ≥ 1} 1/n^{2k} = (-1)^{k-1} 2^{2k-1} B_{2k} π^{2k} / (2k)!`. -/
theorem euler_zeta_even {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k))
      ((-1) ^ (k - 1) * 2 ^ (2 * k - 1) * (bernoulli (2 * k) : ℝ) * π ^ (2 * k) / (2 * k)!) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := bernoulli_coeff_eq_zeta j
  have hz : zetaEven (j + 1) = -(π ^ (2 * (j + 1))) / 2 *
      ((-1) ^ (j + 1) * 2 ^ (2 * (j + 1)) * (bernoulli (2 * (j + 1)) : ℝ) / (2 * (j + 1))!) := by
    rw [h]
    field_simp
  have hsum := (summable_zetaEven_terms (k := j + 1) (by omega)).hasSum
  rw [show j + 1 - 1 = j by omega, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  convert hsum using 1
  change _ = zetaEven (j + 1)
  rw [hz]
  ring

/-! ### The table of Bernoulli numbers -/

theorem bernoulli_three : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli_five : bernoulli 5 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli_seven : bernoulli 7 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli_nine : bernoulli 9 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli_eleven : bernoulli 11 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  have h := sum_bernoulli 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_three, bernoulli_zero,
    bernoulli_one, bernoulli_two] at h
  norm_num [Nat.choose] at h
  linarith

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_three, bernoulli_five,
    bernoulli_four, bernoulli_zero, bernoulli_one, bernoulli_two] at h
  norm_num [Nat.choose] at h
  linarith

theorem bernoulli_eight : bernoulli 8 = -1 / 30 := by
  have h := sum_bernoulli 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_three, bernoulli_five,
    bernoulli_seven, bernoulli_four, bernoulli_six, bernoulli_zero, bernoulli_one,
    bernoulli_two] at h
  norm_num [Nat.choose] at h
  linarith

theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  have h := sum_bernoulli 11
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_three, bernoulli_five,
    bernoulli_seven, bernoulli_nine, bernoulli_four, bernoulli_six, bernoulli_eight,
    bernoulli_zero, bernoulli_one, bernoulli_two] at h
  norm_num [Nat.choose] at h
  linarith

theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by
  have h := sum_bernoulli 13
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli_three, bernoulli_five,
    bernoulli_seven, bernoulli_nine, bernoulli_eleven, bernoulli_four, bernoulli_six,
    bernoulli_eight, bernoulli_ten, bernoulli_zero, bernoulli_one, bernoulli_two] at h
  norm_num [Nat.choose] at h
  linarith

/-! ### The values `ζ(2), ζ(4), …, ζ(12)` -/

theorem zeta_two : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := euler_zeta_even (k := 1) (by norm_num)
  norm_num [Nat.factorial] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

theorem zeta_four : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have := euler_zeta_even (k := 2) (by norm_num)
  norm_num [Nat.factorial, bernoulli_four] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

theorem zeta_six : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 6) (π ^ 6 / 945) := by
  have := euler_zeta_even (k := 3) (by norm_num)
  norm_num [Nat.factorial, bernoulli_six] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

theorem zeta_eight : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 8) (π ^ 8 / 9450) := by
  have := euler_zeta_even (k := 4) (by norm_num)
  norm_num [Nat.factorial, bernoulli_eight] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

theorem zeta_ten : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 10) (π ^ 10 / 93555) := by
  have := euler_zeta_even (k := 5) (by norm_num)
  norm_num [Nat.factorial, bernoulli_ten] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

theorem zeta_twelve :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 12) (691 * π ^ 12 / 638512875) := by
  have := euler_zeta_even (k := 6) (by norm_num)
  norm_num [Nat.factorial, bernoulli_twelve] at this
  convert this using 1
  · funext n; rw [one_div]
  · ring

/-- Since `ζ(2k) ≥ 1`, formula (9) shows that the Bernoulli numbers grow very fast:
`|B_{2k}| ≥ 2 (2k)! / (2π)^{2k}`. -/
theorem abs_bernoulli_ge {k : ℕ} (hk : k ≠ 0) :
    2 * ((2 * k)! : ℝ) / (2 * π) ^ (2 * k) ≤ |(bernoulli (2 * k) : ℝ)| := by
  have hs := euler_zeta_even hk
  have h1 : 1 ≤ (-1) ^ (k - 1) * 2 ^ (2 * k - 1) * (bernoulli (2 * k) : ℝ) * π ^ (2 * k) /
      (2 * k)! := by
    have := le_hasSum hs 0 (fun j _ => by positivity)
    simpa using this
  have h2 := h1.trans (le_abs_self _)
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_two, abs_pow, abs_of_pos pi_pos, abs_of_pos (by positivity : (0 : ℝ) < (2 * k)!)] at h2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at h2
  rw [le_div_iff₀ (by positivity)] at h2
  rw [div_le_iff₀ (by positivity)]
  calc 2 * ((2 * (j + 1))! : ℝ)
      ≤ 2 * (2 ^ (2 * j + 1) * |(bernoulli (2 * (j + 1)) : ℝ)| * π ^ (2 * (j + 1))) := by
        linarith
    _ = |(bernoulli (2 * (j + 1)) : ℝ)| * (2 * π) ^ (2 * (j + 1)) := by rw [mul_pow]; ring

end Chapter26
