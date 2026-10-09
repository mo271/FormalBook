/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic

@[expose] public section

/-! ## Part: Defs -/

section DefsPart

/-!
# Van der Waerden's permanent conjecture: basic definitions

We fix the notions used throughout the chapter.

* `Gurvits.matrixPoly M` is the polynomial `p_M(x) = ∏ᵢ (∑ⱼ mᵢⱼ xⱼ)`.
* `Gurvits.NonnegCoeffs p` says that `p ∈ ℝ₊[x₁, …, xₙ]`.
* `Gurvits.IsHStable p` says that `p` has no roots in `ℂⁿ₊₊`.
* `Gurvits.cap p` is the capacity `inf {p(x) : x ∈ ℝⁿ₊, ∏ xᵢ = 1}`.
* `Gurvits.gfun k` is the function `g(k) = ((k-1)/k)^(k-1)` with `g(0) = 1`.
* `Gurvits.pDeriv p` is the polynomial `p'`: the derivative of `p` with respect to a
  distinguished variable, evaluated at `0`.

**Convention.** The book singles out the *last* variable `xₙ` when forming `p'`.
Lean's `MvPolynomial.finSuccEquiv` singles out the *first* variable `x₀`, so here `p'` is
`∂p/∂x₀ |_{x₀ = 0}`, a polynomial in the remaining variables `x₁, …, xₙ` (renumbered as
`Fin n`). By symmetry this makes no difference to any of the arguments.
-/

/-! ### Small auxiliary lemmas

These elementary facts are proved here directly, so that the file does not depend on
Mathlib lemma names that differ between Mathlib versions. -/

namespace Chapter24Aux

theorem prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih hs,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s)) (Finset.prod_nonneg hs)]

theorem prod_le_prod {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hPQ := ih h0s fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP := Finset.prod_nonneg h0s
    have hfa := h0 a (Finset.mem_insert_self a s)
    have hfg := h1 a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hfa (sub_nonneg.2 hPQ), mul_nonneg (sub_nonneg.2 hfg) (hP.trans hPQ)]

theorem finsupp_sum_apply {ι α M : Type*} [AddCommMonoid M] (s : Finset ι) (g : ι → α →₀ M)
    (a : α) : (∑ i ∈ s, g i) a = ∑ i ∈ s, g i a :=
  map_sum (Finsupp.applyAddHom a) g s

theorem polynomial_eval_sum {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → Polynomial R) (x : R) : (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

end Chapter24Aux

open MvPolynomial

namespace Gurvits

variable {σ : Type*}

/-- The polynomial `p_M(x) = ∏ᵢ (∑ⱼ mᵢⱼ xⱼ)` associated to a square matrix `M`. -/
noncomputable def matrixPoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∏ i, ∑ j, C (M i j) * X j

/-- `p ∈ ℝ₊[x]`: all coefficients of `p` are nonnegative. -/
def NonnegCoeffs (p : MvPolynomial σ ℝ) : Prop := ∀ d, 0 ≤ p.coeff d

/-- A real polynomial is *H-stable* if it has no roots in `ℂⁿ₊₊`, i.e. it does not vanish
at any complex point all of whose coordinates have positive real part. -/
def IsHStable (p : MvPolynomial σ ℝ) : Prop :=
  ∀ z : σ → ℂ, (∀ i, 0 < (z i).re) → aeval z p ≠ 0

/-- The *capacity* `cap(p) = inf {p(x) : x ∈ ℝⁿ₊, x₁ ⋯ xₙ = 1}`. -/
noncomputable def cap {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sInf ((fun x => eval x p) '' {x | (∀ i, 0 ≤ x i) ∧ ∏ i, x i = 1})

/-- The function `g : ℕ → ℝ`, `g(0) = 1`, `g(k) = ((k-1)/k)^(k-1)` for `k ≥ 1`. -/
noncomputable def gfun (k : ℕ) : ℝ := if k = 0 then 1 else (((k : ℝ) - 1) / k) ^ (k - 1)

/-- The polynomial `p'`: the partial derivative of `p` with respect to the distinguished
variable `x₀`, evaluated at `x₀ = 0`; it is a polynomial in the remaining `n` variables.
(It is the coefficient of `x₀¹` when `p` is viewed as a polynomial in `x₀`.) -/
noncomputable def pDeriv {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) : MvPolynomial (Fin n) ℝ :=
  (finSuccEquiv ℝ n p).coeff 1

/-- The exponent vector of the monomial `x₁ x₂ ⋯ xₙ`. -/
noncomputable def allOnes (n : ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

/-- The coefficient of the monomial `x₁ x₂ ⋯ xₙ` in `p`. -/
noncomputable def topCoeff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ := p.coeff (allOnes n)

/-- The number `λ_M(j)` of nonzero entries in the `j`-th column of `M`. -/
noncomputable def colNonzero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun i => M i j ≠ 0).card

end Gurvits

end DefsPart

/-! ## Part: Basic -/

section BasicPart

/-!
# Basic facts about the objects of the chapter

Elementary lemmas about evaluation of polynomials with nonnegative coefficients,
homogeneity, the capacity, the function `g`, and the passage `p ↦ p'`.
-/

open MvPolynomial

namespace Gurvits

variable {σ : Type*}

/-! ### Evaluation -/

theorem aeval_ofReal (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    aeval (fun i => (x i : ℂ)) p = (eval x p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Homogeneity as a functional identity: `p(c z) = c^d p(z)`. -/
theorem aeval_smul_of_isHomogeneous {S : Type*} [CommSemiring S] [Algebra ℝ S]
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (z : σ → S) :
    aeval (c • z) p = c ^ d * aeval z p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hp (mem_support_iff.mp hm)
  simp only [aeval_monomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finsupp.prod_mul]
  rw [Finsupp.weight_apply] at hdeg
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at hdeg
  have : (m.prod fun _ k => c ^ k) = c ^ d := by
    rw [← hdeg, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  rw [this]; ring

theorem eval_smul_of_isHomogeneous {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d)
    (c : ℝ) (x : σ → ℝ) : eval (c • x) p = c ^ d * eval x p := by
  have := aeval_smul_of_isHomogeneous (S := ℝ) hp c x
  exact this

theorem eval_nonneg {p : MvPolynomial σ ℝ} (hp : NonnegCoeffs p) {x : σ → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x p := by
  rw [p.as_sum, map_sum]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [eval_monomial]
  exact mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

/-- A polynomial with nonnegative coefficients vanishing at a positive point is zero. -/
theorem eq_zero_of_eval_eq_zero {p : MvPolynomial σ ℝ} (hp : NonnegCoeffs p) {x : σ → ℝ}
    (hx : ∀ i, 0 < x i) (h : eval x p = 0) : p = 0 := by
  rw [p.as_sum, map_sum] at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => by
    rw [eval_monomial]
    exact mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i).le _))).1 h
  ext m
  by_contra hm
  have h1 := hall m (mem_support_iff.2 hm)
  rw [eval_monomial] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact hm h2
  · exact (Finset.prod_pos fun i _ => pow_pos (hx i) _).ne' h2

/-! ### Capacity -/

section cap

variable {n : ℕ}

theorem cap_set_nonempty (p : MvPolynomial (Fin n) ℝ) :
    ((fun x => eval x p) '' {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∏ i, x i = 1}).Nonempty :=
  ⟨_, fun _ => 1, ⟨fun _ => zero_le_one, by simp⟩, rfl⟩

theorem cap_bddBelow {p : MvPolynomial (Fin n) ℝ} (hp : NonnegCoeffs p) :
    BddBelow ((fun x => eval x p) '' {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∏ i, x i = 1}) :=
  ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact eval_nonneg hp hx.1⟩

theorem cap_le_eval {p : MvPolynomial (Fin n) ℝ} (hp : NonnegCoeffs p) {x : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∏ i, x i = 1) : cap p ≤ eval x p :=
  csInf_le (cap_bddBelow hp) ⟨x, ⟨hx0, hx1⟩, rfl⟩

theorem le_cap {p : MvPolynomial (Fin n) ℝ} {c : ℝ}
    (h : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∏ i, x i = 1 → c ≤ eval x p) : c ≤ cap p :=
  le_csInf (cap_set_nonempty p) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx.1 hx.2)

theorem cap_nonneg {p : MvPolynomial (Fin n) ℝ} (hp : NonnegCoeffs p) : 0 ≤ cap p :=
  le_cap fun _ hx _ => eval_nonneg hp hx

theorem eval_fin_zero (p : MvPolynomial (Fin 0) ℝ) (x : Fin 0 → ℝ) : eval x p = p.coeff 0 := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  rw [eval_zero, constantCoeff_eq]

theorem cap_fin_zero (p : MvPolynomial (Fin 0) ℝ) : cap p = p.coeff 0 := by
  apply le_antisymm
  · unfold cap
    refine csInf_le ⟨p.coeff 0, ?_⟩ ⟨Fin.elim0, ⟨fun i => i.elim0, by simp⟩, eval_fin_zero _ _⟩
    rintro _ ⟨x, -, rfl⟩
    exact (eval_fin_zero p x).ge
  · exact le_cap fun x _ _ => (eval_fin_zero p x).ge

end cap

/-! ### The function `g` -/

theorem gfun_zero : gfun 0 = 1 := by simp [gfun]

theorem gfun_one : gfun 1 = 1 := by simp [gfun]

theorem gfun_of_pos {k : ℕ} (hk : 0 < k) : gfun k = (((k : ℝ) - 1) / k) ^ (k - 1) := by
  simp [gfun, hk.ne']

theorem gfun_pos (k : ℕ) : 0 < gfun k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [gfun]
  · rw [gfun_of_pos (by omega)]
    apply pow_pos
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    apply div_pos <;> linarith

theorem gfun_le_one (k : ℕ) : gfun k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [gfun]
  · rw [gfun_of_pos hk]
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    apply pow_le_one₀
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by linarith)]; linarith

/-- The key inequality behind the monotonicity of `g`, proved via Bernoulli's inequality. -/
theorem gfun_aux (m : ℕ) (hm : 1 ≤ m) :
    (((m:ℝ) + 1) / (m + 2)) ^ (m + 1) < ((m:ℝ) / (m + 1)) ^ m := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  set a : ℝ := ((m:ℝ) + 1) / (m + 2) with ha
  set c : ℝ := 1 - 1 / ((m:ℝ)+1)^2 with hc
  have hb : (m:ℝ) / (m + 1) = a * c := by
    rw [ha, hc]; field_simp; ring
  have ha0 : 0 < a := by positivity
  have hbern : 1 + (m:ℝ) * (-(1 / ((m:ℝ)+1)^2)) ≤ c ^ m := by
    rw [hc, sub_eq_add_neg]
    apply one_add_mul_le_pow
    have : 1 / ((m:ℝ)+1)^2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hlt : a < 1 + (m:ℝ) * (-(1 / ((m:ℝ)+1)^2)) := by
    rw [ha]
    rw [div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  rw [hb, mul_pow, pow_succ]
  have := pow_pos ha0 m
  nlinarith

/-- `g(k+1) < g(k)` for `k ≥ 1`. -/
theorem gfun_succ_lt {k : ℕ} (hk : 1 ≤ k) : gfun (k + 1) < gfun k := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · norm_num [gfun]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [gfun_of_pos (by omega), gfun_of_pos (by omega)]
    have := gfun_aux m (by omega)
    rw [show m + 1 + 1 - 1 = m + 1 from rfl, show m + 1 - 1 = m from rfl]
    push_cast
    convert this using 2 <;> ring

/-- `g` is non-increasing: `g(0) = g(1) > g(2) > ⋯`. -/
theorem gfun_antitone : Antitone gfun := by
  refine antitone_nat_of_succ_le fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [gfun]
  · exact (gfun_succ_lt hk).le

/-- `g(m) > g(k)` whenever `m < k` and `k ≥ 2`. -/
theorem gfun_lt_of_lt {m k : ℕ} (hk : 2 ≤ k) (hmk : m < k) : gfun k < gfun m := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (gfun_succ_lt (by omega)).trans_le (gfun_antitone (by omega))

/-- `∏_{i=1}^n g(i) = n!/nⁿ`. -/
theorem prod_gfun (n : ℕ) :
    ∏ i ∈ Finset.range n, gfun (i + 1) = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, gfun_of_pos (by omega)]
    rw [show n + 1 - 1 = n from rfl]
    push_cast
    rw [add_sub_cancel_right, div_pow, Nat.factorial_succ]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (0:ℝ) < n := by exact_mod_cast hn
      field_simp
      ring

open Filter Topology in
/-- `g(k) = (1 - 1/k)^(k-1) → 1/e` as `k → ∞`. -/
theorem tendsto_gfun : Tendsto gfun atTop (𝓝 (Real.exp (-1))) := by
  have h1 : Tendsto (fun k : ℕ => (1 + (-1 : ℝ) / k) ^ k) atTop (𝓝 (Real.exp (-1))) :=
    Real.tendsto_one_add_div_pow_exp (-1)
  have h2 : Tendsto (fun k : ℕ => (1 + (-1 : ℝ) / k)) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (-1 : ℝ)).const_add 1
    simpa using this
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  simp only [gfun, show k ≠ 0 by omega, ite_false]
  have h0 : (k : ℝ) - 1 ≠ 0 := by linarith
  have h0' : (k : ℝ) ≠ 0 := by linarith
  have : (1:ℝ) + (-1) / (k : ℝ) = ((k : ℝ) - 1) / k := by
    field_simp; ring
  show (1 + (-1 : ℝ) / (k : ℝ)) ^ k / (1 + (-1 : ℝ) / (k : ℝ)) = _
  rw [this]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have hne : ((((j + 1 : ℕ) : ℝ) - 1) / ((j + 1 : ℕ) : ℝ)) ≠ 0 := div_ne_zero h0 h0'
  rw [mul_div_assoc, div_self hne, mul_one]

/-! ### The univariate slices `t ↦ p(t, y)` -/

section slice

variable {n : ℕ}

/-- `p(t, y)` as a complex polynomial in `t`, for fixed complex `y`. -/
noncomputable def sliceC (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.map (aeval y).toRingHom (finSuccEquiv ℝ n p)

/-- `p(t, r)` as a real polynomial in `t`, for fixed real `r`. -/
noncomputable def sliceR (p : MvPolynomial (Fin (n + 1)) ℝ) (r : Fin n → ℝ) : Polynomial ℝ :=
  Polynomial.map (eval r) (finSuccEquiv ℝ n p)

theorem sliceC_eval (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℂ) (t : ℂ) :
    (sliceC p y).eval t = aeval (Fin.cons t y : Fin (n + 1) → ℂ) p := by
  unfold sliceC
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, ← hp, aeval_X, Polynomial.eval_mul, Polynomial.map_mul]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

theorem sliceR_eval (p : MvPolynomial (Fin (n + 1)) ℝ) (r : Fin n → ℝ) (t : ℝ) :
    (sliceR p r).eval t = eval (Fin.cons t r : Fin (n + 1) → ℝ) p :=
  (eval_eq_eval_mv_eval' r t p).symm

theorem sliceC_coeff (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℂ) (j : ℕ) :
    (sliceC p y).coeff j = aeval y ((finSuccEquiv ℝ n p).coeff j) := by
  simp [sliceC, Polynomial.coeff_map]

theorem sliceR_coeff (p : MvPolynomial (Fin (n + 1)) ℝ) (r : Fin n → ℝ) (j : ℕ) :
    (sliceR p r).coeff j = eval r ((finSuccEquiv ℝ n p).coeff j) := by
  simp [sliceR, Polynomial.coeff_map]

theorem sliceC_coeff_one (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℂ) :
    (sliceC p y).coeff 1 = aeval y (pDeriv p) := sliceC_coeff p y 1

theorem sliceR_coeff_one (p : MvPolynomial (Fin (n + 1)) ℝ) (r : Fin n → ℝ) :
    (sliceR p r).coeff 1 = eval r (pDeriv p) := sliceR_coeff p r 1

theorem sliceC_ofReal (p : MvPolynomial (Fin (n + 1)) ℝ) (r : Fin n → ℝ) :
    sliceC p (fun j => (r j : ℂ)) = Polynomial.map Complex.ofRealHom (sliceR p r) := by
  ext j
  rw [sliceC_coeff, Polynomial.coeff_map, sliceR_coeff, aeval_ofReal]
  rfl

theorem sliceC_natDegree_le (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℂ) :
    (sliceC p y).natDegree ≤ p.degreeOf 0 := by
  rw [← natDegree_finSuccEquiv]
  exact Polynomial.natDegree_map_le

theorem sliceR_coeff_nonneg {p : MvPolynomial (Fin (n + 1)) ℝ} (hp : NonnegCoeffs p)
    {r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i) (j : ℕ) : 0 ≤ (sliceR p r).coeff j := by
  rw [sliceR_coeff]
  refine eval_nonneg (fun m => ?_) hr
  rw [finSuccEquiv_coeff_coeff]
  exact hp _

end slice

/-! ### The derivative `p'` -/

section deriv

variable {n : ℕ}

theorem pDeriv_coeff (p : MvPolynomial (Fin (n + 1)) ℝ) (m : Fin n →₀ ℕ) :
    (pDeriv p).coeff m = p.coeff (m.cons 1) :=
  finSuccEquiv_coeff_coeff m p 1

theorem pDeriv_nonnegCoeffs {p : MvPolynomial (Fin (n + 1)) ℝ} (hp : NonnegCoeffs p) :
    NonnegCoeffs (pDeriv p) := fun m => by
  rw [pDeriv_coeff]; exact hp _

/-- If `p` is homogeneous of degree `n + 1` then `p'` is homogeneous of degree `n`. -/
theorem pDeriv_isHomogeneous {p : MvPolynomial (Fin (n + 1)) ℝ} (hp : p.IsHomogeneous (n + 1)) :
    (pDeriv p).IsHomogeneous n :=
  hp.finSuccEquiv_coeff_isHomogeneous 1 n (by omega)

theorem allOnes_succ (n : ℕ) : allOnes (n + 1) = (allOnes n).cons 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [allOnes]

/-- The coefficient of `x₀ x₁ ⋯ xₙ` in `p` is the coefficient of `x₁ ⋯ xₙ` in `p'`. -/
theorem topCoeff_pDeriv (p : MvPolynomial (Fin (n + 1)) ℝ) :
    topCoeff (pDeriv p) = topCoeff p := by
  rw [topCoeff, topCoeff, pDeriv_coeff, allOnes_succ]

/-- The degree of `x₀` in a homogeneous polynomial of degree `d` is at most `d`. -/
theorem degreeOf_le_of_isHomogeneous {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d)
    (i : σ) : p.degreeOf i ≤ d :=
  (degreeOf_le_totalDegree p i).trans hp.totalDegree_le

end deriv

end Gurvits

end BasicPart

/-! ## Part: Analytic -/

section AnalyticPart

/-!
# Analytic tools

Auxiliary real/complex analysis used in the proof of Gurvits' Proposition:

* `amgm_one_add`: the AM-GM inequality in the form `∏ (1 + bᵢ t) ≤ (1 + (∑ bᵢ) t / k)^k`;
* `key_opt`: minimising `f₀ (1 + S t / k)^k / t` over `t > 0`, which produces `g(k)`;
* limits `t ↦ q(t)/t` as `t → 0⁺` for polynomials `q` with `q(0) = 0`
  (i.e. `p'(y) = lim_{t→0} p(y,t)/t`);
* the factorization `f(t) = f(0) ∏ (1 + aᵢ t)` of a complex polynomial with `f(0) ≠ 0`.
-/

open Polynomial Filter Topology

namespace Gurvits

/-! ### AM-GM -/

/-- AM-GM for a multiset of nonnegative reals: `∏ c ≤ (∑ c / #C)^#C`. -/
theorem amgm_multiset_card (C : Multiset ℝ) (hC : ∀ c ∈ C, 0 ≤ c) :
    C.prod ≤ (C.sum / C.card) ^ C.card := by
  classical
  rcases Nat.eq_zero_or_pos C.card with h | h
  · rw [Multiset.card_eq_zero.1 h]; simp
  set s := C.toEnumFinset
  have hprod : C.prod = ∏ x ∈ s, x.1 := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_toEnumFinset_fst]
  have hsum : C.sum = ∑ x ∈ s, x.1 := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_toEnumFinset_fst]
  have hcard : s.card = C.card := Multiset.card_toEnumFinset C
  have hz : ∀ x ∈ s, 0 ≤ x.1 := fun x hx => hC _ (Multiset.mem_of_mem_toEnumFinset hx)
  have hk : (0:ℝ) < C.card := by exact_mod_cast h
  have amgm := Real.geom_mean_le_arith_mean_weighted s (fun _ => ((C.card : ℝ))⁻¹)
    (fun x => x.1) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, hcard, nsmul_eq_mul]; field_simp) hz
  rw [Chapter24Aux.prod_rpow s _ hz, ← Finset.mul_sum, ← hprod, ← hsum] at amgm
  have hP : 0 ≤ C.prod := Multiset.prod_nonneg hC
  calc C.prod = (C.prod ^ ((C.card : ℝ))⁻¹) ^ C.card :=
        (Real.rpow_inv_natCast_pow hP h.ne').symm
    _ ≤ ((C.card : ℝ)⁻¹ * C.sum) ^ C.card := by gcongr
    _ = (C.sum / C.card) ^ C.card := by ring

/-- AM-GM in the form used in Case 3: if `b₁, …, b_m ≥ 0` with `m ≤ k` and `t ≥ 0`, then
`∏ (1 + bᵢ t) ≤ (1 + (∑ bᵢ) t / k)^k`. -/
theorem amgm_one_add (B : Multiset ℝ) (hB : ∀ b ∈ B, 0 ≤ b) {k : ℕ} (hk : B.card ≤ k)
    {t : ℝ} (ht : 0 ≤ t) :
    (B.map fun b => 1 + b * t).prod ≤ (1 + B.sum * t / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Multiset.card_eq_zero.1 (Nat.le_zero.1 hk)]; simp
  set B' := B + Multiset.replicate (k - B.card) 0
  have hcard : B'.card = k := by simp [B']; omega
  have hprod : (B'.map fun b => 1 + b * t).prod = (B.map fun b => 1 + b * t).prod := by
    simp [B', Multiset.map_replicate]
  have hsum : B'.sum = B.sum := by simp [B']
  set C := B'.map fun b => 1 + b * t
  have hC : ∀ c ∈ C, 0 ≤ c := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hc
    have : 0 ≤ b := by
      rcases Multiset.mem_add.1 hb with hb | hb
      · exact hB b hb
      · rw [Multiset.eq_of_mem_replicate hb]
    positivity
  have := amgm_multiset_card C hC
  have hCcard : C.card = k := by simp [C, hcard]
  have hCsum : C.sum = k + B.sum * t := by
    simp only [C, Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, hcard,
      Multiset.sum_map_mul_right, nsmul_eq_mul, mul_one, Multiset.map_id', hsum]
  rw [← hprod]
  rw [hCcard, hCsum] at this
  convert this using 2
  have : (0:ℝ) < k := by exact_mod_cast hk0
  field_simp

/-! ### The optimisation producing `g(k)` -/

theorem le_zero_of_forall_le_div {a c : ℝ} (h : ∀ t : ℝ, 0 < t → c ≤ a / t) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  have ha : 0 ≤ a := by
    have := h 1 one_pos; simp at this; linarith
  have := h ((a + 1) / c) (by positivity)
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- If `c ≤ f₀ (1 + S t / k)^k / t` for all `t > 0`, then `c · g(k) ≤ f₀ S`.
(For `k ≥ 2` one takes `t = k / ((k-1) S)`, as in the book.) -/
theorem key_opt {c f0 S : ℝ} {k : ℕ} (hf0 : 0 ≤ f0) (hS : 0 ≤ S)
    (h : ∀ t : ℝ, 0 < t → c ≤ f0 * (1 + S * t / k) ^ k / t) : c * gfun k ≤ f0 * S := by
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · subst hS0
    have : c ≤ 0 := le_zero_of_forall_le_div (a := f0) fun t ht => by simpa using h t ht
    have := gfun_pos k
    simp; nlinarith
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · have : c ≤ 0 := le_zero_of_forall_le_div (a := f0) fun t ht => by simpa using h t ht
      have := mul_nonneg hf0 hS
      simp [gfun]; linarith
    · have : c - f0 * S ≤ 0 := le_zero_of_forall_le_div (a := f0) fun t ht => by
        have := h t ht
        simp only [Nat.cast_one, div_one, pow_one] at this
        rw [show f0 * (1 + S * t) / t = f0 / t + f0 * S by field_simp] at this
        linarith
      simp [gfun]; linarith
  · have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : (k:ℝ) - 1 ≠ 0 := by linarith
    have hk0 : (k:ℝ) ≠ 0 := by linarith
    set t := (k:ℝ) / ((k - 1) * S) with ht
    have htpos : 0 < t := by apply div_pos <;> nlinarith
    have h1 := h t htpos
    have hg : gfun k = (((k:ℝ) - 1) / k) ^ (k - 1) := by simp [gfun]; omega
    have hbase : 1 + S * t / k = k / (k - 1) := by
      rw [ht]; field_simp; ring
    rw [hbase] at h1
    have hval : f0 * ((k:ℝ) / (k - 1)) ^ k / t = f0 * S * ((k:ℝ) / (k - 1)) ^ (k - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have e : k - 1 = j := by omega
      rw [e, hj, pow_succ, ht, ← hj]
      field_simp
    rw [hval] at h1
    rw [hg]
    have hprod : ((k:ℝ) / (k - 1)) ^ (k - 1) * (((k:ℝ) - 1) / k) ^ (k - 1) = 1 := by
      rw [← mul_pow]
      rw [show (k:ℝ) / (k - 1) * ((k - 1) / k) = 1 by field_simp]
      simp
    have hgpos : 0 ≤ (((k:ℝ) - 1) / k) ^ (k - 1) := by
      apply pow_nonneg; apply div_nonneg <;> linarith
    calc c * (((k:ℝ) - 1) / k) ^ (k - 1)
        ≤ f0 * S * ((k:ℝ) / (k - 1)) ^ (k - 1) * (((k:ℝ) - 1) / k) ^ (k - 1) := by gcongr
      _ = f0 * S := by rw [mul_assoc, hprod, mul_one]

/-! ### Limits `q(t)/t → q'(0)` -/

theorem tendsto_eval_div_real (q : ℝ[X]) (h0 : q.coeff 0 = 0) :
    Tendsto (fun t => q.eval t / t) (𝓝[>] 0) (𝓝 (q.coeff 1)) := by
  obtain ⟨q', rfl⟩ := X_dvd_iff.2 h0
  rw [coeff_X_mul, coeff_zero_eq_eval_zero]
  have h1 : Tendsto (fun t => q'.eval t) (𝓝[>] 0) (𝓝 (q'.eval 0)) :=
    (q'.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [eval_mul, eval_X]
  field_simp

theorem tendsto_norm_eval_div (q : ℂ[X]) (h0 : q.coeff 0 = 0) :
    Tendsto (fun t : ℝ => ‖q.eval (t : ℂ)‖ / t) (𝓝[>] 0) (𝓝 ‖q.coeff 1‖) := by
  obtain ⟨q', rfl⟩ := X_dvd_iff.2 h0
  rw [coeff_X_mul, coeff_zero_eq_eval_zero]
  have h1 : Tendsto (fun t : ℝ => ‖q'.eval (t : ℂ)‖) (𝓝[>] 0) (𝓝 ‖q'.eval ((0:ℝ):ℂ)‖) :=
    (((q'.continuous.comp Complex.continuous_ofReal).norm).tendsto 0).mono_left
      nhdsWithin_le_nhds
  simp only [Complex.ofReal_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [eval_mul, eval_X, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']
  field_simp

/-! ### Factorization `f(t) = f(0) ∏ (1 + aᵢ t)` -/

theorem coeff_prod_one_add (A : Multiset ℂ) :
    ((A.map fun a => 1 + C a * X).prod).coeff 0 = 1 ∧
    ((A.map fun a => 1 + C a * X).prod).coeff 1 = A.sum := by
  induction A using Multiset.induction_on with
  | empty => simp [coeff_one]
  | cons a A ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine ⟨?_, ?_⟩
    · rw [mul_coeff_zero, ih.1]; simp
    · rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, ih.1, ih.2]; ring

/-- A complex polynomial with `f(0) ≠ 0` factors as `f(t) = f(0) ∏ (1 + aᵢ t)`, where
`aᵢ = -ρᵢ⁻¹` for the roots `ρᵢ` of `f`. -/
theorem eq_C_mul_prod_one_add (f : ℂ[X]) (hf : f.coeff 0 ≠ 0) :
    f = C (f.coeff 0) * ((f.roots.map fun ρ => -ρ⁻¹).map fun a => 1 + C a * X).prod := by
  have hs := (IsAlgClosed.splits f).eq_prod_roots
  have hne : ∀ ρ ∈ f.roots, ρ ≠ 0 := by
    intro ρ hρ h0
    subst h0
    have := (mem_roots'.1 hρ).2
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero] at this
    exact hf this
  have hfac : (f.roots.map fun ρ => X - C ρ) =
      f.roots.map fun ρ => C (-ρ) * (1 + C (-ρ⁻¹) * X) := by
    apply Multiset.map_congr rfl
    intro ρ hρ
    have := hne ρ hρ
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul]
    rw [show -ρ * -ρ⁻¹ = 1 by field_simp]
    simp; ring
  have h2 : f = C (f.leadingCoeff * (f.roots.map fun ρ => -ρ).prod) *
      ((f.roots.map fun ρ => -ρ⁻¹).map fun a => 1 + C a * X).prod := by
    conv_lhs => rw [hs, hfac]
    rw [Multiset.prod_map_mul, Multiset.map_map, C_mul, map_multiset_prod C, Multiset.map_map]
    simp only [Function.comp_def]
    ring
  have h3 : f.coeff 0 = f.leadingCoeff * (f.roots.map fun ρ => -ρ).prod := by
    conv_lhs => rw [h2]
    rw [mul_coeff_zero, coeff_C_zero, (coeff_prod_one_add _).1, mul_one]
  rw [h3]
  exact h2

end Gurvits

end AnalyticPart

/-! ## Part: Lemma1 -/

section Lemma1Part

/-!
# Lemma 1

If `p` is H-stable and homogeneous, then `|p(x)| ≥ |p(Re x)|` for every `x ∈ ℂⁿ₊`.

The book considers the univariate polynomial `s ↦ p(x + s Re(x))` and its roots. We use the
equivalent polynomial `R(u) = p(Re x + u (x - Re x))`, which satisfies `R(0) = p(Re x)` and
`R(1) = p(x)`; H-stability and homogeneity force every root `u` of `R` to satisfy
`Re u ≤ 0`, hence `|u| ≤ |1 - u|`, and the factorization of `R` gives `|R(0)| ≤ |R(1)|`.
-/

open MvPolynomial

namespace Gurvits

/-- If every root `u` of a complex polynomial `R` satisfies `|u| ≤ |1 - u|`,
then `|R(0)| ≤ |R(1)|`. -/
theorem norm_eval_zero_le_eval_one (R : Polynomial ℂ) (h : ∀ u ∈ R.roots, ‖u‖ ≤ ‖1 - u‖) :
    ‖R.eval 0‖ ≤ ‖R.eval 1‖ := by
  have hs := (IsAlgClosed.splits R).eq_prod_roots
  rw [hs]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
    Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, norm_mul]
  gcongr
  have key : ∀ (s : Multiset ℂ) (f : ℂ → ℂ),
      ‖(s.map f).prod‖ = (s.map fun x => ‖f x‖).prod := by
    intro s f
    have := map_multiset_prod (normHom : ℂ →*₀ ℝ) (s.map f)
    rw [Multiset.map_map] at this
    exact this
  rw [key, key]
  apply Multiset.prod_map_le_prod_map₀
  · intros; positivity
  · intro u hu; simpa [norm_neg] using h u hu

theorem norm_le_norm_one_sub {u : ℂ} (hu : u.re ≤ 0) : ‖u‖ ≤ ‖1 - u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

variable {n d : ℕ}

theorem eval_aeval_line (p : MvPolynomial (Fin n) ℝ) (a b : Fin n → ℂ) (u : ℂ) :
    (aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X) p).eval u =
      aeval (fun i => a i + b i * u) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Polynomial.eval_C, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, Polynomial.eval_mul, hp, aeval_X, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]

/-- Lemma 1 on the open half-plane `ℂⁿ₊₊`. -/
theorem lemma1_open {p : MvPolynomial (Fin n) ℝ} (hhom : p.IsHomogeneous d) (hst : IsHStable p)
    (x : Fin n → ℂ) (hx : ∀ i, 0 < (x i).re) :
    |eval (fun i => (x i).re) p| ≤ ‖aeval x p‖ := by
  set r : Fin n → ℝ := fun i => (x i).re with hr
  set R : Polynomial ℂ :=
    aeval (fun i => Polynomial.C ((r i : ℂ)) + Polynomial.C (x i - r i) * Polynomial.X) p
  have hR : ∀ u, R.eval u = aeval (fun i => (r i : ℂ) + (x i - r i) * u) p :=
    fun u => eval_aeval_line p _ _ u
  have h0 : R.eval 0 = (eval r p : ℂ) := by
    rw [hR]; simp only [mul_zero, add_zero]; exact aeval_ofReal p r
  have h1 : R.eval 1 = aeval x p := by
    rw [hR]; simp
  have key := norm_eval_zero_le_eval_one R (fun u hu => by
    apply norm_le_norm_one_sub
    by_contra hpos
    push Not at hpos
    have hu0 : u ≠ 0 := by rintro rfl; simp at hpos
    have hroot : R.eval u = 0 := (Polynomial.mem_roots'.1 hu).2
    set w : Fin n → ℂ := fun i => (r i : ℂ) * u⁻¹ + (x i - r i) with hw
    have hwpos : ∀ i, 0 < (w i).re := by
      intro i
      have hinv : 0 < (u⁻¹).re := by
        rw [Complex.inv_re]; exact div_pos hpos (Complex.normSq_pos.2 hu0)
      simp only [hw, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, zero_mul, sub_zero, hr]
      have := hx i
      nlinarith
    have hsmul : u • w = fun i => (r i : ℂ) + (x i - r i) * u := by
      ext i
      simp only [hw, Pi.smul_apply, smul_eq_mul]
      field_simp
    have := aeval_smul_of_isHomogeneous hhom u w
    rw [hsmul, ← hR, hroot] at this
    exact mul_ne_zero (pow_ne_zero _ hu0) (hst w hwpos) this.symm)
  rw [h0, h1, Complex.norm_real, Real.norm_eq_abs] at key
  exact key

/-- **Lemma 1.** If `p` is H-stable and homogeneous, then `|p(x)| ≥ |p(Re x)|` for every
`x ∈ ℂⁿ₊` (closed right half-plane). -/
theorem lemma1 {p : MvPolynomial (Fin n) ℝ} (hhom : p.IsHomogeneous d) (hst : IsHStable p)
    (x : Fin n → ℂ) (hx : ∀ i, 0 ≤ (x i).re) :
    |eval (fun i => (x i).re) p| ≤ ‖aeval x p‖ := by
  have hcont1 : Continuous fun ε : ℝ => ‖aeval (fun i => x i + (ε : ℂ)) p‖ := by
    refine Continuous.norm ?_
    have : (fun ε : ℝ => aeval (fun i => x i + (ε : ℂ)) p) =
        fun ε : ℝ => eval (fun i => x i + (ε : ℂ)) (map (algebraMap ℝ ℂ) p) := by
      ext ε; rw [aeval_def, eval_map]
    rw [this]
    exact (continuous_eval _).comp (continuous_pi fun i =>
      continuous_const.add Complex.continuous_ofReal)
  have hcont2 : Continuous fun ε : ℝ => |eval (fun i => (x i).re + ε) p| :=
    ((continuous_eval _).comp (continuous_pi fun i => continuous_const.add continuous_id)).abs
  have hle : ∀ ε : ℝ, 0 < ε →
      |eval (fun i => (x i).re + ε) p| ≤ ‖aeval (fun i => x i + (ε : ℂ)) p‖ := by
    intro ε hε
    have := lemma1_open hhom hst (fun i => x i + (ε : ℂ)) (fun i => by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith [hx i])
    simpa using this
  have h1 := (hcont1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h2 := (hcont2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have := le_of_tendsto_of_tendsto h2 h1
    (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  simpa using this

end Gurvits

end Lemma1Part

/-! ## Part: Lemma2 -/

section Lemma2Part

/-!
# Lemma 2

If `p ∈ ℝ₊[x₀, …, xₙ]` is homogeneous of degree `n + 1`, then for every `r ∈ ℝⁿ₊₊` with
`∏ rⱼ = 1` and every `t > 0` we have `cap(p) ≤ p(t, r) / t`.

(Recall that in this formalization the distinguished variable is `x₀` rather than `xₙ`, so the
book's `p(Re(y), t)` is written `p(t, Re(y))`.)
-/

open MvPolynomial

namespace Gurvits

variable {n : ℕ}

/-- **Lemma 2** (real form). -/
theorem lemma2_real {p : MvPolynomial (Fin (n + 1)) ℝ} (hnn : NonnegCoeffs p)
    (hhom : p.IsHomogeneous (n + 1)) {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    (hprod : ∏ j, r j = 1) {t : ℝ} (ht : 0 < t) :
    cap p ≤ eval (Fin.cons t r : Fin (n + 1) → ℝ) p / t := by
  set l : ℝ := t ^ (-(1:ℝ) / (n + 1)) with hl
  have hl0 : 0 < l := Real.rpow_pos_of_pos ht _
  have hln : l ^ (n + 1) = t⁻¹ := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1:ℝ) / (n + 1) * (n + 1) = -1 by field_simp, Real.rpow_neg_one]
  set xb : Fin (n + 1) → ℝ := l • (Fin.cons t r : Fin (n + 1) → ℝ) with hxb
  have hxb0 : ∀ i, 0 ≤ xb i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hxb, Pi.smul_apply, Fin.cons_zero, smul_eq_mul]; positivity
    · simp only [hxb, Pi.smul_apply, Fin.cons_succ, smul_eq_mul]; exact (mul_pos hl0 (hr j)).le
  have hxb1 : ∏ i, xb i = 1 := by
    simp only [hxb, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      hprod, hln]
    field_simp
  have h := cap_le_eval hnn hxb0 hxb1
  rw [hxb, eval_smul_of_isHomogeneous hhom, hln] at h
  rwa [inv_mul_eq_div] at h

/-- **Lemma 2.** Let `y ∈ ℂⁿ₊₊` with `∏ Re(yⱼ) = 1`. Then `cap(p) ≤ p(t, Re y) / t` for every
`t > 0`. -/
theorem lemma2 {p : MvPolynomial (Fin (n + 1)) ℝ} (hnn : NonnegCoeffs p)
    (hhom : p.IsHomogeneous (n + 1)) {y : Fin n → ℂ} (hy : ∀ j, 0 < (y j).re)
    (hprod : ∏ j, (y j).re = 1) {t : ℝ} (ht : 0 < t) :
    cap p ≤ eval (Fin.cons t (fun j => (y j).re) : Fin (n + 1) → ℝ) p / t :=
  lemma2_real hnn hhom hy hprod ht

end Gurvits

end Lemma2Part

/-! ## Part: Gurvits -/

section GurvitsPart

/-!
# Gurvits' Proposition

If `p ∈ ℝ₊[x₀, …, xₙ]` is H-stable and homogeneous of degree `n + 1`, then either `p' ≡ 0` or
`p'` is H-stable, `p'` is homogeneous of degree `n`, and `cap(p') ≥ cap(p) · g(deg₀ p)`.

The proof follows the book. For `y ∈ ℂⁿ₊₊` we study the univariate polynomial
`f(t) = p(t, y)`, whose coefficient of `t` is `p'(y)`.

* If `f(0) = 0` (Case 1), Lemma 1 and Lemma 2 give `cap(p) ≤ p'(Re y) ≤ |p'(y)|`, through the
  limit `t → 0⁺` of `p(t, ·)/t`.
* If `f(0) ≠ 0` we factor `f(t) = f(0) ∏ (1 + aᵢ t)`. The heart of the proof (the Claim) is
  that every root `ρ = -aᵢ⁻¹` of `f` satisfies `Re(λρ) ≤ 0` whenever `Re(λ yⱼ) > 0` for all
  `j`. This is the step where the book applies Farkas' Lemma; we use the consequence directly:
  `Re aᵢ > 0`, and `aᵢ > 0` is real when `y` is real. When all `aᵢ` vanish (`f` constant) the
  conclusions follow from Lemma 1 (this covers the book's Case 2 when `f` is constant). In the
  remaining case (the book's Cases 2 and 3 together) `p'(y) = f(0) ∑ aᵢ ≠ 0`, and for real `y`
  the AM-GM inequality together with Lemma 2 gives `p'(y) ≥ cap(p) g(k)`.
-/

open MvPolynomial Filter Topology

namespace Gurvits

variable {n : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ}

/-! ### Small helper facts -/

theorem re_multiset_sum (A : Multiset ℂ) : A.sum.re = (A.map Complex.re).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [ih]

theorem re_multiset_sum_pos (A : Multiset ℂ) (hA : A ≠ 0) (h : ∀ a ∈ A, 0 < a.re) :
    0 < A.sum.re := by
  induction A using Multiset.induction_on with
  | empty => exact absurd rfl hA
  | cons a A ih =>
    rw [Multiset.sum_cons, Complex.add_re]
    have ha := h a (Multiset.mem_cons_self a A)
    by_cases hA' : A = 0
    · subst hA'; simpa using ha
    · have := ih hA' fun b hb => h b (Multiset.mem_cons_of_mem hb)
      linarith

/-- For a real polynomial with nonnegative coefficients and `t ≥ 0`: `q₁ t ≤ q(t)`. -/
theorem coeff_one_mul_le_eval (q : Polynomial ℝ) (hq : ∀ i, 0 ≤ q.coeff i) {t : ℝ}
    (ht : 0 ≤ t) : q.coeff 1 * t ≤ q.eval t := by
  rw [Polynomial.eval_eq_sum_range' (n := q.natDegree + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Finset.range (q.natDegree + 2) := by simp
  have := Finset.single_le_sum (f := fun i => q.coeff i * t ^ i)
    (fun i _ => mul_nonneg (hq i) (pow_nonneg ht i)) h1
  simpa using this

/-- `Re(x)` of the point `(t, y)` is `(t, Re y)` for real `t`. -/
theorem re_cons (t : ℝ) (y : Fin n → ℂ) :
    (fun i => ((Fin.cons (t : ℂ) y : Fin (n + 1) → ℂ) i).re) =
      (Fin.cons t (fun j => (y j).re) : Fin (n + 1) → ℝ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Consequence of Lemma 1 for the slices: `p(t, Re y) ≤ |p(t, y)|` for `t ≥ 0`. -/
theorem sliceR_le_norm_sliceC (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p)
    {y : Fin n → ℂ} (hy : ∀ j, 0 ≤ (y j).re) {t : ℝ} (ht : 0 ≤ t) :
    (sliceR p (fun j => (y j).re)).eval t ≤ ‖(sliceC p y).eval (t : ℂ)‖ := by
  have h := lemma1 hhom hst (Fin.cons (t : ℂ) y) (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ht
    · simpa using hy j)
  rw [re_cons] at h
  rw [sliceR_eval, sliceC_eval]
  exact (le_abs_self _).trans h

theorem re_one_add_mul_I (s : ℝ) (z : ℂ) : ((1 + s * Complex.I) * z).re = z.re - s * z.im := by
  simp [Complex.mul_re]

/-! ### The Claim: location of the roots of `t ↦ p(t, y)` -/

/-- If `ρ` is a root of `t ↦ p(t, y)` and `Re(λ yⱼ) > 0` for all `j`, then `Re(λ ρ) ≤ 0`
(otherwise `(λρ, λy) ∈ ℂⁿ⁺¹₊₊` would be a root of `p`). -/
theorem root_re_le (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {y : Fin n → ℂ}
    {ρ : ℂ} (hρ : (sliceC p y).eval ρ = 0) (l : ℂ) (hl : ∀ j, 0 < (l * y j).re) :
    (l * ρ).re ≤ 0 := by
  by_contra h
  push Not at h
  have hpos : ∀ i, 0 < ((l • (Fin.cons ρ y : Fin (n + 1) → ℂ)) i).re := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h
    · simpa using hl j
  have := hst _ hpos
  rw [aeval_smul_of_isHomogeneous hhom, ← sliceC_eval, hρ, mul_zero] at this
  exact this rfl

/-- Every nonzero root `ρ` of `t ↦ p(t, y)`, `y ∈ ℂⁿ₊₊`, has `Re ρ < 0`. -/
theorem root_re_neg (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {y : Fin n → ℂ}
    (hy : ∀ j, 0 < (y j).re) {ρ : ℂ} (hρ : (sliceC p y).eval ρ = 0) (hρ0 : ρ ≠ 0) :
    ρ.re < 0 := by
  have hev : ∀ᶠ δ in 𝓝 (0:ℝ), ∀ j, 0 < (y j).re - δ * |(y j).im| := by
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous fun δ : ℝ => (y j).re - δ * |(y j).im| := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hy j)
  obtain ⟨δ, hδ, hδ0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)))
      |>.exists)
  have hδ0 : (0:ℝ) < δ := hδ0
  have h1 := root_re_le hhom hst hρ (1 + (δ : ℝ) * Complex.I) (fun j => by
    rw [re_one_add_mul_I]
    have := hδ j
    have := mul_le_mul_of_nonneg_left (le_abs_self (y j).im) hδ0.le
    linarith)
  have h2 := root_re_le hhom hst hρ (1 + ((-δ : ℝ)) * Complex.I) (fun j => by
    rw [re_one_add_mul_I]
    have := hδ j
    have := mul_le_mul_of_nonneg_left (neg_abs_le (y j).im) hδ0.le
    linarith)
  rw [re_one_add_mul_I] at h1 h2
  rcases lt_or_eq_of_le (show ρ.re ≤ 0 by nlinarith) with h | h
  · exact h
  · exfalso
    have him : ρ.im = 0 := by
      have : δ * ρ.im = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact h'
    exact hρ0 (Complex.ext h him)

/-- For real positive `y`, every root of `t ↦ p(t, y)` is real. -/
theorem root_im_eq_zero (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {ρ : ℂ} (hρ : (sliceC p (fun j => (r j : ℂ))).eval ρ = 0) :
    ρ.im = 0 := by
  by_contra him
  have h := root_re_le hhom hst hρ (1 + ((ρ.re - 1) / ρ.im : ℝ) * Complex.I) (fun j => by
    rw [re_one_add_mul_I]; simpa using hr j)
  rw [re_one_add_mul_I] at h
  have : (ρ.re - 1) / ρ.im * ρ.im = ρ.re - 1 := div_mul_cancel₀ _ him
  linarith

/-! ### Conditions (I) and (II) -/

/-- **(I)** If `p'(y) = 0` for some `y ∈ ℂⁿ₊₊`, then `p' ≡ 0`. -/
theorem pDeriv_eq_zero_of_aeval_eq_zero (hnn : NonnegCoeffs p)
    (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {y : Fin n → ℂ}
    (hy : ∀ j, 0 < (y j).re) (h : aeval y (pDeriv p) = 0) : pDeriv p = 0 := by
  set r : Fin n → ℝ := fun j => (y j).re with hr
  set f := sliceC p y with hf
  set fr := sliceR p r with hfr
  have hr0 : ∀ j, 0 < r j := hy
  have hfr_nonneg : ∀ i, 0 ≤ fr.coeff i := sliceR_coeff_nonneg hnn (fun j => (hr0 j).le)
  have hle : ∀ t : ℝ, 0 ≤ t → fr.eval t ≤ ‖f.eval (t : ℂ)‖ :=
    fun t ht => sliceR_le_norm_sliceC hhom hst (fun j => (hy j).le) ht
  have hf1 : f.coeff 1 = 0 := by rw [hf, sliceC_coeff_one, h]
  suffices hc : fr.coeff 1 ≤ 0 by
    refine eq_zero_of_eval_eq_zero (pDeriv_nonnegCoeffs hnn) hr0 ?_
    rw [← sliceR_coeff_one]
    exact le_antisymm hc (hfr_nonneg 1)
  by_cases h0 : f.coeff 0 = 0
  · -- Case 1: `p(0, y) = 0`.
    have hfr0 : fr.coeff 0 = 0 := by
      have := hle 0 le_rfl
      rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero,
        ← Polynomial.coeff_zero_eq_eval_zero, h0, norm_zero] at this
      exact le_antisymm this (hfr_nonneg 0)
    have hlim1 := tendsto_eval_div_real fr hfr0
    have hlim2 := tendsto_norm_eval_div f h0
    rw [hf1, norm_zero] at hlim2
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_le_div_of_nonneg_right (hle t (le_of_lt ht)) (le_of_lt ht)
  · -- `p(0, y) ≠ 0`: factor `f(t) = f(0) ∏ (1 + aᵢ t)`.
    set A := f.roots.map fun ρ => -ρ⁻¹ with hA
    have hfac := eq_C_mul_prod_one_add f h0
    rw [← hA] at hfac
    have hApos : ∀ a ∈ A, 0 < a.re := by
      intro a ha
      obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.1 ha
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        have := (Polynomial.mem_roots'.1 hρ).2
        rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at this
        exact h0 this
      have hre := root_re_neg hhom hst hy (Polynomial.mem_roots'.1 hρ).2 hρ0
      rw [Complex.neg_re, Complex.inv_re]
      have := Complex.normSq_pos.2 hρ0
      have : ρ.re / Complex.normSq ρ < 0 := div_neg_of_neg_of_pos hre this
      linarith
    have hcoeff1 : f.coeff 1 = f.coeff 0 * A.sum := by
      conv_lhs => rw [hfac]
      rw [Polynomial.coeff_C_mul, (coeff_prod_one_add A).2]
    have hA0 : A = 0 := by
      by_contra hA0
      have := re_multiset_sum_pos A hA0 hApos
      rw [hf1] at hcoeff1
      have hsum : A.sum = 0 := by
        rcases mul_eq_zero.1 hcoeff1.symm with h' | h'
        · exact absurd h' h0
        · exact h'
      rw [hsum] at this
      simp at this
    have hconst : ∀ t : ℂ, f.eval t = f.coeff 0 := by
      intro t
      conv_lhs => rw [hfac, hA0]
      simp
    apply le_zero_of_forall_le_div (a := ‖f.coeff 0‖)
    intro t ht
    rw [le_div_iff₀ ht]
    calc fr.coeff 1 * t ≤ fr.eval t := coeff_one_mul_le_eval fr hfr_nonneg ht.le
      _ ≤ ‖f.eval (t : ℂ)‖ := hle t ht.le
      _ = ‖f.coeff 0‖ := by rw [hconst]

/-- **(II)** For `y ∈ ℝⁿ₊₊` with `∏ yⱼ = 1`: `p'(y) ≥ cap(p) · g(deg₀ p)`. -/
theorem cap_mul_gfun_le_eval_pDeriv (hnn : NonnegCoeffs p)
    (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) (hprod : ∏ j, r j = 1) :
    cap p * gfun (p.degreeOf 0) ≤ eval r (pDeriv p) := by
  set k := p.degreeOf 0 with hk
  set fr := sliceR p r with hfr
  set f := sliceC p (fun j => (r j : ℂ)) with hf
  have hfmap : f = Polynomial.map Complex.ofRealHom fr := sliceC_ofReal p r
  have hfr_nonneg : ∀ i, 0 ≤ fr.coeff i := sliceR_coeff_nonneg hnn (fun j => (hr j).le)
  have hcap : ∀ t : ℝ, 0 < t → cap p ≤ fr.eval t / t := by
    intro t ht
    rw [hfr, sliceR_eval]
    exact lemma2_real hnn hhom hr hprod ht
  have hcap0 : 0 ≤ cap p := cap_nonneg hnn
  rw [← sliceR_coeff_one]
  by_cases h0 : fr.coeff 0 = 0
  · -- Case 1: `p(0, y) = 0`; then `cap(p) ≤ p'(y)`.
    have hlim := tendsto_eval_div_real fr h0
    have hle : cap p ≤ fr.coeff 1 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hcap t ht
    calc cap p * gfun k ≤ cap p * 1 := mul_le_mul_of_nonneg_left (gfun_le_one k) hcap0
      _ = cap p := mul_one _
      _ ≤ fr.coeff 1 := hle
  · -- `p(0, y) ≠ 0`: all `aᵢ` are positive reals; AM-GM and Lemma 2.
    have hf0 : f.coeff 0 ≠ 0 := by
      rw [hfmap, Polynomial.coeff_map]
      simpa using h0
    set A := f.roots.map fun ρ => -ρ⁻¹ with hA
    have hfac := eq_C_mul_prod_one_add f hf0
    rw [← hA] at hfac
    have hAreal : ∀ a ∈ A, a.im = 0 ∧ 0 < a.re := by
      intro a ha
      obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.1 ha
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        have := (Polynomial.mem_roots'.1 hρ).2
        rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at this
        exact hf0 this
      have hroot := (Polynomial.mem_roots'.1 hρ).2
      have hre := root_re_neg hhom hst (y := fun j => (r j : ℂ)) (fun j => by simpa using hr j)
        hroot hρ0
      have him := root_im_eq_zero hhom hst hr hroot
      refine ⟨?_, ?_⟩
      · rw [Complex.neg_im, Complex.inv_im, him]; simp
      · rw [Complex.neg_re, Complex.inv_re]
        have := Complex.normSq_pos.2 hρ0
        have : ρ.re / Complex.normSq ρ < 0 := div_neg_of_neg_of_pos hre this
        linarith
    set B := A.map Complex.re with hB
    have hAB : A = B.map Complex.ofReal := by
      rw [hB, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id A]
      apply Multiset.map_congr rfl
      intro a ha
      exact (Complex.ext (by simp) (by simp [(hAreal a ha).1])).symm
    clear_value B
    have hBpos : ∀ b ∈ B, 0 ≤ b := by
      intro b hb
      rw [hB] at hb
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
      exact (hAreal a ha).2.le
    have hBcard : B.card ≤ k := by
      rw [hB, Multiset.card_map, hA, Multiset.card_map]
      exact (Polynomial.card_roots' f).trans (sliceC_natDegree_le p _)
    have hc0 : f.coeff 0 = (fr.coeff 0 : ℂ) := by
      rw [hfmap, Polynomial.coeff_map]; rfl
    -- `p(t, y) = p(0, y) ∏ (1 + bᵢ t)`
    have heval : ∀ t : ℝ, fr.eval t = fr.coeff 0 * (B.map fun b => 1 + b * t).prod := by
      intro t
      have h1 : f.eval (t : ℂ) = ((Polynomial.eval t fr : ℝ) : ℂ) := by
        rw [hfmap, Polynomial.eval_map]; exact Polynomial.eval₂_at_apply _ _
      have h2 : f.eval (t : ℂ) = ((fr.coeff 0 * (B.map fun b => 1 + b * t).prod : ℝ) : ℂ) := by
        have hm := map_multiset_prod Complex.ofRealHom (B.map fun b => 1 + b * t)
        simp only [Complex.ofRealHom_eq_coe] at hm
        conv_lhs => rw [hfac]
        rw [hc0, hAB, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
          Multiset.map_map, Complex.ofReal_mul, hm, Multiset.map_map]
        congr 2
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro b _
        simp
      exact_mod_cast h1.symm.trans h2
    -- `p'(y) = p(0, y) ∑ bᵢ`
    have hcoeff1 : fr.coeff 1 = fr.coeff 0 * B.sum := by
      have h1 : f.coeff 1 = f.coeff 0 * A.sum := by
        conv_lhs => rw [hfac]
        rw [Polynomial.coeff_C_mul, (coeff_prod_one_add A).2]
      have h2 : f.coeff 1 = (fr.coeff 1 : ℂ) := by
        rw [hfmap, Polynomial.coeff_map]; rfl
      rw [h2, hc0, hAB] at h1
      have h3 : (B.map Complex.ofReal).sum = ((B.sum : ℝ) : ℂ) :=
        (map_multiset_sum Complex.ofRealHom B).symm
      rw [h3] at h1
      exact_mod_cast h1
    have hc0nn : 0 ≤ fr.coeff 0 := hfr_nonneg 0
    have hS : 0 ≤ B.sum := Multiset.sum_nonneg hBpos
    rw [hcoeff1]
    refine key_opt hc0nn hS fun t ht => ?_
    refine (hcap t ht).trans ?_
    rw [heval t]
    gcongr
    exact amgm_one_add B hBpos hBcard ht.le

/-! ### Gurvits' Proposition -/

/-- **Gurvits' Proposition.** If `p ∈ ℝ₊[x₀, …, xₙ]` is H-stable and homogeneous of degree
`n + 1`, then either `p' ≡ 0` or `p'` is H-stable; `p'` is homogeneous of degree `n`; and
in either case `cap(p') ≥ cap(p) · g(deg₀ p)`. -/
theorem gurvits_proposition (hnn : NonnegCoeffs p) (hhom : p.IsHomogeneous (n + 1))
    (hst : IsHStable p) :
    (pDeriv p = 0 ∨ IsHStable (pDeriv p)) ∧ (pDeriv p).IsHomogeneous n ∧
      cap p * gfun (p.degreeOf 0) ≤ cap (pDeriv p) := by
  refine ⟨?_, pDeriv_isHomogeneous hhom, ?_⟩
  · by_cases h : pDeriv p = 0
    · exact Or.inl h
    · exact Or.inr fun y hy h' => h (pDeriv_eq_zero_of_aeval_eq_zero hnn hhom hst hy h')
  · refine le_cap fun x hx0 hx1 => ?_
    have hxpos : ∀ j, 0 < x j := by
      intro j
      rcases (hx0 j).lt_or_eq with h | h
      · exact h
      · exfalso
        have : ∏ i, x i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
        rw [hx1] at this
        exact one_ne_zero this
    exact cap_mul_gfun_le_eval_pDeriv hnn hhom hst hxpos hx1

end Gurvits

end GurvitsPart

/-! ## Part: MatrixPoly -/

section MatrixPolyPart

/-!
# The polynomial `p_M` of a matrix

For a square matrix `M` we study `p_M(x) = ∏ᵢ (∑ⱼ mᵢⱼ xⱼ)`:

* it is homogeneous of degree `n` and has nonnegative coefficients when `M ≥ 0`;
* **Fact A**: `per M` is the coefficient of `x₁ ⋯ xₙ` in `p_M`;
* **Fact B**: the degree of `xⱼ` in `p_M` is at most `λ_M(j)`, the number of nonzero entries
  in the `j`-th column;
* **Claim 1**: `p_M` is H-stable when `M` is doubly stochastic;
* **Claim 2**: `cap(p_M) = 1` when `M` is doubly stochastic.
-/

open MvPolynomial

namespace Gurvits

variable {σ : Type*} {n : ℕ}

/-! ### Nonnegative coefficients -/

theorem NonnegCoeffs.add {p q : MvPolynomial σ ℝ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p + q) := fun d => by simpa using add_nonneg (hp d) (hq d)

theorem NonnegCoeffs.mul {p q : MvPolynomial σ ℝ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p * q) := fun d => by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem NonnegCoeffs.zero : NonnegCoeffs (0 : MvPolynomial σ ℝ) := fun d => by simp

theorem NonnegCoeffs.one : NonnegCoeffs (1 : MvPolynomial σ ℝ) := fun d => by
  classical
  rw [coeff_one]; split_ifs <;> norm_num

theorem NonnegCoeffs.C_mul_X {a : ℝ} (ha : 0 ≤ a) (i : σ) : NonnegCoeffs (C a * X i) := fun d => by
  classical
  rw [coeff_C_mul, X, coeff_monomial]; split_ifs <;> simp [ha]

theorem NonnegCoeffs.sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, NonnegCoeffs (f i)) : NonnegCoeffs (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NonnegCoeffs.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem NonnegCoeffs.prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, NonnegCoeffs (f i)) : NonnegCoeffs (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NonnegCoeffs.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Basic properties of `p_M` -/

theorem matrixPoly_nonnegCoeffs {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    NonnegCoeffs (matrixPoly M) :=
  NonnegCoeffs.prod _ _ fun i _ => NonnegCoeffs.sum _ _ fun j _ => NonnegCoeffs.C_mul_X (hM i j) j

/-- `p_M` is homogeneous of degree `n`. -/
theorem matrixPoly_isHomogeneous (M : Matrix (Fin n) (Fin n) ℝ) :
    (matrixPoly M).IsHomogeneous n := by
  have := IsHomogeneous.prod (Finset.univ : Finset (Fin n)) (fun i => ∑ j, C (M i j) * X j)
    (fun _ => 1) (fun i _ => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)
  unfold matrixPoly
  simpa using this

theorem aeval_matrixPoly (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    aeval z (matrixPoly M) = ∏ i, ∑ j, (M i j : ℂ) * z j := by
  simp [matrixPoly, map_prod, map_sum]

theorem eval_matrixPoly (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (matrixPoly M) = ∏ i, ∑ j, M i j * x j := by
  simp [matrixPoly, map_prod, map_sum]

/-! ### Fact A -/

theorem sum_single_eq_allOnes_iff (s : Fin n → Fin n) :
    (∑ i, Finsupp.single (s i) 1 : Fin n →₀ ℕ) = allOnes n ↔ Function.Bijective s := by
  classical
  have hval : ∀ j, (∑ i, Finsupp.single (s i) 1 : Fin n →₀ ℕ) j =
      (Finset.univ.filter fun i => s i = j).card := by
    intro j
    rw [Chapter24Aux.finsupp_sum_apply, Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.single_apply]
  constructor
  · intro h
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    have h1 : (Finset.univ.filter fun i => s i = s a).card = 1 := by
      rw [← hval, h]; simp [allOnes]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h1
    have ha : a ∈ Finset.univ.filter fun i => s i = s a := by simp
    have hb : b ∈ Finset.univ.filter fun i => s i = s a := by simp [hab]
    rw [hc, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · intro h
    ext j
    have h1 : allOnes n j = 1 := by simp [allOnes]
    rw [hval, h1, Finset.card_eq_one]
    obtain ⟨a, ha⟩ := h.2 j
    refine ⟨a, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi; exact h.1 (hi.trans ha.symm)
    · rintro rfl; exact ha

/-- **Fact A.** `per M` is the coefficient of `x₁ x₂ ⋯ xₙ` in `p_M`. -/
theorem topCoeff_matrixPoly (M : Matrix (Fin n) (Fin n) ℝ) :
    topCoeff (matrixPoly M) = M.permanent := by
  classical
  unfold topCoeff matrixPoly
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  have hterm : ∀ s : Fin n → Fin n, ∏ i, C (M i (s i)) * X (s i) =
      (monomial (∑ i, Finsupp.single (s i) 1) (∏ i, M i (s i)) : MvPolynomial (Fin n) ℝ) := by
    intro s
    rw [Finset.prod_mul_distrib, monomial_sum_index, ← map_prod]
    rfl
  simp only [hterm, coeff_monomial, sum_single_eq_allOnes_iff]
  rw [← Finset.sum_filter]
  have himage : (Finset.univ.image fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) =
      Finset.univ.filter Function.Bijective := by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨e, rfl⟩; exact e.bijective
    · intro hs; exact ⟨Equiv.ofBijective s hs, rfl⟩
  rw [← himage, Finset.sum_image (fun e₁ _ e₂ _ h => Equiv.ext (congrFun h))]
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  rfl

/-! ### Fact B -/

theorem degreeOf_row_le (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    degreeOf j (∑ k, C (M i k) * X k) ≤ if M i j = 0 then 0 else 1 := by
  classical
  split_ifs with h
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
    by_cases hk : k = j
    · subst hk; simp [h]
    · refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C, degreeOf_X]; simp [Ne.symm hk]
  · have := (degreeOf_le_totalDegree (∑ k, C (M i k) * X k) j).trans
      (IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X (M i k) k).totalDegree_le
    exact this

/-- **Fact B.** The degree of `xⱼ` in `p_M` is at most `λ_M(j)`. -/
theorem degreeOf_matrixPoly_le (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    degreeOf j (matrixPoly M) ≤ colNonzero M j := by
  classical
  unfold matrixPoly colNonzero
  refine (degreeOf_prod_le _ _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => degreeOf_row_le M i j).trans ?_
  rw [Finset.card_filter]
  apply le_of_eq
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all

/-! ### Claims 1 and 2 -/

/-- **Claim 1.** If `M` is doubly stochastic, then `p_M` is H-stable. -/
theorem matrixPoly_isHStable {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) : IsHStable (matrixPoly M) := by
  intro z hz
  rw [aeval_matrixPoly, Finset.prod_ne_zero_iff]
  intro i _ h0
  have hre : (∑ j, (M i j : ℂ) * z j).re = ∑ j, M i j * (z j).re := by
    rw [Complex.re_sum]; simp
  have hrow := sum_row_of_mem_doublyStochastic hM i
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, 0 < M i l := by
    by_contra hcon
    push Not at hcon
    have : ∑ j, M i j ≤ 0 := Finset.sum_nonpos fun j _ => hcon j (Finset.mem_univ j)
    linarith
  have hpos : 0 < ∑ j, M i j * (z j).re :=
    Finset.sum_pos' (fun j _ => mul_nonneg (nonneg_of_mem_doublyStochastic hM)
      (hz j).le) ⟨l, Finset.mem_univ _, mul_pos hl (hz l)⟩
  rw [← hre, h0, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

/-- `p_M(x) ≥ ∏ xⱼ` for `x ≥ 0` (weighted AM-GM), when `M` is doubly stochastic. -/
theorem prod_le_eval_matrixPoly {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j) :
    ∏ j, x j ≤ eval x (matrixPoly M) := by
  rw [eval_matrixPoly]
  have hM0 : ∀ i j, 0 ≤ M i j := fun i j => nonneg_of_mem_doublyStochastic hM
  calc ∏ j, x j = ∏ j, x j ^ (∑ i, M i j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sum_col_of_mem_doublyStochastic hM j, Real.rpow_one]
    _ = ∏ i, ∏ j, x j ^ M i j := by
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun j _ => ?_
        exact Real.rpow_sum_of_nonneg (hx j) fun i _ => hM0 i j
    _ ≤ ∏ i, ∑ j, M i j * x j := by
        refine Chapter24Aux.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ =>
          Real.rpow_nonneg (hx j) _) fun i _ => ?_
        exact Real.geom_mean_le_arith_mean_weighted _ _ _ (fun j _ => hM0 i j)
          (sum_row_of_mem_doublyStochastic hM i) (fun j _ => hx j)

/-- **Claim 2.** If `M` is doubly stochastic, then `cap(p_M) = 1`. -/
theorem cap_matrixPoly {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) : cap (matrixPoly M) = 1 := by
  apply le_antisymm
  · have := cap_le_eval (matrixPoly_nonnegCoeffs (M := M) fun i j =>
      nonneg_of_mem_doublyStochastic hM) (x := fun _ => 1) (fun _ => zero_le_one)
      (by simp)
    rw [eval_matrixPoly] at this
    simpa [sum_row_of_mem_doublyStochastic hM] using this
  · exact le_cap fun x hx0 hx1 => hx1 ▸ prod_le_eval_matrixPoly hM hx0

end Gurvits

end MatrixPolyPart

/-! ## Part: Theorem -/

section TheoremPart

/-!
# Proof of the inequality `per M ≥ n!/nⁿ`

Starting from `q_n = p` and passing repeatedly to `q_{i-1} = q_i'`, Gurvits' Proposition gives
`cap(q_{i-1}) ≥ cap(q_i) g(deg q_i) ≥ cap(q_i) g(i)` (the latter because `g` is non-increasing
and `deg q_i ≤ i` by homogeneity), and `q_0` is the coefficient of `x₁ ⋯ xₙ` in `p`.
-/

open MvPolynomial

namespace Gurvits

theorem cap_zero (n : ℕ) : cap (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  apply le_antisymm
  · have := cap_le_eval (p := (0 : MvPolynomial (Fin n) ℝ)) NonnegCoeffs.zero
      (x := fun _ => 1) (fun _ => zero_le_one) (by simp)
    simpa using this
  · exact cap_nonneg NonnegCoeffs.zero

/-- Iterating Gurvits' Proposition along the chain `p = qₙ, qₙ₋₁ = qₙ', …, q₀`:
if `p ∈ ℝ₊[x₁, …, xₙ]` is homogeneous of degree `n` and H-stable (or zero), then the
coefficient `q₀` of `x₁ ⋯ xₙ` satisfies `q₀ ≥ cap(p) ∏_{i=1}^n g(i)`. -/
theorem cap_mul_prod_gfun_le_topCoeff : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
    NonnegCoeffs p → p.IsHomogeneous n → (p = 0 ∨ IsHStable p) →
    cap p * ∏ i ∈ Finset.range n, gfun (i + 1) ≤ topCoeff p
  | 0, p, _, _, _ => by
    have : allOnes 0 = 0 := Subsingleton.elim _ _
    simp [cap_fin_zero, topCoeff, this]
  | n + 1, p, hnn, hhom, hst => by
    rcases hst with rfl | hst
    · simp [cap_zero, topCoeff]
    obtain ⟨h1, -, h3⟩ := gurvits_proposition hnn hhom hst
    have IH := cap_mul_prod_gfun_le_topCoeff n (pDeriv p) (pDeriv_nonnegCoeffs hnn)
      (pDeriv_isHomogeneous hhom) h1
    rw [topCoeff_pDeriv] at IH
    have hprod_nn : 0 ≤ ∏ i ∈ Finset.range n, gfun (i + 1) :=
      Finset.prod_nonneg fun i _ => (gfun_pos _).le
    have hcap := cap_nonneg hnn
    have hg : cap p * gfun (n + 1) ≤ cap (pDeriv p) :=
      (mul_le_mul_of_nonneg_left (gfun_antitone (degreeOf_le_of_isHomogeneous hhom 0)) hcap).trans
        h3
    calc cap p * ∏ i ∈ Finset.range (n + 1), gfun (i + 1)
        = cap p * gfun (n + 1) * ∏ i ∈ Finset.range n, gfun (i + 1) := by
          rw [Finset.prod_range_succ]; ring
      _ ≤ cap (pDeriv p) * ∏ i ∈ Finset.range n, gfun (i + 1) :=
          mul_le_mul_of_nonneg_right hg hprod_nn
      _ ≤ topCoeff p := IH

/-- **Van der Waerden's permanent conjecture (Egorychev–Falikman), inequality part.**
For every doubly stochastic `n × n` matrix `M`, `per M ≥ n!/nⁿ`. -/
theorem permanent_ge {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ M.permanent := by
  have h := cap_mul_prod_gfun_le_topCoeff n (matrixPoly M)
    (matrixPoly_nonnegCoeffs fun i j => nonneg_of_mem_doublyStochastic hM)
    (matrixPoly_isHomogeneous M) (Or.inr (matrixPoly_isHStable hM))
  rwa [cap_matrixPoly hM, one_mul, prod_gfun, topCoeff_matrixPoly] at h

end Gurvits

end TheoremPart

/-! ## Part: Uniqueness -/

section UniquenessPart

/-!
# The equality case

If `M` is doubly stochastic and `per M = n!/nⁿ`, then `mᵢⱼ = 1/n` for all `i, j`.

Following the book:
1. Equality in the chain of inequalities forces `λ_M(j) = n` for every column, so that all
   entries of `M` are positive, and `cap(p_M') = g(n)`.
2. Two applications of the AM-GM inequality give
   `p_M'(y) ≥ ∏ᵢ (1 - mᵢ₀)^(1 - mᵢ₀)` for all `y > 0` with `∏ yⱼ = 1`.
3. Log-convexity of `x ↦ xˣ` gives `∏ᵢ (1 - mᵢ₀)^(1 - mᵢ₀) ≥ ((n-1)/n)^(n-1) = g(n)` with
   equality only if all `mᵢ₀` are equal; hence `mᵢ₀ = 1/n`.
4. By symmetry (permuting the columns) the same holds for every column.

(Here the distinguished column is the first one, `j = 0`, rather than the last.)
-/

open MvPolynomial

namespace Gurvits

/-! ### Real-analytic inequalities -/

theorem log_rpow_self {x : ℝ} (hx : 0 ≤ x) : Real.log (x ^ x) = x * Real.log x := by
  rcases hx.lt_or_eq with h | h
  · rw [Real.log_rpow h]
  · subst h; simp

theorem rpow_self_pos {x : ℝ} (hx : 0 ≤ x) : 0 < x ^ x := by
  rcases hx.lt_or_eq with h | h
  · exact Real.rpow_pos_of_pos h _
  · subst h; simp

/-- Log-convexity of `x ↦ xˣ`: if `x₀, …, x_m ≥ 0` sum to `m` and
`∏ xᵢ^xᵢ ≤ (m/(m+1))^m`, then all `xᵢ` are equal to `m/(m+1)`. -/
theorem eq_of_prod_rpow_self_le (m : ℕ) (x : Fin (m + 1) → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i = m) (h : ∏ i, x i ^ x i ≤ ((m : ℝ) / (m + 1)) ^ m) :
    ∀ i, x i = m / (m + 1) := by
  set μ : ℝ := m / (m + 1) with hμ
  have hm1 : (0:ℝ) < m + 1 := by positivity
  set w : Fin (m + 1) → ℝ := fun _ => 1 / (m + 1) with hw
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), 0 < w i := fun i _ => by positivity
  have hw1 : ∑ i, w i = 1 := by
    simp [hw]; field_simp
  have hmean : ∑ i, w i • x i = μ := by
    simp only [hw, smul_eq_mul, ← Finset.mul_sum, hsum, hμ]; field_simp
  have hconv := Real.strictConvexOn_mul_log
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), x i ∈ Set.Ici (0:ℝ) := fun i _ => hx0 i
  have hjensen := hconv.convexOn.map_sum_le (fun i hi => (hw0 i hi).le) hw1 hmem
  rw [hmean] at hjensen
  have hlog : ∑ i, x i * Real.log (x i) ≤ m * Real.log μ := by
    have hpos : 0 < ∏ i, x i ^ x i := Finset.prod_pos fun i _ => rpow_self_pos (hx0 i)
    have := Real.log_le_log hpos h
    rw [Real.log_prod (fun i _ => (rpow_self_pos (hx0 i)).ne'), Real.log_pow] at this
    simpa [log_rpow_self (hx0 _)] using this
  have hrev : ∑ i, w i • (x i * Real.log (x i)) ≤ μ * Real.log μ := by
    simp only [hw, smul_eq_mul, ← Finset.mul_sum]
    rw [hμ]
    have : 1 / ((m:ℝ) + 1) * ∑ i, x i * Real.log (x i) ≤ 1 / ((m:ℝ) + 1) * (m * Real.log μ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    rw [hμ] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have heq : μ * Real.log μ = ∑ i, w i • (x i * Real.log (x i)) := le_antisymm hjensen hrev
  have := (hconv.map_sum_eq_iff hw0 hw1 hmem).1 (by rw [hmean]; exact heq)
  intro i
  rw [this i (Finset.mem_univ _), hmean]

/-- Weighted AM-GM in the form `(∑ vⱼ)^(∑ vⱼ) ∏ yⱼ^vⱼ ≤ (∑ vⱼ yⱼ)^(∑ vⱼ)`. -/
theorem row_amgm {ι : Type*} (s : Finset ι) (v y : ι → ℝ) (hv : ∀ j ∈ s, 0 ≤ v j)
    (hy : ∀ j ∈ s, 0 < y j) (hS : 0 < ∑ j ∈ s, v j) :
    (∑ j ∈ s, v j) ^ (∑ j ∈ s, v j) * ∏ j ∈ s, y j ^ v j ≤
      (∑ j ∈ s, v j * y j) ^ (∑ j ∈ s, v j) := by
  set S := ∑ j ∈ s, v j with hSdef
  have amgm := Real.geom_mean_le_arith_mean_weighted s (fun j => v j / S) y
    (fun j hj => div_nonneg (hv j hj) hS.le)
    (by rw [← Finset.sum_div, ← hSdef, div_self hS.ne'])
    (fun j hj => (hy j hj).le)
  have h1 : S * ∏ j ∈ s, y j ^ (v j / S) ≤ ∑ j ∈ s, v j * y j := by
    have : ∑ j ∈ s, v j / S * y j = (∑ j ∈ s, v j * y j) / S := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, le_div_iff₀ hS] at amgm
    linarith
  have hP : 0 ≤ ∏ j ∈ s, y j ^ (v j / S) :=
    Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hy j hj).le _
  have h2 := Real.rpow_le_rpow (mul_nonneg hS.le hP) h1 hS.le
  rw [Real.mul_rpow hS.le hP,
    ← Chapter24Aux.prod_rpow s _ (fun j hj => Real.rpow_nonneg (hy j hj).le _)] at h2
  have h3 : ∀ j ∈ s, (y j ^ (v j / S)) ^ S = y j ^ v j := by
    intro j hj
    rw [← Real.rpow_mul (hy j hj).le, div_mul_cancel₀ _ hS.ne']
  rwa [Finset.prod_congr rfl h3] at h2

theorem pos_of_nonneg_of_prod_eq_one {n : ℕ} {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∏ i, x i = 1) (j : Fin n) : 0 < x j := by
  rcases (hx0 j).lt_or_eq with h | h
  · exact h
  · exfalso
    have : ∏ i, x i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
    rw [hx1] at this
    exact one_ne_zero this

/-! ### The polynomial `p_M'` -/

theorem coeff_one_prod_linear {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) :
    (∏ i ∈ s, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (b i))).coeff 1 =
      ∑ k ∈ s, a k * ∏ i ∈ s.erase k, b i := by
  have h : ∀ q : Polynomial ℝ, q.coeff 1 = (Polynomial.derivative q).eval 0 := by
    intro q; rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]; simp
  rw [h, Polynomial.derivative_prod_finset, Chapter24Aux.polynomial_eval_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Polynomial.eval_prod]
  ring

theorem sliceR_matrixPoly {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (y : Fin m → ℝ) :
    sliceR (matrixPoly M) y =
      ∏ i, (Polynomial.C (M i 0) * Polynomial.X + Polynomial.C (∑ j, M i j.succ * y j)) := by
  apply Polynomial.funext
  intro t
  rw [sliceR_eval, eval_matrixPoly, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succ]
  simp [Chapter24Aux.polynomial_eval_sum]

/-- `p_M'(y) = ∑ₖ mₖ₀ ∏_{i ≠ k} (∑ⱼ mᵢⱼ yⱼ)` (Leibniz rule). -/
theorem eval_pDeriv_matrixPoly {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (y : Fin m → ℝ) :
    eval y (pDeriv (matrixPoly M)) =
      ∑ k, M k 0 * ∏ i ∈ Finset.univ.erase k, ∑ j, M i j.succ * y j := by
  rw [← sliceR_coeff_one, sliceR_matrixPoly, coeff_one_prod_linear]

/-- The chain of inequalities `p_M'(y) ≥ ∏ᵢ (1 - mᵢ₀)^(1 - mᵢ₀)` for `y > 0`, `∏ yⱼ = 1`,
when all entries of the doubly stochastic matrix `M` are positive. -/
theorem prod_rpow_le_eval_pDeriv {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (hpos : ∀ i j, 0 < M i j) (hm : 1 ≤ m)
    {y : Fin m → ℝ} (hy : ∀ j, 0 < y j) (hprod : ∏ j, y j = 1) :
    ∏ i, (1 - M i 0) ^ (1 - M i 0) ≤ eval y (pDeriv (matrixPoly M)) := by
  classical
  set L : Fin (m + 1) → ℝ := fun i => ∑ j, M i j.succ * y j with hLdef
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hL : ∀ i, 0 < L i := fun i =>
    Finset.sum_pos (fun j _ => mul_pos (hpos _ _) (hy j)) Finset.univ_nonempty
  have hs : ∀ i, ∑ j : Fin m, M i j.succ = 1 - M i 0 := by
    intro i
    have := sum_row_of_mem_doublyStochastic hM i
    rw [Fin.sum_univ_succ] at this
    linarith
  have hcol : ∑ k, M k 0 = 1 := sum_col_of_mem_doublyStochastic hM 0
  have hsP : ∀ i, 0 < 1 - M i 0 := fun i => by
    rw [← hs i]; exact Finset.sum_pos (fun j _ => hpos _ _) Finset.univ_nonempty
  rw [eval_pDeriv_matrixPoly]
  -- first AM-GM, with weights `mₖ₀`
  have step1 : ∏ k, (∏ i ∈ Finset.univ.erase k, L i) ^ M k 0 ≤
      ∑ k, M k 0 * ∏ i ∈ Finset.univ.erase k, L i :=
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun k _ => (hpos k 0).le) hcol
      (fun k _ => Finset.prod_nonneg fun i _ => (hL i).le)
  -- regrouping the product
  have step2 : ∏ k, (∏ i ∈ Finset.univ.erase k, L i) ^ M k 0 = ∏ i, L i ^ (1 - M i 0) := by
    calc ∏ k, (∏ i ∈ Finset.univ.erase k, L i) ^ M k 0
        = ∏ k, ∏ i ∈ Finset.univ.erase k, L i ^ M k 0 := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [Chapter24Aux.prod_rpow _ _ (fun i _ => (hL i).le)]
      _ = ∏ i, ∏ k ∈ Finset.univ.erase i, L i ^ M k 0 := by
          apply Finset.prod_comm'
          intro k i
          simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true, true_and]
          exact ⟨fun h => fun h' => h h'.symm, fun h => fun h' => h h'.symm⟩
      _ = ∏ i, L i ^ (∑ k ∈ Finset.univ.erase i, M k 0) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Real.rpow_sum_of_pos (hL i)]
      _ = ∏ i, L i ^ (1 - M i 0) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hcol]
  -- second AM-GM, row by row
  have step3 : ∏ i, ((1 - M i 0) ^ (1 - M i 0) * ∏ j, y j ^ M i j.succ) ≤
      ∏ i, L i ^ (1 - M i 0) := by
    refine Chapter24Aux.prod_le_prod (fun i _ => mul_nonneg (rpow_self_pos (hsP i).le).le
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hy j).le _)) fun i _ => ?_
    have := row_amgm Finset.univ (fun j => M i j.succ) y (fun j _ => (hpos _ _).le)
      (fun j _ => hy j) (by rw [hs i]; exact hsP i)
    rwa [hs i] at this
  -- the product of the `y`-factors is `∏ yⱼ = 1`
  have step4 : ∏ i, ((1 - M i 0) ^ (1 - M i 0) * ∏ j, y j ^ M i j.succ) =
      ∏ i, (1 - M i 0) ^ (1 - M i 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    have : ∏ j : Fin m, ∏ i : Fin (m + 1), y j ^ M i j.succ = 1 := by
      calc ∏ j : Fin m, ∏ i : Fin (m + 1), y j ^ M i j.succ
          = ∏ j : Fin m, y j ^ (∑ i, M i j.succ) := by
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [Real.rpow_sum_of_pos (hy j)]
        _ = 1 := by
            simp only [sum_col_of_mem_doublyStochastic hM, Real.rpow_one, hprod]
    rw [this, mul_one]
  rw [← step4]
  exact step3.trans (step2 ▸ step1)

theorem prod_rpow_le_cap_pDeriv {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (hpos : ∀ i j, 0 < M i j) (hm : 1 ≤ m) :
    ∏ i, (1 - M i 0) ^ (1 - M i 0) ≤ cap (pDeriv (matrixPoly M)) :=
  le_cap fun _ hy0 hy1 =>
    prod_rpow_le_eval_pDeriv hM hpos hm (pos_of_nonneg_of_prod_eq_one hy0 hy1) hy1

/-! ### Equality in the chain -/

/-- If `per M = n!/nⁿ` (with `n = m + 1 ≥ 2`), then the first column of `M` has no zero entry
and `cap(p_M') = g(n)`. -/
theorem equality_column_zero {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (hm : 1 ≤ m)
    (heq : M.permanent = ((m + 1).factorial : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (m + 1)) :
    (∀ i, M i 0 ≠ 0) ∧ cap (pDeriv (matrixPoly M)) = gfun (m + 1) := by
  classical
  set p := matrixPoly M with hp
  have hnn : NonnegCoeffs p := matrixPoly_nonnegCoeffs fun i j => nonneg_of_mem_doublyStochastic hM
  have hhom : p.IsHomogeneous (m + 1) := matrixPoly_isHomogeneous M
  have hst : IsHStable p := matrixPoly_isHStable hM
  have hcap : cap p = 1 := cap_matrixPoly hM
  obtain ⟨h1, -, h3⟩ := gurvits_proposition hnn hhom hst
  have chain := cap_mul_prod_gfun_le_topCoeff m (pDeriv p) (pDeriv_nonnegCoeffs hnn)
    (pDeriv_isHomogeneous hhom) h1
  rw [topCoeff_pDeriv, hp, topCoeff_matrixPoly, heq, ← prod_gfun, Finset.prod_range_succ,
    ← hp] at chain
  set P := ∏ i ∈ Finset.range m, gfun (i + 1) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => gfun_pos _
  have hle : cap (pDeriv p) ≤ gfun (m + 1) := by
    have : cap (pDeriv p) * P ≤ gfun (m + 1) * P := by linarith
    exact le_of_mul_le_mul_right this hPpos
  rw [hcap, one_mul] at h3
  have hdeg : p.degreeOf 0 = m + 1 := by
    by_contra hne
    have hlt : p.degreeOf 0 < m + 1 :=
      lt_of_le_of_ne (degreeOf_le_of_isHomogeneous hhom 0) hne
    have := gfun_lt_of_lt (by omega) hlt
    linarith
  refine ⟨?_, le_antisymm hle (hdeg ▸ h3)⟩
  have hcol := degreeOf_matrixPoly_le M 0
  rw [← hp, hdeg] at hcol
  have hcard : (Finset.univ.filter fun i => M i 0 ≠ 0).card =
      (Finset.univ : Finset (Fin (m+1))).card := by
    apply le_antisymm (Finset.card_le_univ _)
    simpa [colNonzero] using hcol
  intro i
  exact (Finset.card_filter_eq_iff.1 hcard) i (Finset.mem_univ i)

/-- Permuting the columns of a doubly stochastic matrix gives a doubly stochastic matrix. -/
theorem submatrix_mem_doublyStochastic {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) (σ : Equiv.Perm (Fin n)) :
    M.submatrix id σ ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum] at hM ⊢
  refine ⟨fun i j => hM.1 _ _, fun i => ?_, fun j => hM.2.2 _⟩
  simp only [Matrix.submatrix_apply, id]
  rw [Equiv.sum_comp σ (fun j => M i j)]
  exact hM.2.1 i

/-- If `per M = n!/nⁿ` (with `n ≥ 2`), all entries of `M` are positive. -/
theorem equality_pos {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (hm : 1 ≤ m)
    (heq : M.permanent = ((m + 1).factorial : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (m + 1)) :
    ∀ i j, 0 < M i j := by
  intro i j
  have hM' := submatrix_mem_doublyStochastic hM (Equiv.swap 0 j)
  have heq' : (M.submatrix id (Equiv.swap 0 j)).permanent =
      ((m + 1).factorial : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
    rw [Matrix.permanent_permute_rows, heq]
  have := (equality_column_zero hM' hm heq').1 i
  simp only [Matrix.submatrix_apply, id, Equiv.swap_apply_left] at this
  exact lt_of_le_of_ne (nonneg_of_mem_doublyStochastic hM) (Ne.symm this)

/-- If `per M = n!/nⁿ` (with `n ≥ 2`), every entry of the first column equals `1/n`. -/
theorem equality_column_zero_eq {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin (m + 1))) (hm : 1 ≤ m)
    (heq : M.permanent = ((m + 1).factorial : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (m + 1)) :
    ∀ i, M i 0 = 1 / (m + 1) := by
  have hpos := equality_pos hM hm heq
  have hcapeq := (equality_column_zero hM hm heq).2
  have hC := prod_rpow_le_cap_pDeriv hM hpos hm
  rw [hcapeq, gfun_of_pos (by omega)] at hC
  have hg : (((m + 1 : ℕ) : ℝ) - 1) / ((m + 1 : ℕ) : ℝ) = (m : ℝ) / (m + 1) := by
    push_cast; ring
  rw [hg, show m + 1 - 1 = m from rfl] at hC
  have hx0 : ∀ i, 0 ≤ 1 - M i 0 := fun i => by
    have := le_one_of_mem_doublyStochastic hM (i := i) (j := 0)
    linarith
  have hsum : ∑ i, (1 - M i 0) = m := by
    rw [Finset.sum_sub_distrib, sum_col_of_mem_doublyStochastic hM 0]
    simp
  have := eq_of_prod_rpow_self_le m (fun i => 1 - M i 0) hx0 hsum hC
  intro i
  have hi := this i
  have : (0:ℝ) < m + 1 := by positivity
  field_simp at hi ⊢
  linarith

/-- **Uniqueness.** If `M` is doubly stochastic and `per M = n!/nⁿ`, then `mᵢⱼ = 1/n` for
all `i, j`. -/
theorem eq_of_permanent_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (heq : M.permanent = (n.factorial : ℝ) / (n : ℝ) ^ n) :
    ∀ i j, M i j = 1 / n := by
  intro i j
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact i.elim0
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      have := sum_row_of_mem_doublyStochastic hM 0
      simpa using this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hM' := submatrix_mem_doublyStochastic hM (Equiv.swap 0 j)
    have heq' : (M.submatrix id (Equiv.swap 0 j)).permanent =
        ((m + 1).factorial : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
      rw [Matrix.permanent_permute_rows, heq]
    have := equality_column_zero_eq hM' (by omega) heq' i
    simp only [Matrix.submatrix_apply, id, Equiv.swap_apply_left] at this
    rw [this]
    push_cast
    ring

/-- The permanent of the matrix with all entries `1/n` is `n!/nⁿ`. -/
theorem permanent_const {n : ℕ} :
    (Matrix.of fun (_ _ : Fin n) => (1 / n : ℝ)).permanent = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  simp [Matrix.permanent, Finset.prod_const, Fintype.card_perm, div_eq_mul_inv]

end Gurvits

end UniquenessPart

/-! ## Part: Farkas -/

section FarkasPart

/-!
# Farkas' Lemma and the Claim

The book quotes the Lemma of Farkas in the following form:

> Let `A ∈ ℝ^{r×s}` and `b ∈ ℝ^r`. Then exactly one of the following alternatives holds:
> (i) `Ax = b, x ∈ ℝ^s, x ≥ 0` is solvable,
> (ii) `Aᵀz > 0, z ∈ ℝ^r, bᵀz < 0` is solvable.

With the *strict* inequality `Aᵀz > 0` in (ii) this statement is not correct in general:
for `A = 0 ∈ ℝ^{1×1}` and `b = 1` neither alternative holds (`book_farkas_false`).
The standard form of Farkas' Lemma has `Aᵀz ≥ 0` in (ii); we prove it (`farkas`) by an
induction argument on the number of columns (in the style of D. Bartl's short algebraic
proof). The strict version is correct as soon as some `z₀` satisfies `Aᵀz₀ > 0`
(`farkas_strict`), and this is the case in the book's application, where the first row of `A`
consists of the positive numbers `Re(yⱼ)`. With it we prove the book's Claim
(`claim_nonneg_combination`): if `aᵢ ≠ 0` then `aᵢ⁻¹` is a nonnegative linear combination of
`y₁, …, y_{n-1}`. (The proof of Gurvits' Proposition in this file uses directly the
consequence `Re(λρ) ≤ 0` of H-stability, which is what the Farkas argument encodes.)
-/

open MvPolynomial Matrix

namespace Gurvits

/-- Farkas' Lemma for linear forms: either `b` is a nonnegative combination of `a₁, …, a_m`,
or there is `x` with `aᵢ(x) ≥ 0` for all `i` and `b(x) < 0`. -/
theorem farkas_forms {V : Type*} [AddCommGroup V] [Module ℝ V] :
    ∀ (m : ℕ) (a : Fin m → V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] ℝ),
      (∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ b = ∑ i, c i • a i) ∨
        (∃ x, (∀ i, 0 ≤ a i x) ∧ b x < 0)
  | 0, a, b => by
    by_cases hb : b = 0
    · left
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [hb]⟩
    · right
      obtain ⟨x, hx⟩ : ∃ x, b x ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (LinearMap.ext h)
      refine ⟨-(b x) • x, fun i => i.elim0, ?_⟩
      simp only [map_smul, smul_eq_mul, neg_mul, neg_lt_zero]
      exact mul_self_pos.2 hx
  | m + 1, a, b => by
    rcases farkas_forms m (fun i => a i.succ) b with ⟨c, hc0, hc⟩ | ⟨x, hx0, hbx⟩
    · left
      refine ⟨Fin.cons 0 c, fun i => Fin.cases le_rfl (fun j => hc0 j) i, ?_⟩
      rw [Fin.sum_univ_succ]
      simp [hc]
    · by_cases ha : 0 ≤ a 0 x
      · right
        exact ⟨x, fun i => Fin.cases ha (fun j => hx0 j) i, hbx⟩
      · push Not at ha
        set t := a 0 x with ht
        rcases farkas_forms m (fun i => a i.succ - (a i.succ x / t) • a 0)
            (b - (b x / t) • a 0) with ⟨c, hc0, hc⟩ | ⟨y, hy0, hby⟩
        · left
          have hsum : 0 ≤ ∑ i, c i * a i.succ x :=
            Finset.sum_nonneg fun i _ => mul_nonneg (hc0 i) (hx0 i)
          refine ⟨Fin.cons ((b x - ∑ i, c i * a i.succ x) / t) c,
            Fin.forall_fin_succ.2 ⟨?_, fun j => hc0 j⟩, ?_⟩
          · simp only [Fin.cons_zero]
            exact div_nonneg_of_nonpos (by linarith) ha.le
          · rw [Fin.sum_univ_succ]
            ext v
            have := congrArg (fun f => f v) hc
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
              LinearMap.coe_sum, Finset.sum_apply] at this
            simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.add_apply, LinearMap.smul_apply,
              smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply]
            have e : ∑ i, c i * (a i.succ v - a i.succ x / t * a 0 v) =
                ∑ i, c i * a i.succ v - (∑ i, c i * a i.succ x) / t * a 0 v := by
              rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [e] at this
            have ht0 : t ≠ 0 := ha.ne
            field_simp
            field_simp at this
            linarith
        · right
          have ht0 : t ≠ 0 := ha.ne
          refine ⟨y - (a 0 y / t) • x, Fin.forall_fin_succ.2 ⟨?_, fun j => ?_⟩, ?_⟩
          · simp only [map_sub, map_smul, smul_eq_mul]
            rw [← ht, div_mul_cancel₀ _ ht0, sub_self]
          · have := hy0 j
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at this
            simp only [map_sub, map_smul, smul_eq_mul]
            have e : a 0 y / t * a j.succ x = a j.succ x / t * a 0 y := by ring
            linarith
          · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hby
            simp only [map_sub, map_smul, smul_eq_mul]
            have e : a 0 y / t * b x = b x / t * a 0 y := by ring
            linarith

/-- **Farkas' Lemma** (standard form). Let `A ∈ ℝ^{r×s}` and `b ∈ ℝ^r`. Then exactly one of
the following holds:
(i) `Ax = b` for some `x ∈ ℝ^s` with `x ≥ 0`;
(ii) `Aᵀz ≥ 0` and `bᵀz < 0` for some `z ∈ ℝ^r`. -/
theorem farkas {r s : ℕ} (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) :
    ((∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ∧
        ¬ (∃ z : Fin r → ℝ, (∀ j, 0 ≤ (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0)) ∨
      ((∃ z : Fin r → ℝ, (∀ j, 0 ≤ (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0) ∧
        ¬ (∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b)) := by
  have hboth : ¬ ((∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ∧
      (∃ z : Fin r → ℝ, (∀ j, 0 ≤ (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0)) := by
    rintro ⟨⟨x, hx0, hx⟩, ⟨z, hz0, hz⟩⟩
    have : b ⬝ᵥ z = x ⬝ᵥ (Aᵀ *ᵥ z) := by
      rw [← hx, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    rw [this] at hz
    have : 0 ≤ x ⬝ᵥ (Aᵀ *ᵥ z) := Finset.sum_nonneg fun j _ => mul_nonneg (hx0 j) (hz0 j)
    linarith
  have hone : (∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ∨
      (∃ z : Fin r → ℝ, (∀ j, 0 ≤ (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0) := by
    let a : Fin s → (Fin r → ℝ) →ₗ[ℝ] ℝ := fun j => (LinearMap.proj j).comp (Matrix.mulVecLin Aᵀ)
    let bf : (Fin r → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun z => b ⬝ᵥ z
        map_add' := fun x y => dotProduct_add b x y
        map_smul' := fun c x => by simp [dotProduct_smul] }
    rcases farkas_forms s a bf with ⟨c, hc0, hc⟩ | ⟨z, hz0, hz⟩
    · left
      refine ⟨c, hc0, ?_⟩
      ext i
      have := congrArg (fun f => f (Pi.single i 1)) hc
      simp only [bf, a, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, Matrix.mulVecLin_apply, smul_eq_mul] at this
      have h1 : b ⬝ᵥ Pi.single i 1 = b i := by simp [dotProduct, Pi.single_apply]
      have h2 : ∀ x, (Aᵀ *ᵥ Pi.single i 1) x = A i x := by
        intro x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1] at this
      simp only [h2] at this
      rw [this]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · right
      exact ⟨z, hz0, hz⟩
  rcases hone with h | h
  · exact Or.inl ⟨h, fun h' => hboth ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hboth ⟨h', h⟩⟩

/-- The Farkas Lemma *as literally stated in the book* (with strict inequality `Aᵀz > 0` in
alternative (ii)) is false: for `A = 0 ∈ ℝ^{1×1}` and `b = 1` neither alternative holds. -/
theorem book_farkas_false :
    ¬ ∀ (r s : ℕ) (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ),
      ((∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ∧
          ¬ (∃ z : Fin r → ℝ, (∀ j, 0 < (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0)) ∨
        ((∃ z : Fin r → ℝ, (∀ j, 0 < (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0) ∧
          ¬ (∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b)) := by
  intro h
  rcases h 1 1 0 (fun _ => 1) with ⟨⟨x, -, hx⟩, -⟩ | ⟨⟨z, hz, -⟩, -⟩
  · have := congrFun hx 0
    simp at this
  · have := hz 0
    simp at this

/-- **Farkas' Lemma, strict version.** If some `z₀` satisfies `Aᵀz₀ > 0`, then exactly one
of the alternatives of the book holds:
(i) `Ax = b` for some `x ≥ 0`;
(ii) `Aᵀz > 0` and `bᵀz < 0` for some `z`. -/
theorem farkas_strict {r s : ℕ} (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ)
    (h₀ : ∃ z₀ : Fin r → ℝ, ∀ j, 0 < (Aᵀ *ᵥ z₀) j) :
    ((∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ∧
        ¬ (∃ z : Fin r → ℝ, (∀ j, 0 < (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0)) ∨
      ((∃ z : Fin r → ℝ, (∀ j, 0 < (Aᵀ *ᵥ z) j) ∧ b ⬝ᵥ z < 0) ∧
        ¬ (∃ x : Fin s → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b)) := by
  obtain ⟨z₀, hz₀⟩ := h₀
  rcases farkas A b with ⟨h1, h2⟩ | ⟨⟨z, hz0, hz⟩, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    rintro ⟨z, hz, hbz⟩
    exact h2 ⟨z, fun j => (hz j).le, hbz⟩
  · refine Or.inr ⟨?_, fun h1 => h2 h1⟩
    set ε : ℝ := -(b ⬝ᵥ z) / (2 * (|b ⬝ᵥ z₀| + 1)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    refine ⟨z + ε • z₀, fun j => ?_, ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hz0 j
      have := mul_pos hεpos (hz₀ j)
      linarith
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 : ε * (b ⬝ᵥ z₀) ≤ ε * |b ⬝ᵥ z₀| := mul_le_mul_of_nonneg_left (le_abs_self _) hεpos.le
      have h2 : ε * |b ⬝ᵥ z₀| < -(b ⬝ᵥ z) / 2 := by
        rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg (b ⬝ᵥ z₀)]
      linarith

/-- **The Claim** in the proof of Gurvits' Proposition. Let `p` be H-stable and homogeneous of
degree `n + 1`, let `y ∈ ℂⁿ₊₊`, and let `a ≠ 0` be such that `1 + a t` divides `p(t, y)`,
i.e. `p(-a⁻¹, y) = 0`. Then `a⁻¹` is a nonnegative linear combination of `y₁, …, yₙ`.
(The hypothesis `a ≠ 0` is not needed in Lean, where `0⁻¹ = 0`.)
The proof is the book's: apply Farkas' Lemma to the `2 × n` matrix with rows `Re(yⱼ)` and
`Im(yⱼ)` and to the vector `(Re(a⁻¹), Im(a⁻¹))`. -/
theorem claim_nonneg_combination {n : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hhom : p.IsHomogeneous (n + 1)) (hst : IsHStable p) {y : Fin n → ℂ}
    (hy : ∀ j, 0 < (y j).re) {a : ℂ} (hroot : aeval (Fin.cons (-a⁻¹) y : Fin (n + 1) → ℂ) p = 0) :
    ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ a⁻¹ = ∑ j, (x j : ℂ) * y j := by
  let A : Matrix (Fin 2) (Fin n) ℝ := Matrix.of ![fun j => (y j).re, fun j => (y j).im]
  let b : Fin 2 → ℝ := ![(a⁻¹).re, (a⁻¹).im]
  have hAT : ∀ (z : Fin 2 → ℝ) j, (Aᵀ *ᵥ z) j = (y j).re * z 0 + (y j).im * z 1 := by
    intro z j
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hAx : ∀ (x : Fin n → ℝ) (i : Fin 2), (A *ᵥ x) i =
      if i = 0 then ∑ j, (y j).re * x j else ∑ j, (y j).im * x j := by
    intro x i
    fin_cases i <;> simp [A, Matrix.mulVec, dotProduct]
  have hroot' : (sliceC p y).eval (-a⁻¹) = 0 := by rw [sliceC_eval]; exact hroot
  rcases farkas_strict A b ⟨![1, 0], fun j => by rw [hAT]; simpa using hy j⟩ with
    ⟨⟨x, hx0, hx⟩, -⟩ | ⟨⟨z, hz, hbz⟩, -⟩
  · refine ⟨x, hx0, Complex.ext ?_ ?_⟩
    · have := congrFun hx 0
      rw [hAx] at this
      simp [b, -Complex.inv_re, -Complex.inv_im] at this
      rw [Complex.re_sum, ← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]
    · have := congrFun hx 1
      rw [hAx] at this
      simp [b, -Complex.inv_re, -Complex.inv_im] at this
      rw [Complex.im_sum, ← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]
  · exfalso
    have hle := root_re_le hhom hst hroot' ((z 0 : ℂ) - (z 1 : ℂ) * Complex.I) (fun j => by
      have := hz j
      rw [hAT] at this
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im]
      nlinarith)
    simp only [b, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hbz
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.neg_re,
      Complex.neg_im] at hle
    nlinarith

end Gurvits

end FarkasPart

/-!
# Van der Waerden's permanent conjecture

Formalization of Chapter 24 of *Proofs from THE BOOK* (Gurvits' proof, following
Laurent–Schrijver). The development is organized into the following parts of this file:

* Part `Defs`: `p_M` (`Gurvits.matrixPoly`), `ℝ₊[x]` (`Gurvits.NonnegCoeffs`),
  H-stability (`Gurvits.IsHStable`), the capacity (`Gurvits.cap`), the function `g`
  (`Gurvits.gfun`), the derivative `p'` (`Gurvits.pDeriv`), the coefficient of `x₁ ⋯ xₙ`
  (`Gurvits.topCoeff`) and `λ_M(j)` (`Gurvits.colNonzero`).
* Part `Basic`: basic facts; `g` is non-increasing (`Gurvits.gfun_antitone`),
  `g(k) → 1/e` (`Gurvits.tendsto_gfun`), `∏_{i=1}^n g(i) = n!/nⁿ` (`Gurvits.prod_gfun`);
  `p'` is homogeneous of degree `n - 1` (`Gurvits.pDeriv_isHomogeneous`).
* Part `MatrixPoly`: Fact A (`Gurvits.topCoeff_matrixPoly`), Fact B
  (`Gurvits.degreeOf_matrixPoly_le`), Claim 1 (`Gurvits.matrixPoly_isHStable`),
  Claim 2 (`Gurvits.cap_matrixPoly`).
* Part `Lemma1`: Lemma 1 (`Gurvits.lemma1`).
* Part `Lemma2`: Lemma 2 (`Gurvits.lemma2`).
* Part `Gurvits`: Gurvits' Proposition (`Gurvits.gurvits_proposition`), with the
  conditions (I) and (II) of its proof.
* Part `Theorem`: the inequality `per M ≥ n!/nⁿ` (`Gurvits.permanent_ge`).
* Part `Uniqueness`: the equality case (`Gurvits.eq_of_permanent_eq`).
* Part `Farkas`: Farkas' Lemma (`Gurvits.farkas`, `Gurvits.farkas_strict`; the
  book's literal statement with strict `Aᵀz > 0` is false in general, `Gurvits.book_farkas_false`)
  and the Claim of the proof of Gurvits' Proposition (`Gurvits.claim_nonneg_combination`).

Convention: the book differentiates with respect to the last variable `xₙ`; we differentiate
with respect to the first variable `x₀` (and correspondingly treat the first column of `M`
first). This is only a relabelling.
-/


open Equiv
namespace Matrix

variable {n : ℕ}

/-- **Theorem (van der Waerden's conjecture), inequality.** Every doubly stochastic `n × n`
matrix `M` satisfies `per M ≥ n!/nⁿ`. -/
theorem permanent_conjecture (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ doublyStochastic ℝ (Fin n) → permanent M ≥ (n.factorial)/(n ^ n) :=
  fun hM => Gurvits.permanent_ge hM

/-- **Theorem (van der Waerden's conjecture), equality case.** For a doubly stochastic
`n × n` matrix `M`, `per M = n!/nⁿ` holds if and only if `mᵢⱼ = 1/n` for all `i` and `j`. -/
theorem permanent_conjecture_eq_iff (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    permanent M = (n.factorial)/(n ^ n) ↔ ∀ i j, M i j = 1 / n := by
  constructor
  · exact Gurvits.eq_of_permanent_eq hM
  · intro h
    have hM' : M = Matrix.of fun (_ _ : Fin n) => (1 / n : ℝ) := by
      ext i j
      exact h i j
    rw [hM']
    exact Gurvits.permanent_const

end Matrix
