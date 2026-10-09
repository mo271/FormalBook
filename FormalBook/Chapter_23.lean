/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.Factorization
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# A theorem of Pólya on polynomials

Formalizes the polynomial sublevel-set bounds, the real-rooted polynomial facts,
Chebyshev's theorem and its equality cases, and the chapter's examples.

-/

/-! ## Contents of former file `Chapter_23/Chebyshev.lean` -/

/-!
# Chebyshev's theorem (Appendix of Chapter 23)

We prove Chebyshev's theorem: a real polynomial of degree `n ≥ 1` with leading
coefficient `c` attains at some point of `[-1, 1]` an absolute value of at least
`|c| / 2 ^ (n - 1)`.

The proof is the one of the book, transported from cosine polynomials to ordinary
polynomials via `x = cos θ`: we compare `p` with the scaled Chebyshev polynomial
`c / 2^(n-1) * T_n`, which alternates in sign at the `n + 1` nodes `cos (kπ/n)`.
-/

public section

open Polynomial Set

namespace Chapter23

/-- Intermediate value theorem in the form of a sign change. -/
lemma exists_root_of_mul_neg {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h : f a * f b < 0) : ∃ c ∈ Ioo a b, f c = 0 := by
  rcases lt_or_gt_of_ne (show f a ≠ 0 by rintro h'; simp [h'] at h) with ha | ha
  · have hb : 0 < f b := by nlinarith
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hab.le hf.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc, hfc⟩
  · have hb : f b < 0 := by nlinarith
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hab.le hf.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc, hfc⟩

/-- The Chebyshev nodes `cos (k π / n)`. -/
noncomputable def chebNode (n k : ℕ) : ℝ := Real.cos (k * Real.pi / n)

lemma chebNode_strictAnti {n j k : ℕ} (hn : 1 ≤ n) (hjk : j < k) (hk : k ≤ n) :
    chebNode n k < chebNode n j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  apply Real.strictAntiOn_cos
  · refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hn']
    have : (j : ℝ) ≤ n := by exact_mod_cast (hjk.le.trans hk)
    nlinarith
  · refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hn']
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  · apply div_lt_div_of_pos_right _ hn'
    have : (j : ℝ) < k := by exact_mod_cast hjk
    nlinarith

lemma chebNode_mem {n k : ℕ} : chebNode n k ∈ Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- The Chebyshev polynomial `T_n` evaluated at the node `cos (kπ/n)` is `(-1)^k`. -/
lemma eval_chebNode {n k : ℕ} (hn : 1 ≤ n) :
    (Chebyshev.T ℝ n).eval (chebNode n k) = (-1) ^ k := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [chebNode, Chebyshev.T_real_cos]
  have : ((n : ℤ) : ℝ) * (k * Real.pi / n) = k * Real.pi := by
    push_cast; field_simp
  rw [this, Real.cos_nat_mul_pi]

/-- **Chebyshev's theorem**, general leading coefficient: if `p` has degree `n ≥ 1`,
then `max_{-1 ≤ x ≤ 1} |p x| ≥ |lc p| / 2^(n-1)`. -/
theorem chebyshev_leadingCoeff (p : ℝ[X]) (n : ℕ) (hn : 1 ≤ n) (hdeg : p.natDegree = n) :
    ∃ x ∈ Icc (-1 : ℝ) 1, |p.leadingCoeff| / 2 ^ (n - 1) ≤ |p.eval x| := by
  set c := p.leadingCoeff with hc
  have hp0 : p ≠ 0 := by rintro rfl; simp at hdeg; omega
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  by_contra hcon
  push Not at hcon
  set Q : ℝ[X] := C (c / 2 ^ (n - 1)) * Chebyshev.T ℝ n with hQ
  have h2 : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  have hQdeg : Q.natDegree = n := by
    rw [hQ, natDegree_C_mul (div_ne_zero hc0 h2), Chebyshev.natDegree_T]; simp
  have hQlc : Q.leadingCoeff = c := by
    rw [hQ, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (div_ne_zero hc0 h2)),
      Chebyshev.leadingCoeff_T]
    simp only [Int.natAbs_natCast]
    field_simp
  have hQ0 : Q ≠ 0 := by rintro h; rw [h] at hQlc; simp at hQlc; exact hc0 hQlc.symm
  set r := Q - p with hr
  have hrdeg : r.natDegree < n := by
    by_cases hr0 : r = 0
    · rw [hr0]; simp; omega
    · have hdeg' : Q.degree = p.degree := by
        rw [degree_eq_natDegree hQ0, degree_eq_natDegree hp0, hQdeg, hdeg]
      have := degree_sub_lt_left hdeg' hQ0 (by rw [hQlc])
      rw [← hr, degree_eq_natDegree hr0, degree_eq_natDegree hQ0, hQdeg] at this
      exact_mod_cast this
  -- sign alternation of `r` at the nodes
  have hsign : ∀ k ≤ n, 0 < c * (-1) ^ k * r.eval (chebNode n k) := by
    intro k _
    have hval : r.eval (chebNode n k) = c / 2 ^ (n - 1) * (-1) ^ k - p.eval (chebNode n k) := by
      rw [hr, eval_sub, hQ, eval_mul, eval_C, eval_chebNode hn]
    rw [hval]
    have hlt := hcon _ (chebNode_mem (n := n) (k := k))
    have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have habs : c * (-1) ^ k * p.eval (chebNode n k) ≤ |c| * |p.eval (chebNode n k)| := by
      have : |c * (-1) ^ k * p.eval (chebNode n k)| = |c| * |p.eval (chebNode n k)| := by
        rw [abs_mul, abs_mul]; simp
      rw [← this]; exact le_abs_self _
    have hcpos : 0 < |c| := abs_pos.mpr hc0
    have : |c| * |p.eval (chebNode n k)| < |c| * (|c| / 2 ^ (n - 1)) :=
      mul_lt_mul_of_pos_left hlt hcpos
    have e : c * (-1) ^ k * (c / 2 ^ (n - 1) * (-1) ^ k - p.eval (chebNode n k))
        = c ^ 2 / 2 ^ (n - 1) * ((-1) ^ k) ^ 2 - c * (-1) ^ k * p.eval (chebNode n k) := by ring
    rw [e, hsq, mul_one]
    have : |c| * (|c| / 2 ^ (n - 1)) = c ^ 2 / 2 ^ (n - 1) := by
      rw [← mul_div_assoc, ← sq, sq_abs]
    linarith
  -- a root between consecutive nodes
  have hroot : ∀ k : Fin n, ∃ y ∈ Ioo (chebNode n (k + 1)) (chebNode n k), r.eval y = 0 := by
    intro k
    apply exists_root_of_mul_neg (f := fun x => r.eval x) r.continuous
      (chebNode_strictAnti hn (Nat.lt_succ_self _) (by omega))
    have h1 := hsign (k + 1) (by omega)
    have h2 := hsign k (by omega)
    have := mul_pos h1 h2
    have e : c * (-1) ^ (k.1 + 1) * r.eval (chebNode n (k + 1)) *
        (c * (-1) ^ k.1 * r.eval (chebNode n k))
        = - (c ^ 2 * (((-1) ^ k.1) ^ 2)) *
          (r.eval (chebNode n (k + 1)) * r.eval (chebNode n k)) := by
      ring
    have hsq : ((-1 : ℝ) ^ k.1) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [e, hsq, mul_one] at this
    have hc2 : 0 < c ^ 2 := by positivity
    nlinarith
  choose y hy hyr using hroot
  have hinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have h1 := (hy j).2
      have h2 := (hy i).1
      have h3 : chebNode n j ≤ chebNode n (i + 1) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · rw [← h']
        · exact (chebNode_strictAnti hn h' (by omega)).le
      rw [hij] at h2; linarith
    · have h1 := (hy i).2
      have h2 := (hy j).1
      have h3 : chebNode n i ≤ chebNode n (j + 1) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · rw [← h']
        · exact (chebNode_strictAnti hn h' (by omega)).le
      rw [← hij] at h2; linarith
  have hr0 : r = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero r hinj hyr (by simpa using hrdeg)
  have hpQ : p = Q := (sub_eq_zero.mp hr0).symm
  have := hcon _ (chebNode_mem (n := n) (k := 0))
  rw [hpQ, hQ, eval_mul, eval_C, eval_chebNode hn, pow_zero, mul_one, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n - 1))] at this
  exact lt_irrefl _ this

/-- **Chebyshev's theorem.** Let `p` be a real polynomial of degree `n ≥ 1` with leading
coefficient `1`. Then `max_{-1 ≤ x ≤ 1} |p x| ≥ 1 / 2^(n-1)`. -/
theorem chebyshev (p : ℝ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree) :
    ∃ x ∈ Icc (-1 : ℝ) 1, 1 / 2 ^ (p.natDegree - 1) ≤ |p.eval x| := by
  simpa [hp.leadingCoeff] using chebyshev_leadingCoeff p p.natDegree hn rfl

/-- **Corollary.** Let `p` be a real polynomial of degree `n ≥ 1` with leading coefficient `1`,
and suppose `|p x| ≤ 2` for all `x ∈ [a, b]`. Then `b - a ≤ 4`. -/
theorem corollary (p : ℝ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree) (a b : ℝ)
    (h : ∀ x ∈ Icc a b, |p.eval x| ≤ 2) : b - a ≤ 4 := by
  by_contra hcon
  push Not at hcon
  set n := p.natDegree
  set k := (b - a) / 2 with hk
  have hk2 : 2 < k := by rw [hk]; linarith
  have hk0 : 0 < k := by linarith
  set g : ℝ[X] := C k * X + C (k + a) with hg
  have hgdeg : g.natDegree = 1 := by rw [hg]; exact natDegree_linear hk0.ne'
  have hglc : g.leadingCoeff = k := by rw [hg]; exact leadingCoeff_linear hk0.ne'
  set q := p.comp g with hq
  have hqdeg : q.natDegree = n := by rw [hq, natDegree_comp, hgdeg, mul_one]
  have hqlc : q.leadingCoeff = k ^ n := by
    rw [hq, leadingCoeff_comp (by rw [hgdeg]; exact one_ne_zero), hglc, hp.leadingCoeff, one_mul]
  obtain ⟨y, hy, hle⟩ := chebyshev_leadingCoeff q n hn hqdeg
  rw [hqlc, hq, eval_comp, abs_of_pos (by positivity)] at hle
  have hx : g.eval y ∈ Icc a b := by
    rw [hg]; simp only [eval_add, eval_mul, eval_C, eval_X]
    obtain ⟨h1, h2⟩ := hy
    constructor <;> nlinarith
  have h2 := h _ hx
  have hpow : (2 : ℝ) ^ n < k ^ n := pow_lt_pow_left₀ hk2 (by norm_num) (by omega)
  have : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  rw [div_le_iff₀ hpos] at hle
  nlinarith

end Chapter23

end

/-! ## Contents of former file `Chapter_23/Facts.lean` -/

/-!
# Two facts about polynomials with real roots (box in Chapter 23)

Let `p` be a real polynomial all of whose roots are real (i.e. the number of roots counted
with multiplicity equals the degree).

* **Fact 1.** If `b` is a multiple root of `p'`, then `b` is also a root of `p`.
* **Fact 2.** `p'(x)² ≥ p(x) p''(x)` for all `x ∈ ℝ`.
-/

public section

open Polynomial Finset

namespace Chapter23

/-- Fact 2 for a product `∏ (X - a)`, by induction on the roots. -/
lemma fact_2_prod (s : Multiset ℝ) (x : ℝ) :
    ((s.map fun a => X - C a).prod).eval x *
        (derivative (derivative (s.map fun a => X - C a).prod)).eval x ≤
      ((derivative (s.map fun a => X - C a).prod).eval x) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    generalize (s.map fun a => X - C a).prod = q at ih ⊢
    have h1 : derivative ((X - C a) * q) = q + (X - C a) * derivative q := by
      simp [derivative_mul]
    have h2 : derivative (derivative ((X - C a) * q)) =
        2 * derivative q + (X - C a) * derivative (derivative q) := by
      rw [h1]; simp [derivative_mul]; ring
    rw [h2, h1]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_ofNat]
    nlinarith [mul_nonneg (sq_nonneg (x - a)) (sub_nonneg.mpr ih), sq_nonneg (eval x q)]

/-- **Fact 2.** If all roots of the real polynomial `p` are real, then
`p'(x)² ≥ p(x) p''(x)` for all real `x`. -/
theorem fact_2 (p : ℝ[X]) (hroots : Multiset.card p.roots = p.natDegree) (x : ℝ) :
    p.eval x * (derivative (derivative p)).eval x ≤ ((derivative p).eval x) ^ 2 := by
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  simp only [derivative_C_mul, eval_mul, eval_C]
  have := fact_2_prod p.roots x
  nlinarith [sq_nonneg p.leadingCoeff]

/-- **Fact 1.** If all roots of the real polynomial `p` are real and `b` is a multiple root of
`p'` (i.e. `(X - b)²` divides `p'`, with `p' ≠ 0`), then `b` is a root of `p`. -/
theorem fact_1 (p : ℝ[X]) (hroots : Multiset.card p.roots = p.natDegree) (b : ℝ)
    (hb : 2 ≤ rootMultiplicity b (derivative p)) : p.IsRoot b := by
  classical
  by_contra hpb
  set D := (derivative p).roots with hD
  set S := p.roots.toFinset with hS
  set N := D.toFinset \ S with hN
  set n := p.natDegree with hn
  have hd0 : derivative p ≠ 0 := by
    rintro h; rw [h, rootMultiplicity_zero] at hb; omega
  have hn0 : n ≠ 0 := by
    intro h
    apply hd0
    rw [eq_C_of_natDegree_eq_zero h, derivative_C]
  -- upper bound on the number of roots of `p'`
  have hcardD : Multiset.card D < n :=
    lt_of_le_of_lt (card_roots' _) (natDegree_derivative_lt hn0)
  -- Rolle: one new root of `p'` between consecutive roots of `p`
  have hrolle : S.card ≤ N.card + 1 :=
    card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ p
  -- splitting the count of roots of `p'`
  have hsplit : Multiset.card D = ∑ a ∈ S, D.count a + ∑ a ∈ N, D.count a := by
    rw [← sum_union (disjoint_sdiff), union_sdiff_self_eq_union]
    symm
    apply Multiset.sum_count_eq_card
    intro a ha
    exact mem_union_right _ (Multiset.mem_toFinset.mpr ha)
  -- roots of `p` of multiplicity `s` are roots of `p'` of multiplicity `≥ s - 1`
  have hS' : n ≤ ∑ a ∈ S, D.count a + S.card := by
    have h1 : ∑ a ∈ S, p.roots.count a = n := by
      rw [hS, Multiset.toFinset_sum_count_eq, hroots]
    have h2 : ∀ a ∈ S, p.roots.count a ≤ D.count a + 1 := by
      intro a _
      rw [count_roots, hD, count_roots]
      have := rootMultiplicity_sub_one_le_derivative_rootMultiplicity p a
      omega
    calc n = ∑ a ∈ S, p.roots.count a := h1.symm
      _ ≤ ∑ a ∈ S, (D.count a + 1) := sum_le_sum h2
      _ = ∑ a ∈ S, D.count a + S.card := by rw [sum_add_distrib, card_eq_sum_ones]
  -- the new roots, one of which (namely `b`) is a multiple root
  have hbN : b ∈ N := by
    rw [hN, mem_sdiff, Multiset.mem_toFinset, Multiset.mem_toFinset, hD,
      mem_roots hd0, mem_roots']
    refine ⟨?_, fun h => hpb h.2⟩
    rw [← rootMultiplicity_pos hd0]; omega
  have hN' : N.card + 1 ≤ ∑ a ∈ N, D.count a := by
    rw [← add_sum_erase N _ hbN]
    have h1 : 2 ≤ D.count b := by rw [hD, count_roots]; exact hb
    have h2 : (N.erase b).card ≤ ∑ a ∈ N.erase b, D.count a := by
      rw [card_eq_sum_ones]
      apply sum_le_sum
      intro a ha
      have : a ∈ D := Multiset.mem_toFinset.mp (mem_sdiff.mp (mem_of_mem_erase ha)).1
      exact Multiset.count_pos.mpr this
    have h3 := card_erase_of_mem hbN
    have h4 : 1 ≤ N.card := card_pos.mpr ⟨b, hbN⟩
    omega
  omega

end Chapter23

end

/-! ## Contents of former file `Chapter_23/RootProd.lean` -/

/-!
# Products `∏ (x - a)` over a multiset of real roots

For a multiset `s` of real numbers we study `rootProd s x = ∏_{a ∈ s} (x - a)`, i.e. the
evaluation of the monic real-rooted polynomial with root multiset `s`.  We collect:

* elementary algebraic facts and comparison lemmas for `|rootProd s x|`;
* log-concavity between consecutive roots, which yields the "quasi-concavity" statement
  `two_lt_abs_rootProd_of_between`: between two consecutive roots, the set where
  `|rootProd s x| > 2` is an interval;
* the structure of a "gap" of the set `{x | |rootProd s x| ≤ 2}` between consecutive roots;
* finite interval covers (`Coverable`) and the cut-and-shift lemma used in Pólya's argument.
-/

public section

open Polynomial Set

namespace Chapter23

/-- `rootProd s x = ∏_{a ∈ s} (x - a)`. -/
@[expose] noncomputable def rootProd (s : Multiset ℝ) (x : ℝ) : ℝ := (s.map (fun a => x - a)).prod

@[simp] lemma rootProd_zero (x : ℝ) : rootProd 0 x = 1 := by simp [rootProd]

@[simp] lemma rootProd_cons (a : ℝ) (s : Multiset ℝ) (x : ℝ) :
    rootProd (a ::ₘ s) x = (x - a) * rootProd s x := by simp [rootProd]

lemma rootProd_add (s t : Multiset ℝ) (x : ℝ) :
    rootProd (s + t) x = rootProd s x * rootProd t x := by
  simp [rootProd, Multiset.map_add, Multiset.prod_add]

lemma rootProd_map_sub (s : Multiset ℝ) (d x : ℝ) :
    rootProd (s.map (· - d)) x = rootProd s (x + d) := by
  simp only [rootProd, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp only [Function.comp]
  ring

lemma eval_prod_X_sub_C (s : Multiset ℝ) (x : ℝ) :
    ((s.map (fun a => X - C a)).prod).eval x = rootProd s x := by
  simp [rootProd, eval_multiset_prod, Multiset.map_map]

lemma continuous_rootProd (s : Multiset ℝ) : Continuous (rootProd s) := by
  have : rootProd s = fun x => ((s.map (fun a => X - C a)).prod).eval x :=
    funext fun x => (eval_prod_X_sub_C s x).symm
  rw [this]
  exact Polynomial.continuous _

lemma rootProd_eq_zero_of_mem {s : Multiset ℝ} {a : ℝ} (h : a ∈ s) : rootProd s a = 0 := by
  rw [rootProd, Multiset.prod_eq_zero_iff]
  exact Multiset.mem_map.mpr ⟨a, h, sub_self a⟩

lemma rootProd_ne_zero {s : Multiset ℝ} {x : ℝ} (h : x ∉ s) : rootProd s x ≠ 0 := by
  rw [rootProd, Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨a, ha, hxa⟩
  rw [sub_eq_zero] at hxa
  exact h (hxa ▸ ha)

/-- Comparison of absolute values of `rootProd` factor by factor. -/
lemma abs_rootProd_le {s : Multiset ℝ} {x y : ℝ} (h : ∀ a ∈ s, |y - a| ≤ |x - a|) :
    |rootProd s y| ≤ |rootProd s x| := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [rootProd_cons, abs_mul]
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (abs_nonneg _) (abs_nonneg _)

/-- The monic polynomial with root multiset `s`. -/
lemma monic_prod_X_sub_C (s : Multiset ℝ) : ((s.map (fun a => X - C a)).prod).Monic :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

/-! ### Log-concavity between consecutive roots -/

/-- `∑_{a ∈ s} log (x - a)`; equal to `log |rootProd s x|` away from the roots. -/
noncomputable def logRootSum (s : Multiset ℝ) (x : ℝ) : ℝ :=
  (s.map (fun a => Real.log (x - a))).sum

lemma log_abs_rootProd {s : Multiset ℝ} {x : ℝ} (h : x ∉ s) :
    Real.log |rootProd s x| = logRootSum s x := by
  induction s using Multiset.induction_on with
  | empty => simp [logRootSum]
  | cons a s ih =>
    have hxa : x - a ≠ 0 := by
      intro h'; rw [sub_eq_zero] at h'; exact h (h' ▸ Multiset.mem_cons_self a s)
    have hs : x ∉ s := fun h' => h (Multiset.mem_cons_of_mem h')
    rw [rootProd_cons, abs_mul, Real.log_mul (abs_ne_zero.mpr hxa)
      (abs_ne_zero.mpr (rootProd_ne_zero hs)), ih hs, Real.log_abs]
    simp [logRootSum]

lemma concaveOn_log_sub {a α β : ℝ} (h : a ≤ α ∨ β ≤ a) :
    ConcaveOn ℝ (Ioo α β) (fun x => Real.log (x - a)) := by
  rcases h with h | h
  · have := (strictConcaveOn_log_Ioi.concaveOn).translate_right (-a)
    refine (this.subset ?_ (convex_Ioo α β)).congr ?_
    · intro x hx
      simp only [mem_preimage, mem_Ioi]
      linarith [hx.1]
    · intro x _
      simp [neg_add_eq_sub]
  · have := (strictConcaveOn_log_Iio.concaveOn).translate_right (-a)
    refine (this.subset ?_ (convex_Ioo α β)).congr ?_
    · intro x hx
      simp only [mem_preimage, mem_Iio]
      linarith [hx.2]
    · intro x _
      simp [neg_add_eq_sub]

lemma concaveOn_logRootSum {s : Multiset ℝ} {α β : ℝ} (h : ∀ a ∈ s, a ≤ α ∨ β ≤ a) :
    ConcaveOn ℝ (Ioo α β) (logRootSum s) := by
  induction s using Multiset.induction_on with
  | empty =>
    have : logRootSum 0 = fun _ => (0 : ℝ) := by funext x; simp [logRootSum]
    rw [this]
    exact concaveOn_const 0 (convex_Ioo α β)
  | cons a s ih =>
    have : logRootSum (a ::ₘ s) = fun x => Real.log (x - a) + logRootSum s x := by
      funext x; simp [logRootSum]
    rw [this]
    exact (concaveOn_log_sub (h a (Multiset.mem_cons_self a s))).add
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/-- Quasi-concavity of `|rootProd s|` between consecutive roots: if `|rootProd s| > 2` at
`x` and `z`, then also at every `y` between them. -/
lemma two_lt_abs_rootProd_of_between {s : Multiset ℝ} {α β : ℝ}
    (hroots : ∀ a ∈ s, a ≤ α ∨ β ≤ a) {x y z : ℝ} (hx : α < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z < β) (hfx : 2 < |rootProd s x|) (hfz : 2 < |rootProd s z|) :
    2 < |rootProd s y| := by
  have hnot : ∀ t, α < t → t < β → t ∉ s := by
    intro t h1 h2 ht
    rcases hroots t ht with h | h <;> linarith
  have hGx : Real.log 2 < logRootSum s x := by
    rw [← log_abs_rootProd (hnot x hx (by linarith))]
    exact Real.log_lt_log (by norm_num) hfx
  have hGz : Real.log 2 < logRootSum s z := by
    rw [← log_abs_rootProd (hnot z (by linarith) hz)]
    exact Real.log_lt_log (by norm_num) hfz
  have hGy := (concaveOn_logRootSum hroots).ge_on_segment
    (⟨hx, by linarith⟩ : x ∈ Ioo α β) (⟨by linarith, hz⟩ : z ∈ Ioo α β)
    (by rw [segment_eq_Icc (hxy.trans hyz)]; exact ⟨hxy, hyz⟩)
  have hy : y ∉ s := hnot y (by linarith) (by linarith)
  rw [← log_abs_rootProd hy] at hGy
  by_contra hcon
  push Not at hcon
  have := Real.log_le_log (abs_pos.mpr (rootProd_ne_zero hy)) hcon
  have := lt_min hGx hGz
  linarith

/-- Structure of a gap of `{x | |rootProd s x| ≤ 2}` between two consecutive roots
`α < β`: the set where `|rootProd s x| > 2` inside `(α, β)` is an open interval `(u, v)`. -/
lemma gap_structure {s : Multiset ℝ} {α β c : ℝ} (hroots : ∀ a ∈ s, a ≤ α ∨ β ≤ a)
    (hα : |rootProd s α| ≤ 2) (hβ : |rootProd s β| ≤ 2) (hc : c ∈ Ioo α β)
    (hfc : 2 < |rootProd s c|) :
    ∃ u v, α ≤ u ∧ u ≤ v ∧ v ≤ β ∧ (∀ x ∈ Icc α u, |rootProd s x| ≤ 2) ∧
      (∀ x ∈ Icc v β, |rootProd s x| ≤ 2) ∧ (∀ x ∈ Ioo u v, 2 < |rootProd s x|) := by
  have hcont : Continuous fun x => |rootProd s x| := (continuous_rootProd s).abs
  set A := Icc α c ∩ {x | |rootProd s x| ≤ 2} with hA
  set B := Icc c β ∩ {x | |rootProd s x| ≤ 2} with hB
  have hAc : IsClosed A := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hBc : IsClosed B := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hAne : A.Nonempty := ⟨α, ⟨le_refl _, hc.1.le⟩, hα⟩
  have hBne : B.Nonempty := ⟨β, ⟨hc.2.le, le_refl _⟩, hβ⟩
  have hAbdd : BddAbove A := ⟨c, fun x hx => hx.1.2⟩
  have hBbdd : BddBelow B := ⟨c, fun x hx => hx.1.1⟩
  set u := sSup A
  set v := sInf B
  have hu : u ∈ A := hAc.csSup_mem hAne hAbdd
  have hv : v ∈ B := hBc.csInf_mem hBne hBbdd
  have hαu : α ≤ u := le_csSup hAbdd ⟨⟨le_refl _, hc.1.le⟩, hα⟩
  have hvβ : v ≤ β := csInf_le hBbdd ⟨⟨hc.2.le, le_refl _⟩, hβ⟩
  have hu2 : |rootProd s u| ≤ 2 := hu.2
  have hv2 : |rootProd s v| ≤ 2 := hv.2
  have huc : u < c := lt_of_le_of_ne hu.1.2 (by rintro h; rw [h] at hu2; linarith)
  have hcv : c < v := lt_of_le_of_ne hv.1.1 (by rintro h; rw [← h] at hv2; linarith)
  refine ⟨u, v, hαu, by linarith, hvβ, ?_, ?_, ?_⟩
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hα
    · by_contra hcon
      push Not at hcon
      have := two_lt_abs_rootProd_of_between hroots h hx.2 huc.le hc.2 hcon hfc
      linarith
  · intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; exact hβ
    · by_contra hcon
      push Not at hcon
      have := two_lt_abs_rootProd_of_between hroots hc.1 hcv.le hx.1 h hfc hcon
      linarith
  · intro x hx
    by_contra hcon
    push Not at hcon
    rcases le_total x c with h | h
    · have : x ≤ u := le_csSup hAbdd ⟨⟨by linarith [hx.1], h⟩, hcon⟩
      linarith [hx.1]
    · have : v ≤ x := csInf_le hBbdd ⟨⟨h, by linarith [hx.2]⟩, hcon⟩
      linarith [hx.2]

/-- `{x | |rootProd s x| ≤ 2}` is bounded when `s` is nonempty. -/
lemma abs_le_of_abs_rootProd_le {s : Multiset ℝ} (hs : s ≠ 0) :
    ∃ M, ∀ x, |rootProd s x| ≤ 2 → |x| ≤ M := by
  have key : ∀ (t : Multiset ℝ) (x : ℝ), t ≠ 0 → (∀ a ∈ t, 2 < |x - a|) →
      2 < |rootProd t x| := by
    intro t x
    induction t using Multiset.induction_on with
    | empty => intro h; exact absurd rfl h
    | cons a t ih =>
      intro _ h
      rw [rootProd_cons, abs_mul]
      have ha := h a (Multiset.mem_cons_self a t)
      by_cases ht : t = 0
      · subst ht; simpa using ha
      · have := ih ht fun b hb => h b (Multiset.mem_cons_of_mem hb)
        nlinarith
  refine ⟨(s.map abs).sum + 2, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have : ∀ a ∈ s, 2 < |x - a| := by
    intro a ha
    have h1 : |a| ≤ (s.map abs).sum :=
      Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ ha)
    have h2 : |x| - |a| ≤ |x - a| := abs_sub_abs_le_abs_sub x a
    linarith
  linarith [key s x hs this]

/-! ### Finite interval covers -/

/-- `S` can be covered by finitely many closed intervals `[a_i, b_i]` of total length at
most `L`. -/
@[expose] def Coverable (S : Set ℝ) (L : ℝ) : Prop :=
  ∃ I : List (ℝ × ℝ), (∀ i ∈ I, i.1 ≤ i.2) ∧ S ⊆ ⋃ i ∈ I, Icc i.1 i.2 ∧
    (I.map fun i => i.2 - i.1).sum ≤ L

lemma Coverable.mono {S T : Set ℝ} {L : ℝ} (h : Coverable T L) (hST : S ⊆ T) :
    Coverable S L := by
  obtain ⟨I, h1, h2, h3⟩ := h
  exact ⟨I, h1, hST.trans h2, h3⟩

/-- The cut-and-shift lemma: if every point of `S` either lies in `T ∩ (-∞, u]`, or
is mapped by `x ↦ x - d` into `T ∩ [u, ∞)`, then a cover of `T` yields a cover of `S`
of no larger total length. -/
lemma Coverable.cut_shift {S T : Set ℝ} {L u d : ℝ} (hT : Coverable T L)
    (h : ∀ x ∈ S, (x ≤ u ∧ x ∈ T) ∨ (u ≤ x - d ∧ x - d ∈ T)) : Coverable S L := by
  obtain ⟨I, hI, hTI, hsum⟩ := hT
  have aux : ∀ I : List (ℝ × ℝ), (∀ i ∈ I, i.1 ≤ i.2) → ∃ J : List (ℝ × ℝ),
      (∀ j ∈ J, j.1 ≤ j.2) ∧
      (∀ x, ((x ≤ u ∧ ∃ i ∈ I, x ∈ Icc i.1 i.2) ∨ (u ≤ x - d ∧ ∃ i ∈ I, x - d ∈ Icc i.1 i.2))
        → ∃ j ∈ J, x ∈ Icc j.1 j.2) ∧
      (J.map fun i => i.2 - i.1).sum ≤ (I.map fun i => i.2 - i.1).sum := by
    intro I
    induction I with
    | nil =>
      intro _
      refine ⟨[], by simp, ?_, by simp⟩
      intro x hx; simp at hx
    | cons i I ih =>
      intro hI
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := ih fun j hj => hI j (List.mem_cons_of_mem _ hj)
      have hi := hI i List.mem_cons_self
      obtain ⟨a, b⟩ := i
      simp only at hi
      rcases lt_or_ge u a with hua | hau
      · -- interval entirely to the right of `u`: shift it
        refine ⟨(a + d, b + d) :: J, ?_, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · simp; linarith
          · exact hJ1 j hj
        · intro x hx
          rcases hx with ⟨hxu, j, hj, hxj⟩ | ⟨hxu, j, hj, hxj⟩
          · rcases List.mem_cons.mp hj with rfl | hj
            · simp at hxj; linarith [hxj.1]
            · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inl ⟨hxu, j, hj, hxj⟩)
              exact ⟨k, List.mem_cons_of_mem _ hk, hxk⟩
          · rcases List.mem_cons.mp hj with rfl | hj
            · refine ⟨(a + d, b + d), List.mem_cons_self, ?_⟩
              simp at hxj ⊢; constructor <;> linarith [hxj.1, hxj.2]
            · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inr ⟨hxu, j, hj, hxj⟩)
              exact ⟨k, List.mem_cons_of_mem _ hk, hxk⟩
        · simp only [List.map_cons, List.sum_cons]; linarith
      · rcases lt_or_ge b u with hbu | hub
        · -- interval entirely to the left of `u`: keep it
          refine ⟨(a, b) :: J, ?_, ?_, ?_⟩
          · intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact hi
            · exact hJ1 j hj
          · intro x hx
            rcases hx with ⟨hxu, j, hj, hxj⟩ | ⟨hxu, j, hj, hxj⟩
            · rcases List.mem_cons.mp hj with rfl | hj
              · exact ⟨(a, b), List.mem_cons_self, hxj⟩
              · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inl ⟨hxu, j, hj, hxj⟩)
                exact ⟨k, List.mem_cons_of_mem _ hk, hxk⟩
            · rcases List.mem_cons.mp hj with rfl | hj
              · simp at hxj; linarith [hxj.2]
              · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inr ⟨hxu, j, hj, hxj⟩)
                exact ⟨k, List.mem_cons_of_mem _ hk, hxk⟩
          · simp only [List.map_cons, List.sum_cons]; linarith
        · -- interval straddles `u`: cut it at `u` and shift the right part
          refine ⟨(a, u) :: (u + d, b + d) :: J, ?_, ?_, ?_⟩
          · intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact hau
            rcases List.mem_cons.mp hj with rfl | hj
            · simp; exact hub
            · exact hJ1 j hj
          · intro x hx
            rcases hx with ⟨hxu, j, hj, hxj⟩ | ⟨hxu, j, hj, hxj⟩
            · rcases List.mem_cons.mp hj with rfl | hj
              · exact ⟨(a, u), List.mem_cons_self, hxj.1, hxu⟩
              · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inl ⟨hxu, j, hj, hxj⟩)
                exact ⟨k, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk), hxk⟩
            · rcases List.mem_cons.mp hj with rfl | hj
              · refine ⟨(u + d, b + d), List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                simp at hxj ⊢; constructor <;> linarith [hxj.1, hxj.2]
              · obtain ⟨k, hk, hxk⟩ := hJ2 x (Or.inr ⟨hxu, j, hj, hxj⟩)
                exact ⟨k, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk), hxk⟩
          · simp only [List.map_cons, List.sum_cons]; linarith
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := aux I hI
  refine ⟨J, hJ1, ?_, hJ3.trans hsum⟩
  intro x hx
  have hmem : ∀ y ∈ T, ∃ i ∈ I, y ∈ Icc i.1 i.2 := by
    intro y hy
    have := hTI hy
    simp only [mem_iUnion] at this
    obtain ⟨i, hi, hyi⟩ := this
    exact ⟨i, hi, hyi⟩
  obtain ⟨j, hj, hxj⟩ : ∃ j ∈ J, x ∈ Icc j.1 j.2 := by
    rcases h x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hJ2 x (Or.inl ⟨h1, hmem x h2⟩)
    · exact hJ2 x (Or.inr ⟨h1, hmem _ h2⟩)
  simp only [mem_iUnion]
  exact ⟨j, hj, hxj⟩

end Chapter23

end

/-! ## Contents of former file `Chapter_23/Polya.lean` -/

/-!
# Pólya's theorem (Theorems 1 and 2 of Chapter 23)

We prove

* **Theorem 2**: if `p` is a monic real polynomial of degree `n ≥ 1` all of whose roots are
  real, then `P = {x | |p x| ≤ 2}` can be covered by finitely many intervals of total
  length at most `4`;
* **Theorem 1**: if `f` is a monic complex polynomial of degree `n ≥ 1`, then the orthogonal
  projection onto the real axis of `C = {z | |f z| ≤ 2}` can be covered by finitely many
  intervals of total length at most `4`.

The proof of Theorem 2 follows Pólya's idea: as long as `P` is not an interval, we take
the gap of `P` between the rightmost "bad" root `α` and the next root `β` and shift all roots
to the right of the gap to the left by the length `d` of the gap. The new set `P₁` contains
`P ∩ (-∞, u]` and `(P ∩ [v, ∞)) - d`, so covers transfer back (`Coverable.cut_shift`),
and the number of "bad" roots strictly decreases. When no bad root remains, `P` is a single
interval on which `|p| ≤ 2`, and the Corollary of Chebyshev's theorem bounds its length by `4`.
-/

public section

open Polynomial Set

namespace Chapter23

/-- The sublevel set `{x | |∏_{a ∈ s} (x - a)| ≤ 2}`. -/
@[expose] def sublevel (s : Multiset ℝ) : Set ℝ := {x | |rootProd s x| ≤ 2}

/-- A root `a` is *good* if `|p| ≤ 2` on the whole segment from `a` to the largest root. -/
@[expose] def Good (s : Multiset ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ x → (∃ b ∈ s, x ≤ b) → |rootProd s x| ≤ 2

open Classical in
/-- The number of distinct roots which are not good. -/
noncomputable def badCount (s : Multiset ℝ) : ℕ := (s.toFinset.filter fun a => ¬ Good s a).card

open Classical

/-- If every root is good, then `P` is a single interval of length at most `4`. -/
lemma coverable_of_all_good {s : Multiset ℝ} (hs : s ≠ 0) (hgood : ∀ a ∈ s, Good s a) :
    Coverable (sublevel s) 4 := by
  set P := sublevel s with hP
  have hcont := continuous_rootProd s
  have hPc : IsClosed P := isClosed_le hcont.abs continuous_const
  obtain ⟨a0, ha0⟩ := Multiset.exists_mem_of_ne_zero hs
  have hPne : P.Nonempty := ⟨a0, by simp [P, sublevel, rootProd_eq_zero_of_mem ha0]⟩
  obtain ⟨M, hM⟩ := abs_le_of_abs_rootProd_le hs
  have hbddA : BddAbove P := ⟨M, fun x hx => (abs_le.mp (hM x hx)).2⟩
  have hbddB : BddBelow P := ⟨-M, fun x hx => (abs_le.mp (hM x hx)).1⟩
  set lo := sInf P
  set hi := sSup P
  have hlo : |rootProd s lo| ≤ 2 := hPc.csInf_mem hPne hbddB
  have hhi : |rootProd s hi| ≤ 2 := hPc.csSup_mem hPne hbddA
  have hlohi : lo ≤ hi := csInf_le_csSup hPne hbddB hbddA
  have hIcc : ∀ z ∈ Icc lo hi, |rootProd s z| ≤ 2 := by
    intro z hz
    by_cases h1 : ∃ a ∈ s, a ≤ z
    · by_cases h2 : ∃ b ∈ s, z ≤ b
      · obtain ⟨a, ha, haz⟩ := h1
        exact hgood a ha z haz h2
      · push Not at h2
        refine le_trans (abs_rootProd_le fun b hb => ?_) hhi
        have := h2 b hb
        rw [abs_of_pos (sub_pos.mpr this), abs_of_pos (by linarith [hz.2])]
        linarith [hz.2]
    · push Not at h1
      refine le_trans (abs_rootProd_le fun b hb => ?_) hlo
      have := h1 b hb
      rw [abs_of_neg (sub_neg.mpr this), abs_of_neg (by linarith [hz.1])]
      linarith [hz.1]
  have hlen : hi - lo ≤ 4 := by
    apply corollary ((s.map fun a => X - C a).prod) (monic_prod_X_sub_C s) _ lo hi
    · intro x hx
      rw [eval_prod_X_sub_C]
      exact hIcc x hx
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]
      exact Multiset.card_pos.mpr hs
  refine ⟨[(lo, hi)], by simpa using hlohi, ?_, by simpa using hlen⟩
  intro x hx
  simp only [List.mem_singleton, mem_iUnion, exists_prop, exists_eq_left, mem_Icc]
  exact ⟨csInf_le hbddB hx, le_csSup hbddA hx⟩

/-- **Pólya's shift.** If some root is bad, shifting the roots to the right of the gap after
the rightmost bad root to the left produces a new root multiset of the same size with fewer
bad roots, whose sublevel set receives `P` by a cut-and-shift map. -/
lemma shift_step {s : Multiset ℝ} (hbad : 0 < badCount s) :
    ∃ s1 : Multiset ℝ, Multiset.card s1 = Multiset.card s ∧ badCount s1 < badCount s ∧
      ∃ u d : ℝ, ∀ x ∈ sublevel s,
        (x ≤ u ∧ x ∈ sublevel s1) ∨ (u ≤ x - d ∧ x - d ∈ sublevel s1) := by
  set Bset := s.toFinset.filter fun a => ¬ Good s a with hBset
  have hBne : Bset.Nonempty := Finset.card_pos.mp hbad
  set α := Bset.max' hBne
  have hαB : α ∈ Bset := Finset.max'_mem _ _
  have hαs : α ∈ s := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hαB).1
  have hαbad : ¬ Good s α := (Finset.mem_filter.mp hαB).2
  have hαmax : ∀ a ∈ s, ¬ Good s a → a ≤ α := fun a ha hna =>
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ha, hna⟩)
  obtain ⟨c, hαc, ⟨b, hb, hcb⟩, hc2⟩ :
      ∃ x, α ≤ x ∧ (∃ b ∈ s, x ≤ b) ∧ 2 < |rootProd s x| := by
    by_contra h
    push Not at h
    exact hαbad fun x h1 h2 => h x h1 h2
  have hcα : α < c := lt_of_le_of_ne hαc (by
    rintro rfl; rw [rootProd_eq_zero_of_mem hαs] at hc2; norm_num at hc2)
  set Above := s.toFinset.filter (α < ·) with hAbove
  have hAne : Above.Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hb, by linarith⟩⟩
  set β := Above.min' hAne
  have hβA : β ∈ Above := Finset.min'_mem _ _
  have hβs : β ∈ s := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hβA).1
  have hαβ : α < β := (Finset.mem_filter.mp hβA).2
  have hβmin : ∀ a ∈ s, α < a → β ≤ a := fun a ha h =>
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ha, h⟩)
  have hroots : ∀ a ∈ s, a ≤ α ∨ β ≤ a := fun a ha => (le_or_gt a α).imp id (hβmin a ha)
  have hgoodAbove : ∀ a ∈ s, α < a → Good s a := fun a ha h => by
    by_contra hna; linarith [hαmax a ha hna]
  have hcβ : c < β := by
    by_contra h
    push Not at h
    have := hgoodAbove β hβs hαβ c h ⟨b, hb, hcb⟩
    linarith
  obtain ⟨u, v, hαu, huv, hvβ, hleft, hright, hgap⟩ := gap_structure hroots
    (by rw [rootProd_eq_zero_of_mem hαs]; norm_num)
    (by rw [rootProd_eq_zero_of_mem hβs]; norm_num) ⟨hcα, hcβ⟩ hc2
  set d := v - u with hd
  set r := s.filter (· ≤ α) with hr_def
  set q := s.filter (fun a => ¬ a ≤ α) with hq_def
  have hsrq : s = r + q := (Multiset.filter_add_not _ s).symm
  have hr : ∀ a ∈ r, a ≤ α := fun a ha => (Multiset.mem_filter.mp ha).2
  have hqs : ∀ a ∈ q, a ∈ s := fun a ha => (Multiset.mem_filter.mp ha).1
  have hq : ∀ a ∈ q, β ≤ a := fun a ha =>
    hβmin a (hqs a ha) (not_le.mp (Multiset.mem_filter.mp ha).2)
  have hrs : ∀ a ∈ r, a ∈ s := fun a ha => (Multiset.mem_filter.mp ha).1
  set s1 := r + q.map (· - d) with hs1
  have hR : ∀ x, rootProd s x = rootProd r x * rootProd q x := fun x => by
    conv_lhs => rw [hsrq]
    rw [rootProd_add]
  have hR1 : ∀ x, rootProd s1 x = rootProd r x * rootProd q (x + d) := fun x => by
    rw [hs1, rootProd_add, rootProd_map_sub]
  -- to the left of the gap, `|p₁| ≤ |p|`
  have hi : ∀ x ≤ u, |rootProd s1 x| ≤ |rootProd s x| := by
    intro x hx
    rw [hR1, hR, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply abs_rootProd_le
    intro b hb
    have := hq b hb
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  -- to the right of the gap, `|p₁(x - d)| ≤ |p(x)|`
  have hii : ∀ x, v ≤ x → |rootProd s1 (x - d)| ≤ |rootProd s x| := by
    intro x hx
    rw [hR1, hR, sub_add_cancel, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply abs_rootProd_le
    intro a ha
    have := hr a ha
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  refine ⟨s1, ?_, ?_, u, d, ?_⟩
  · rw [hs1]
    conv_rhs => rw [hsrq]
    simp [Multiset.card_add, Multiset.card_map]
  · have hsub : (s1.toFinset.filter fun a => ¬ Good s1 a) ⊆ Bset.erase α := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      have hw1 := Multiset.mem_toFinset.mp hw1
      rcases Multiset.mem_add.mp hw1 with hwr | hwq
      · have hwα := hr w hwr
        rcases eq_or_lt_of_le hwα with heq | hlt
        · exfalso
          apply hw2
          rw [heq]
          rintro x hx ⟨e, he, hxe⟩
          rcases le_or_gt x u with hxu | hxu
          · exact (hi x hxu).trans (hleft x ⟨hx, hxu⟩)
          · rcases Multiset.mem_add.mp he with her | heq'
            · linarith [hr e her]
            · obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp heq'
              have hb's := hqs b' hb'
              have h1 : |rootProd s (x + d)| ≤ 2 := by
                rcases le_or_gt β (x + d) with h1 | h1
                · exact hgoodAbove β hβs hαβ (x + d) h1 ⟨b', hb's, by linarith⟩
                · exact hright (x + d) ⟨by linarith, h1.le⟩
              have h2 := hii (x + d) (by linarith)
              rw [add_sub_cancel_right] at h2
              linarith
        · refine Finset.mem_erase.mpr ⟨hlt.ne, Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr (hrs w hwr), ?_⟩⟩
          intro hg
          have := hg c (by linarith) ⟨b, hb, hcb⟩
          linarith
      · exfalso
        obtain ⟨b', hb', rfl⟩ := Multiset.mem_map.mp hwq
        apply hw2
        rintro x hx ⟨e, he, hxe⟩
        have h2 := hq b' hb'
        rcases Multiset.mem_add.mp he with her | heq'
        · have h1 := hr e her
          have hxe' : x = e := by linarith
          rw [hxe', rootProd_eq_zero_of_mem he]
          norm_num
        · obtain ⟨b'', hb'', rfl⟩ := Multiset.mem_map.mp heq'
          have hgb : Good s b' := hgoodAbove b' (hqs b' hb') (by linarith)
          have h4 := hgb (x + d) (by linarith) ⟨b'', hqs b'' hb'', by linarith⟩
          have h3 := hii (x + d) (by linarith)
          rw [add_sub_cancel_right] at h3
          linarith
    calc badCount s1 = (s1.toFinset.filter fun a => ¬ Good s1 a).card := rfl
      _ ≤ (Bset.erase α).card := Finset.card_le_card hsub
      _ < Bset.card := Finset.card_erase_lt_of_mem hαB
  · intro x hx
    have hx2 : |rootProd s x| ≤ 2 := hx
    rcases le_or_gt x u with h | h
    · exact Or.inl ⟨h, (hi x h).trans hx2⟩
    · rcases le_or_gt v x with h' | h'
      · exact Or.inr ⟨by linarith, (hii x h').trans hx2⟩
      · have := hgap x ⟨h, h'⟩
        linarith

/-- Theorem 2 for the product `∏_{a ∈ s} (x - a)`. -/
theorem coverable_sublevel (s : Multiset ℝ) (hs : s ≠ 0) : Coverable (sublevel s) 4 := by
  induction h : badCount s using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · apply coverable_of_all_good hs
      intro a ha
      by_contra hna
      have hmem : a ∈ s.toFinset.filter (fun a => ¬ Good s a) :=
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ha, hna⟩
      have := Finset.card_pos.mpr ⟨a, hmem⟩
      rw [badCount] at h
      omega
    · obtain ⟨s1, hcard, hlt, u, d, hcov⟩ := shift_step (h ▸ hk)
      have hs1 : s1 ≠ 0 := by
        intro h0
        rw [h0, Multiset.card_zero] at hcard
        exact hs (Multiset.card_eq_zero.mp hcard.symm)
      exact (ih _ (h ▸ hlt) s1 hs1 rfl).cut_shift hcov

/-- **Theorem 2.** Let `p` be a real polynomial of degree `n ≥ 1` with leading coefficient `1`
and all roots real. Then `P = {x ∈ ℝ | |p x| ≤ 2}` can be covered by finitely many intervals
`[a_i, b_i]` of total length at most `4`. -/
theorem theorem_2 (p : ℝ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree)
    (hroots : Multiset.card p.roots = p.natDegree) :
    ∃ I : List (ℝ × ℝ), (∀ i ∈ I, i.1 ≤ i.2) ∧
      {x : ℝ | |p.eval x| ≤ 2} ⊆ ⋃ i ∈ I, Icc i.1 i.2 ∧
      (I.map fun i => i.2 - i.1).sum ≤ 4 := by
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hroots
  have hs : p.roots ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hroots; omega
  have heq : {x : ℝ | |p.eval x| ≤ 2} = sublevel p.roots := by
    ext x
    simp only [sublevel, mem_ofPred_eq, ← eval_prod_X_sub_C, hprod]
  rw [heq]
  exact coverable_sublevel p.roots hs

/-- The first step of the proof of Theorem 1 ("by the theorem of Pythagoras"):
if `f(z) = (z - c₁) ⋯ (z - cₙ)` and `p(x) = (x - Re c₁) ⋯ (x - Re cₙ)`, then
`|p (Re z)| ≤ |f z|`. -/
lemma abs_rootProd_re_le_norm (t : Multiset ℂ) (z : ℂ) :
    |rootProd (t.map Complex.re) z.re| ≤ ‖(t.map fun c => z - c).prod‖ := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons c t ih =>
    simp only [Multiset.map_cons, rootProd_cons, Multiset.prod_cons, abs_mul, norm_mul]
    refine mul_le_mul ?_ ih (abs_nonneg _) (norm_nonneg _)
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _

/-- With `f` monic complex and `p(x) = ∏ (x - Re cₖ)` over the roots `cₖ` of `f`, we have
`|p (Re z)| ≤ |f z|` for all `z`. -/
theorem abs_eval_re_le_norm_eval (f : ℂ[X]) (hf : f.Monic) (z : ℂ) :
    |((f.roots.map fun c : ℂ => X - C c.re).prod).eval z.re| ≤ ‖f.eval z‖ := by
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf
    IsAlgClosed.card_roots_eq_natDegree
  have h1 : (f.roots.map fun c : ℂ => X - C c.re) =
      ((f.roots.map Complex.re).map fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [h1, eval_prod_X_sub_C]
  conv_rhs => rw [← hprod]
  rw [eval_multiset_prod, Multiset.map_map]
  simpa only [Function.comp_apply, eval_sub, eval_X, eval_C] using
    abs_rootProd_re_le_norm f.roots z

/-- **Theorem 1 (Pólya).** Let `f` be a complex polynomial of degree at least `1` with
leading coefficient `1`. Set `C = {z ∈ ℂ | |f z| ≤ 2}` and let `R` be the orthogonal
projection of `C` onto the real axis. Then there are intervals `I₁, …, I_t` on the real line
which together cover `R` and satisfy `ℓ(I₁) + ⋯ + ℓ(I_t) ≤ 4`. -/
theorem theorem_1 (f : ℂ[X]) (hf : f.Monic) (hn : 1 ≤ f.natDegree) :
    ∃ I : List (ℝ × ℝ), (∀ i ∈ I, i.1 ≤ i.2) ∧
      Complex.re '' {z : ℂ | ‖f.eval z‖ ≤ 2} ⊆ ⋃ i ∈ I, Icc i.1 i.2 ∧
      (I.map fun i => i.2 - i.1).sum ≤ 4 := by
  set p : ℝ[X] := (f.roots.map fun c : ℂ => X - C c.re).prod with hp
  have hcard : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hpm : (f.roots.map fun c : ℂ => X - C c.re) =
    ((f.roots.map Complex.re).map fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  have hpmon : p.Monic := by rw [hp, hpm]; exact monic_prod_X_sub_C _
  have hpdeg : p.natDegree = f.natDegree := by
    rw [hp, hpm, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]
  have hproots : Multiset.card p.roots = p.natDegree := by
    rw [hp, hpm, roots_multiset_prod_X_sub_C, natDegree_multiset_prod_X_sub_C_eq_card]
  obtain ⟨I, h1, h2, h3⟩ := theorem_2 p hpmon (hpdeg ▸ hn) hproots
  refine ⟨I, h1, ?_, h3⟩
  rintro _ ⟨z, hz, rfl⟩
  apply h2
  exact (abs_eval_re_le_norm_eval f hf z).trans hz

end Chapter23

/-! ### Measure-theoretic reformulation -/

namespace Chapter23

open MeasureTheory

/-- A set covered by intervals of total length at most `L` has Lebesgue measure at most `L`. -/
lemma volume_le_of_coverable {S : Set ℝ} {L : ℝ} (h : Coverable S L) :
    volume S ≤ ENNReal.ofReal L := by
  obtain ⟨I, hI, hS, hL⟩ := h
  have aux : ∀ I : List (ℝ × ℝ), (∀ i ∈ I, i.1 ≤ i.2) →
      volume (⋃ i ∈ I, Icc i.1 i.2) ≤ ENNReal.ofReal (I.map fun i => i.2 - i.1).sum := by
    intro I
    induction I with
    | nil => intro _; simp
    | cons i I ih =>
      intro hI
      have hi := hI i List.mem_cons_self
      have hI' : ∀ j ∈ I, j.1 ≤ j.2 := fun j hj => hI j (List.mem_cons_of_mem _ hj)
      have hnn : 0 ≤ (I.map fun i => i.2 - i.1).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        linarith [hI' j hj]
      have hU : (⋃ j ∈ i :: I, Icc j.1 j.2) = Icc i.1 i.2 ∪ ⋃ j ∈ I, Icc j.1 j.2 := by
        ext x; simp [List.mem_cons]
      rw [hU, List.map_cons, List.sum_cons, ENNReal.ofReal_add (by linarith) hnn]
      refine (measure_union_le _ _).trans (add_le_add ?_ (ih hI'))
      rw [Real.volume_Icc]
  exact (measure_mono hS).trans ((aux I hI).trans (ENNReal.ofReal_le_ofReal hL))

/-- Theorem 2, measure version: `P = {x | |p x| ≤ 2}` has Lebesgue measure at most `4`. -/
theorem theorem_2_volume (p : ℝ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree)
    (hroots : Multiset.card p.roots = p.natDegree) :
    volume {x : ℝ | |p.eval x| ≤ 2} ≤ 4 := by
  have := volume_le_of_coverable (theorem_2 p hp hn hroots)
  simpa using this

/-- Theorem 1, measure version: the projection of `C = {z | |f z| ≤ 2}` onto the real axis has
Lebesgue (outer) measure at most `4`. -/
theorem theorem_1_volume (f : ℂ[X]) (hf : f.Monic) (hn : 1 ≤ f.natDegree) :
    volume (Complex.re '' {z : ℂ | ‖f.eval z‖ ≤ 2}) ≤ 4 := by
  have := volume_le_of_coverable (theorem_1 f hf hn)
  simpa using this

end Chapter23

end

/-! ## Contents of former file `Chapter_23/Appendix.lean` -/

/-!
# Appendix of Chapter 23: cosine polynomials

* Equation (7): `cos nθ` is a polynomial in `cos θ` of degree `n` with leading coefficient
  `2^(n-1)` (the Chebyshev polynomial `T_n`), and the binomial identity
  `∑_{ℓ} (n choose 2ℓ) = 2^(n-1)` used to compute this leading coefficient.
* Step (A): `p(cos θ)` is a cosine polynomial `∑ b_k cos kθ` whose leading coefficient is
  `b_n = 1/2^(n-1)`.
* Step (B): a cosine polynomial `h(θ) = ∑_{k ≤ n} λ_k cos kθ` satisfies
  `|λ_n| ≤ max |h(θ)|`.
* Chebyshev's theorem obtained from (A) and (B), as in the book.
* The polynomials `x`, `x² - 1/2`, `x³ - 3/4 x`, and in general `T_n(x) / 2^(n-1)`,
  attain equality in Chebyshev's theorem.
-/

public section

open Polynomial Set Finset

namespace Chapter23

/-- Equation (7): `cos nθ = c_n (cos θ)^n + ⋯ + c_0` with `c_n = 2^(n-1)`. -/
theorem cos_nat_mul_eq_poly (n : ℕ) :
    ∃ P : ℝ[X], P.natDegree = n ∧ P.leadingCoeff = 2 ^ (n - 1) ∧
      ∀ θ : ℝ, P.eval (Real.cos θ) = Real.cos (n * θ) := by
  refine ⟨Chebyshev.T ℝ n, by simp [Chebyshev.natDegree_T], by simp [Chebyshev.leadingCoeff_T],
    fun θ => ?_⟩
  rw [Chebyshev.T_real_cos]
  simp

/-- The margin identity: `∑_{k even} (n choose k) = 2^(n-1)` for `n > 0`. -/
theorem sum_even_choose (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ (range (n + 1)).filter Even, n.choose k = 2 ^ (n - 1) := by
  have h1 : ∑ m ∈ range (n + 1), (n.choose m : ℤ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have h2 := Int.alternating_sum_range_choose (n := n)
  simp only [hn.ne', ↓reduceIte] at h2
  have h3 : ∑ m ∈ range (n + 1), (n.choose m : ℤ) + ∑ m ∈ range (n + 1), (-1) ^ m * (n.choose m : ℤ)
      = 2 * ∑ m ∈ range (n + 1), (if Even m then (n.choose m : ℤ) else 0) := by
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro m _
    rcases Nat.even_or_odd m with h | h
    · simp only [h, ↓reduceIte, h.neg_one_pow]; ring
    · simp only [Nat.not_even_iff_odd.mpr h, ↓reduceIte, h.neg_one_pow]; ring
  rw [h1, h2, add_zero, ← sum_filter] at h3
  have h4 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h4] at h3
  have h5 : (∑ k ∈ (range (n + 1)).filter Even, (n.choose k : ℤ)) = 2 ^ (n - 1) := by
    linarith
  exact_mod_cast h5

/-- Every real polynomial of degree `≤ n` is a linear combination of the Chebyshev polynomials
`T_0, …, T_n`, and the coefficient of `T_n` is `coeff n / 2^(n-1)`. -/
lemma exists_chebyshev_expansion (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    ∃ b : ℕ → ℝ, p = ∑ k ∈ range (n + 1), C (b k) * Chebyshev.T ℝ k ∧
      b n * 2 ^ (n - 1) = p.coeff n := by
  induction n generalizing p with
  | zero =>
    refine ⟨fun _ => p.coeff 0, ?_, by simp⟩
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, Chebyshev.T_zero, mul_one]
    exact eq_C_of_natDegree_le_zero hp
  | succ n ih =>
    set c := p.coeff (n + 1)
    set q := p - C (c / 2 ^ n) * Chebyshev.T ℝ (n + 1 : ℕ) with hq
    have hTdeg : (Chebyshev.T ℝ (n + 1 : ℕ)).natDegree = n + 1 := by
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
    have hTc : (Chebyshev.T ℝ (n + 1 : ℕ)).coeff (n + 1) = 2 ^ n := by
      have := Chebyshev.leadingCoeff_T ℝ (n + 1 : ℕ)
      rw [leadingCoeff, hTdeg] at this
      rw [this, Int.natAbs_natCast, Nat.add_sub_cancel]
    have hqdeg : q.natDegree ≤ n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hq, coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h | h
      · rw [← h, hTc]; field_simp; ring
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h),
          coeff_eq_zero_of_natDegree_lt (by rw [hTdeg]; exact h)]
        ring
    obtain ⟨b', hb', -⟩ := ih q hqdeg
    refine ⟨fun k => if k = n + 1 then c / 2 ^ n else b' k, ?_, ?_⟩
    · rw [sum_range_succ]
      dsimp only
      simp only [↓reduceIte]
      have : ∑ k ∈ range (n + 1), C (if k = n + 1 then c / 2 ^ n else b' k) * Chebyshev.T ℝ k
          = ∑ k ∈ range (n + 1), C (b' k) * Chebyshev.T ℝ k := by
        apply sum_congr rfl
        intro k hk
        have hne : k ≠ n + 1 := by simp at hk; omega
        simp only [hne, ↓reduceIte]
      rw [this, ← hb', hq]
      push_cast
      ring
    · simp only [↓reduceIte, Nat.add_sub_cancel]
      field_simp

/-- **Step (A).** For a real polynomial `p` of degree `n ≥ 1` with leading coefficient `1`,
`g(θ) = p(cos θ)` is a cosine polynomial `b_n cos nθ + ⋯ + b_1 cos θ + b_0` whose leading
coefficient is `b_n = 1/2^(n-1)`. -/
theorem step_A (p : ℝ[X]) (hp : p.Monic) :
    ∃ b : ℕ → ℝ, b p.natDegree = 1 / 2 ^ (p.natDegree - 1) ∧
      ∀ θ : ℝ, p.eval (Real.cos θ) =
        ∑ k ∈ range (p.natDegree + 1), b k * Real.cos (k * θ) := by
  obtain ⟨b, hb, hbn⟩ := exists_chebyshev_expansion p.natDegree p le_rfl
  refine ⟨b, ?_, fun θ => ?_⟩
  · rw [eq_div_iff (by positivity), hbn]
    exact hp.coeff_natDegree
  · conv_lhs => rw [hb]
    rw [eval_finsetSum]
    apply sum_congr rfl
    intro k _
    rw [eval_mul, eval_C, Chebyshev.T_real_cos]
    simp

/-- The polynomial `∑_{k ≤ n} λ_k T_k` has degree `n` and leading coefficient `λ_n 2^(n-1)`
if `λ_n ≠ 0` and `n ≥ 1`. -/
lemma chebyshev_sum_natDegree_leadingCoeff (n : ℕ) (hn : 1 ≤ n) (l : ℕ → ℝ) (hl : l n ≠ 0) :
    (∑ k ∈ range (n + 1), C (l k) * Chebyshev.T ℝ k).natDegree = n ∧
      (∑ k ∈ range (n + 1), C (l k) * Chebyshev.T ℝ k).leadingCoeff = l n * 2 ^ (n - 1) := by
  rw [sum_range_succ]
  set A := ∑ k ∈ range n, C (l k) * Chebyshev.T ℝ k
  set B := C (l n) * Chebyshev.T ℝ n
  have hBdeg : B.natDegree = n := by
    rw [natDegree_C_mul hl, Chebyshev.natDegree_T]; simp
  have hBlc : B.leadingCoeff = l n * 2 ^ (n - 1) := by
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hl), Chebyshev.leadingCoeff_T]
    simp
  have hB0 : B ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hBdeg; omega
  have hAdeg : A.natDegree ≤ n - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    simp at hk
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Chebyshev.natDegree_T]; simp; omega
  have hlt : A.degree < B.degree := by
    rw [degree_eq_natDegree hB0, hBdeg]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le hAdeg) ?_
    exact_mod_cast (by omega : n - 1 < n)
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_right_of_degree_lt hlt, hBdeg]
  · rw [leadingCoeff_add_of_degree_lt hlt, hBlc]

/-- **Step (B).** For any cosine polynomial `h(θ) = λ_n cos nθ + ⋯ + λ_1 cos θ + λ_0`,
we have `|λ_n| ≤ max_θ |h(θ)|`. -/
theorem step_B (n : ℕ) (l : ℕ → ℝ) :
    ∃ θ : ℝ, |l n| ≤ |∑ k ∈ range (n + 1), l k * Real.cos (k * θ)| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  by_cases hl : l n = 0
  · exact ⟨0, by rw [hl, abs_zero]; exact abs_nonneg _⟩
  set P := ∑ k ∈ range (n + 1), C (l k) * Chebyshev.T ℝ k
  obtain ⟨hPdeg, hPlc⟩ := chebyshev_sum_natDegree_leadingCoeff n hn l hl
  obtain ⟨x, hx, hle⟩ := chebyshev_leadingCoeff P n hn hPdeg
  refine ⟨Real.arccos x, ?_⟩
  have heval : P.eval (Real.cos (Real.arccos x)) =
      ∑ k ∈ range (n + 1), l k * Real.cos (k * Real.arccos x) := by
    rw [eval_finsetSum]
    apply sum_congr rfl
    intro k _
    rw [eval_mul, eval_C, Chebyshev.T_real_cos]
    simp
  rw [← heval, Real.cos_arccos hx.1 hx.2]
  rw [hPlc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n - 1)),
    mul_div_assoc, div_self (by positivity), mul_one] at hle
  exact hle

/-- Chebyshev's theorem deduced from (A) and (B), following the book: apply (B) to the cosine
polynomial `g(θ) = p(cos θ)` provided by (A). -/
theorem chebyshev_of_A_B (p : ℝ[X]) (hp : p.Monic) :
    ∃ x ∈ Icc (-1 : ℝ) 1, 1 / 2 ^ (p.natDegree - 1) ≤ |p.eval x| := by
  obtain ⟨b, hbn, hb⟩ := step_A p hp
  obtain ⟨θ, hθ⟩ := step_B p.natDegree b
  refine ⟨Real.cos θ, ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩, ?_⟩
  rw [hb θ, ← hbn]
  exact (le_abs_self _).trans hθ

/-- The polynomial `T_n(x) / 2^(n-1)` is monic of degree `n` and attains equality in
Chebyshev's theorem: `max_{-1 ≤ x ≤ 1} |T_n(x)/2^(n-1)| = 1/2^(n-1)`. -/
theorem chebyshev_equality (n : ℕ) :
    (C (1 / 2 ^ (n - 1)) * Chebyshev.T ℝ n).Monic ∧
      (C (1 / 2 ^ (n - 1)) * Chebyshev.T ℝ n).natDegree = n ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, |(C (1 / 2 ^ (n - 1)) * Chebyshev.T ℝ n).eval x| ≤ 1 / 2 ^ (n - 1)) ∧
      |(C (1 / 2 ^ (n - 1)) * Chebyshev.T ℝ n).eval 1| = 1 / 2 ^ (n - 1) := by
  have h2 : (1 : ℝ) / 2 ^ (n - 1) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Monic, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr h2),
      Chebyshev.leadingCoeff_T]
    simp
  · rw [natDegree_C_mul h2, Chebyshev.natDegree_T]; simp
  · intro x hx
    rw [eval_mul, eval_C, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ (n - 1))]
    rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  · rw [eval_mul, eval_C, ← Real.cos_zero, Chebyshev.T_real_cos, mul_zero, Real.cos_zero,
      mul_one, abs_of_pos (by positivity)]

/-- The polynomials `p₁(x) = x`, `p₂(x) = x² - 1/2` and `p₃(x) = x³ - 3/4 x` achieve equality
in Chebyshev's theorem. -/
theorem chebyshev_equality_examples :
    ((∀ x ∈ Icc (-1 : ℝ) 1, |x| ≤ 1) ∧ |(1 : ℝ)| = 1) ∧
    ((∀ x ∈ Icc (-1 : ℝ) 1, |x ^ 2 - 1 / 2| ≤ 1 / 2) ∧ |(1 : ℝ) ^ 2 - 1 / 2| = 1 / 2) ∧
    ((∀ x ∈ Icc (-1 : ℝ) 1, |x ^ 3 - 3 / 4 * x| ≤ 1 / 4) ∧
      |(1 : ℝ) ^ 3 - 3 / 4 * 1| = 1 / 4) := by
  refine ⟨⟨fun x hx => abs_le.mpr hx, by norm_num⟩, ⟨fun x hx => ?_, by norm_num⟩,
    ⟨fun x hx => ?_, by norm_num⟩⟩
  · obtain ⟨h1, h2⟩ := hx
    rw [abs_le]; constructor <;> nlinarith
  · obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) (neg_le_iff_add_nonneg.mp h1))
        (sq_nonneg (2 * x - 1)), mul_nonneg (sub_nonneg.mpr h2) (neg_le_iff_add_nonneg.mp h1)]
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) (neg_le_iff_add_nonneg.mp h1))
        (sq_nonneg (2 * x + 1)), mul_nonneg (sub_nonneg.mpr h2) (neg_le_iff_add_nonneg.mp h1)]

/-- The sign of `∏_{j ≠ k} (x_k - x_j)` at the Chebyshev nodes is `(-1)^k`. -/
lemma neg_one_pow_mul_prod_chebNode_pos {n k : ℕ} (hn : 1 ≤ n) (hk : k ∈ range (n + 1)) :
    0 < (-1) ^ k * ∏ j ∈ (range (n + 1)).erase k, (chebNode n k - chebNode n j) := by
  set E := (range (n + 1)).erase k
  have hk' : k ≤ n := by simp at hk; omega
  have hsign : ∏ j ∈ E, (if j < k then (-1 : ℝ) else 1) = (-1) ^ k := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    congr 1
    have : E.filter (· < k) = range k := by
      ext j; simp [E]; omega
    rw [this, card_range]
  rw [← hsign, ← prod_mul_distrib]
  apply prod_pos
  intro j hj
  have hjk : j ≠ k := (mem_erase.mp hj).1
  have hjn : j ≤ n := by have := (mem_erase.mp hj).2; simp at this; omega
  split_ifs with h
  · have := chebNode_strictAnti hn h hk'
    linarith
  · have := chebNode_strictAnti hn (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hjk)) hjn
    linarith

/-- **Uniqueness of the extremal polynomial** (the exercise at the end of the chapter):
`T_n(x) / 2^(n-1)` is the only monic polynomial of degree `n ≥ 1` with
`max_{-1 ≤ x ≤ 1} |p x| ≤ 1/2^(n-1)`, i.e. the only one achieving equality in
Chebyshev's theorem. -/
theorem chebyshev_equality_unique (p : ℝ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree)
    (hmax : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 / 2 ^ (p.natDegree - 1)) :
    p = C (1 / 2 ^ (p.natDegree - 1)) * Chebyshev.T ℝ p.natDegree := by
  set n := p.natDegree with hn_def
  set E : ℝ := 1 / 2 ^ (n - 1) with hE
  set Q := C E * Chebyshev.T ℝ n with hQ
  obtain ⟨hQm, hQdeg, -, -⟩ := chebyshev_equality n
  have hp0 : p ≠ 0 := hp.ne_zero
  have hQ0 : Q ≠ 0 := hQm.ne_zero
  set r := Q - p with hr
  have hrdeg : r.degree < (n : ℕ) := by
    by_cases hr0 : r = 0
    · rw [hr0, degree_zero]; exact WithBot.bot_lt_coe _
    · have hdeg' : Q.degree = p.degree := by
        rw [degree_eq_natDegree hQ0, degree_eq_natDegree hp0, hQdeg]
      have := degree_sub_lt_left hdeg' hQ0 (by rw [hQm.leadingCoeff, hp.leadingCoeff])
      rw [← hr, degree_eq_natDegree hQ0, hQdeg] at this
      exact this
  -- weak sign alternation at the nodes
  have hsign : ∀ k ∈ range (n + 1), 0 ≤ (-1) ^ k * r.eval (chebNode n k) := by
    intro k _
    rw [hr, eval_sub, hQ, eval_mul, eval_C, eval_chebNode hn, mul_sub]
    have hsq : (-1 : ℝ) ^ k * (E * (-1) ^ k) = E := by
      rw [mul_left_comm, ← pow_add, ← two_mul, pow_mul]; simp
    rw [hsq]
    have h1 := hmax _ (chebNode_mem (n := n) (k := k))
    have h2 : (-1 : ℝ) ^ k * p.eval (chebNode n k) ≤ |p.eval (chebNode n k)| := by
      refine (le_abs_self _).trans (le_of_eq ?_)
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    linarith
  -- the `n`-th coefficient of `r` vanishes, giving a sum of nonnegative terms equal to `0`
  have hinj : Set.InjOn (chebNode n) ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (chebNode_strictAnti hn h (by omega)).ne' hij
    · exact (chebNode_strictAnti hn h (by omega)).ne hij
  have hcoeff := Lagrange.coeff_eq_sum hinj (P := r) (by rw [card_range]; exact_mod_cast
    (lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_succ n)))
  rw [card_range, Nat.add_sub_cancel, coeff_eq_zero_of_degree_lt hrdeg] at hcoeff
  have hterm : ∀ k ∈ range (n + 1), 0 ≤ r.eval (chebNode n k) /
      ∏ j ∈ (range (n + 1)).erase k, (chebNode n k - chebNode n j) := by
    intro k hk
    have h1 := hsign k hk
    have h2 := neg_one_pow_mul_prod_chebNode_pos hn hk
    have : r.eval (chebNode n k) / ∏ j ∈ (range (n + 1)).erase k, (chebNode n k - chebNode n j)
        = ((-1) ^ k * r.eval (chebNode n k)) /
          ((-1) ^ k * ∏ j ∈ (range (n + 1)).erase k, (chebNode n k - chebNode n j)) := by
      rw [mul_div_mul_left]
      exact pow_ne_zero _ (by norm_num)
    rw [this]
    exact div_nonneg h1 h2.le
  have hzero := (sum_eq_zero_iff_of_nonneg hterm).mp hcoeff.symm
  have hroots : ∀ k : Fin n, r.eval (chebNode n k) = 0 := by
    intro k
    have hk : (k : ℕ) ∈ range (n + 1) := by simp
    have h := hzero k hk
    have h2 := neg_one_pow_mul_prod_chebNode_pos hn hk
    have hne : ∏ j ∈ (range (n + 1)).erase k, (chebNode n k - chebNode n j) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h2; exact lt_irrefl _ h2
    exact (div_eq_zero_iff.mp h).resolve_right hne
  have hinj' : Function.Injective fun k : Fin n => chebNode n k := by
    intro i j hij
    apply Fin.ext
    exact hinj (by simp) (by simp) hij
  have hrnat : r.natDegree < n := by
    by_cases hr0 : r = 0
    · rw [hr0, natDegree_zero]; omega
    · rw [degree_eq_natDegree hr0] at hrdeg; exact_mod_cast hrdeg
  have hr0 : r = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero r hinj' hroots (by simpa using hrnat)
  exact (sub_eq_zero.mp hr0).symm

end Chapter23

end

/-! ## Contents of former file `Chapter_23/Examples.lean` -/

/-!
# Examples from Chapter 23

* For `f(z) = z² - 2`: `x + iy ∈ C` iff `(x² + y²)² ≤ 4 (x² - y²)`, and the projection
  `R` of `C` onto the real axis is exactly `[-2, 2]`, of length `4`.
* For `f(z) = z - c` (degree 1), `C` is a disk of diameter `4`, whose projection is an
  interval of length `4`.
* For `p(x) = x²(x - 3)`: `P = [1 - √3, 1] ∪ [1 + √3, γ]` with `γ ≈ 3.2`, the real root of
  `x³ - 3x² - 2`.
-/

public section

open Set Complex

namespace Chapter23

/-- For `f(z) = z² - 2` and `z = x + iy`: `|f z| ≤ 2 ↔ (x² + y²)² ≤ 4 (x² - y²)`. -/
theorem sq_sub_two_mem_iff (x y : ℝ) :
    ‖(x + y * I) ^ 2 - 2‖ ≤ 2 ↔ (x ^ 2 + y ^ 2) ^ 2 ≤ 4 * (x ^ 2 - y ^ 2) := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have hre : ((x + y * I) ^ 2 - 2).re = x ^ 2 - y ^ 2 - 2 := by simp [sq]
  have him : ((x + y * I) ^ 2 - 2).im = 2 * x * y := by simp [sq]; ring
  rw [hre, him]
  constructor <;> intro h <;> nlinarith

/-- For `f(z) = z² - 2`, the projection of `C = {z | |f z| ≤ 2}` to the real axis is
`[-2, 2]`. -/
theorem sq_sub_two_projection :
    Complex.re '' {z : ℂ | ‖z ^ 2 - 2‖ ≤ 2} = Icc (-2) 2 := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : ‖(z.re + z.im * I) ^ 2 - 2‖ ≤ 2 := by rwa [Complex.re_add_im]
    rw [sq_sub_two_mem_iff] at hz'
    have h4 : z.re ^ 2 ≤ 4 := by nlinarith [sq_nonneg z.im, sq_nonneg z.re]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨x, ?_, by simp⟩
    simp only [mem_ofPred_eq]
    have : ((x : ℂ) ^ 2 - 2) = ((x ^ 2 - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

/-- For `n = 1`, i.e. `f(z) = z - c`, the set `C` is the closed disk of radius `2` (diameter
`4`) around `c`, and its projection onto the real axis is `[Re c - 2, Re c + 2]`. -/
theorem linear_projection (c : ℂ) :
    Complex.re '' {z : ℂ | ‖z - c‖ ≤ 2} = Icc (c.re - 2) (c.re + 2) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := (Complex.abs_re_le_norm (z - c)).trans hz
    rw [Complex.sub_re, abs_le] at this
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    refine ⟨x + c.im * I, ?_, by simp⟩
    simp only [mem_ofPred_eq]
    have : (x : ℂ) + c.im * I - c = ((x - c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith

/-- For `p(x) = x²(x - 3)`, the set `P = {x | |p x| ≤ 2}` consists of two intervals:
`P = [1 - √3, 1] ∪ [1 + √3, γ]`, where `γ ≈ 3.2` is the real root of `x³ - 3x² - 2`. -/
theorem example_two_intervals :
    ∃ γ : ℝ, 3.19 < γ ∧ γ < 3.2 ∧ γ ^ 3 - 3 * γ ^ 2 - 2 = 0 ∧
      {x : ℝ | |x ^ 2 * (x - 3)| ≤ 2} = Icc (1 - √3) 1 ∪ Icc (1 + √3) γ := by
  have hcont : Continuous fun x : ℝ => x ^ 3 - 3 * x ^ 2 - 2 := by fun_prop
  obtain ⟨γ, ⟨hγ1, hγ2⟩, hγ⟩ := intermediate_value_Ioo (show (3.19 : ℝ) ≤ 3.2 by norm_num)
    hcont.continuousOn (show (0 : ℝ) ∈ Ioo _ _ by constructor <;> norm_num)
  simp only at hγ
  refine ⟨γ, hγ1, hγ2, hγ, ?_⟩
  set s := √3 with hs
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : s < 1.8 := by nlinarith
  have hs1' : 1.7 < s := by nlinarith
  -- factorizations
  have hlow : ∀ x : ℝ, x ^ 2 * (x - 3) + 2 = (x - 1) * ((x - 1 - s) * (x - 1 + s)) := by
    intro x; ring_nf; rw [hs2]; ring
  have hup : ∀ x : ℝ, x ^ 2 * (x - 3) - 2 =
      (x - γ) * ((x + (γ - 3) / 2) ^ 2 + 3 * (γ - 3) * (γ + 1) / 4) := by
    intro x; ring_nf; nlinarith [hγ]
  have hQ : ∀ x : ℝ, 0 < (x + (γ - 3) / 2) ^ 2 + 3 * (γ - 3) * (γ + 1) / 4 := by
    intro x; nlinarith [sq_nonneg (x + (γ - 3) / 2)]
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have hxγ : x ≤ γ := by
      by_contra h
      push Not at h
      have := hup x
      have := mul_pos (sub_pos.mpr h) (hQ x)
      linarith
    have hl := hlow x
    by_cases hx1 : x ≤ 1
    · left
      refine ⟨?_, hx1⟩
      by_contra h
      push Not at h
      have : (x - 1) * ((x - 1 - s) * (x - 1 + s)) < 0 := by
        have : 0 < (x - 1 - s) * (x - 1 + s) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
        exact mul_neg_of_neg_of_pos (by linarith) this
      linarith
    · right
      refine ⟨?_, hxγ⟩
      by_contra h
      push Not at h
      have : (x - 1) * ((x - 1 - s) * (x - 1 + s)) < 0 := by
        have : (x - 1 - s) * (x - 1 + s) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
        exact mul_neg_of_pos_of_neg (by linarith) this
      linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · constructor
      · have := hlow x
        have : 0 ≤ (x - 1) * ((x - 1 - s) * (x - 1 + s)) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith)
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
        linarith
      · have := hup x
        have : (x - γ) * ((x + (γ - 3) / 2) ^ 2 + 3 * (γ - 3) * (γ + 1) / 4) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (hQ x).le
        linarith
    · constructor
      · have := hlow x
        have : 0 ≤ (x - 1) * ((x - 1 - s) * (x - 1 + s)) :=
          mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
        linarith
      · have := hup x
        have : (x - γ) * ((x + (γ - 3) / 2) ^ 2 + 3 * (γ - 3) * (γ + 1) / 4) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (hQ x).le
        linarith

end Chapter23

end
