/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib

/-!
# Hilbert's third problem: decomposing polyhedra (single-file version)

Formalization of Chapter 10 of *Proofs from THE BOOK*, collected into one file.
The parts appear in dependency order:

1. Cone Lemma
2. Fourier–Motzkin elimination (book proof of the Cone Lemma)
3. Pearl Lemma
4. Bricard's condition
5. Irrationality of `(1/π) arccos (1/√n)` (Chapter 8, Theorem 3)
6. Dihedral angles
7. Examples 1–3 and Hilbert's third problem
8. Appendix: polytopes and polyhedra
9. Geometric equidecomposability / equicomplementability
10. Minkowski–Weyl (convex polytopes = bounded H-polytopes)
-/

@[expose] public section

/-! ## Part 1: `ConeLemma` -/

section Part_ConeLemma


/-!
# The Cone Lemma

*If a system of homogeneous linear equations with integer coefficients has a positive real
solution, then it also has a positive integer solution.*
-/

open Finset

namespace Chapter10

/-- Rational step: a positive real solution of an integral homogeneous system yields a positive
rational solution. -/
theorem exists_pos_rat_solution {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ)
    (x : n → ℝ) (hx : ∀ j, 0 < x j) (hAx : ∀ i, ∑ j, (A i j : ℝ) * x j = 0) :
    ∃ q : n → ℚ, (∀ j, 0 < q j) ∧ ∀ i, ∑ j, (A i j : ℚ) * q j = 0 := by
  classical
  set V : Submodule ℚ ℝ := Submodule.span ℚ (Set.range x)
  have : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  let b := Module.finBasis ℚ V
  let xV : n → V := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  let r : n → Fin (Module.finrank ℚ V) → ℚ := fun j l => b.repr (xV j) l
  -- expansion of `x` in the basis
  have hxr : ∀ j, x j = ∑ l, (r j l : ℝ) * (b l : ℝ) := by
    intro j
    have := congrArg (fun v : V => (v : ℝ)) (b.sum_repr (xV j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    change _ = x j at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [r, Rat.smul_def]
  -- each coordinate column is a rational solution
  have hker : ∀ i l, ∑ j, (A i j : ℚ) * r j l = 0 := by
    intro i l
    have h0 : ∑ j, (A i j : ℚ) • xV j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, xV, Rat.smul_def,
        Rat.cast_intCast]
      exact hAx i
    have := congrArg (fun v => b.repr v l) h0
    simpa [map_sum, r, Finsupp.coe_finsetSum, Finset.sum_apply] using this
  -- approximate the real basis vectors by rationals
  let f : (Fin (Module.finrank ℚ V) → ℝ) → n → ℝ := fun t j => ∑ l, (r j l : ℝ) * t l
  have hf : Continuous f := by
    apply continuous_pi; intro j
    exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)
  let U : Set (Fin (Module.finrank ℚ V) → ℝ) := f ⁻¹' {y | ∀ j, 0 < y j}
  have hU : IsOpen U := by
    apply hf.isOpen_preimage
    have : {y : n → ℝ | ∀ j, 0 < y j} = ⋂ j, {y | 0 < y j} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)
  have hbU : (fun l => (b l : ℝ)) ∈ U := by
    intro j; simp only [f]; rw [← hxr]; exact hx j
  have hdense : DenseRange (Pi.map fun (_ : Fin (Module.finrank ℚ V)) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨t, ht⟩ := hdense.exists_mem_open hU ⟨_, hbU⟩
  refine ⟨fun j => ∑ l, r j l * t l, fun j => ?_, fun i => ?_⟩
  · have := ht j
    simp only [f, Pi.map_apply] at this
    exact_mod_cast this
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := hker i l
    calc ∑ j, (A i j : ℚ) * (r j l * t l) = (∑ j, (A i j : ℚ) * r j l) * t l := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, zero_mul]

/-- Integral step: clearing denominators. -/
theorem exists_pos_int_of_pos_rat {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ)
    (q : n → ℚ) (hq : ∀ j, 0 < q j) (hAq : ∀ i, ∑ j, (A i j : ℚ) * q j = 0) :
    ∃ z : n → ℕ, (∀ j, 0 < z j) ∧ ∀ i, ∑ j, A i j * (z j : ℤ) = 0 := by
  classical
  set d : ℕ := ∏ j, (q j).den
  have hd : 0 < d := Finset.prod_pos fun j _ => (q j).den_pos
  -- `q j * d` is a positive integer
  have hint : ∀ j, ∃ z : ℕ, 0 < z ∧ ((z : ℚ) = q j * d) := by
    intro j
    obtain ⟨c, hc⟩ : (q j).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hnum : 0 < (q j).num := Rat.num_pos.mpr (hq j)
    refine ⟨((q j).num * c).toNat, ?_, ?_⟩
    · have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · simp [h] at hc; omega
        · exact h
      have : 0 < (q j).num * (c : ℤ) := mul_pos hnum (by exact_mod_cast hc0)
      omega
    · have h1 : (0 : ℤ) ≤ (q j).num * c := by positivity
      have : ((((q j).num * c).toNat : ℤ) : ℚ) = q j * d := by
        rw [Int.toNat_of_nonneg h1, hc]
        push_cast
        rw [← mul_assoc, Rat.mul_den_eq_num]
      exact_mod_cast this
  choose z hz0 hz using hint
  refine ⟨z, hz0, fun i => ?_⟩
  have : ((∑ j, A i j * (z j : ℤ) : ℤ) : ℚ) = 0 := by
    push_cast
    simp_rw [hz, ← mul_assoc, ← Finset.sum_mul, hAq i, zero_mul]
  exact_mod_cast this

/-- **The Cone Lemma.** If a system of homogeneous linear equations with integer coefficients
has a positive real solution, then it also has a positive integer solution. -/
theorem cone_lemma {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ)
    (x : n → ℝ) (hx : ∀ j, 0 < x j) (hAx : ∀ i, ∑ j, (A i j : ℝ) * x j = 0) :
    ∃ z : n → ℕ, (∀ j, 0 < z j) ∧ ∀ i, ∑ j, A i j * (z j : ℤ) = 0 := by
  obtain ⟨q, hq, hAq⟩ := exists_pos_rat_solution A x hx hAx
  exact exists_pos_int_of_pos_rat A q hq hAq

end Chapter10

end Part_ConeLemma

/-! ## Part 2: `FourierMotzkin` -/

section Part_FourierMotzkin


/-!
# Fourier–Motzkin elimination and the book's proof of the Cone Lemma

The book proves the Cone Lemma by "Fourier–Motzkin elimination": *any system of the type
`Ax ≥ b, x ≥ 1` with rational (in the book: integral) `A` and `b` has a lexicographically smallest
solution, which is rational, provided that the system has any real solution at all.*

The proof is by induction on the number `N` of variables: the inequalities involving `x_N` give
lower bounds on `x_N` (among them `x_N ≥ 1`) and possibly also upper bounds. The new system in
`N - 1` variables consists of the inequalities not involving `x_N` together with the inequalities
requiring that all upper bounds on `x_N` are at least all lower bounds. By induction it has a
lexicographically minimal solution `x'*`, which is rational, and the smallest `x_N` compatible
with `x'*` is the largest of the lower bounds, which is rational as well.
-/

open Finset

namespace Chapter10

open Classical

/-- `x` is a (real) solution of the system `Ax ≥ b, x ≥ 1` (rows indexed by `ι`, `N` variables). -/
def IsFMSol {ι : Type} {N : ℕ} (A : ι → Fin N → ℚ) (b : ι → ℚ) (x : Fin N → ℝ) : Prop :=
  (∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) ∧ ∀ j, 1 ≤ x j

/-- The lexicographic order on `ℝᴺ` (the first coordinate is the most significant one). -/
def LexLE : {N : ℕ} → (Fin N → ℝ) → (Fin N → ℝ) → Prop
  | 0, _, _ => True
  | N + 1, x, y => LexLE (Fin.init x) (Fin.init y) ∧
      (Fin.init x = Fin.init y → x (Fin.last N) ≤ y (Fin.last N))

/-- `LexLE` is the usual lexicographic order: `x ≤ y` iff `x = y` or `x` and `y` agree up to
some coordinate `i` where `xᵢ < yᵢ`. -/
theorem lexLE_iff : ∀ {N : ℕ} (x y : Fin N → ℝ),
    LexLE x y ↔ x = y ∨ ∃ i, (∀ j < i, x j = y j) ∧ x i < y i
  | 0, x, y => by simp only [LexLE, true_iff]; left; ext j; exact j.elim0
  | N + 1, x, y => by
    rw [LexLE, lexLE_iff (Fin.init x) (Fin.init y)]
    constructor
    · rintro ⟨h | ⟨i, hi, hlt⟩, hlast⟩
      · rcases (hlast h).lt_or_eq with hl | hl
        · right
          refine ⟨Fin.last N, fun j hj => ?_, hl⟩
          obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
          exact congrFun h j'
        · left
          rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, h, hl]
      · right
        refine ⟨i.castSucc, fun j hj => ?_, hlt⟩
        obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
        exact hi j' (Fin.castSucc_lt_castSucc_iff.1 hj)
    · rintro (rfl | ⟨i, hi, hlt⟩)
      · exact ⟨Or.inl rfl, fun _ => le_rfl⟩
      · have hinit : ∀ j : Fin N, j.castSucc < i → Fin.init x j = Fin.init y j :=
          fun j hj => hi _ hj
        induction i using Fin.lastCases with
        | last =>
          have h : Fin.init x = Fin.init y := funext fun j => hinit j (Fin.castSucc_lt_last j)
          exact ⟨Or.inl h, fun _ => hlt.le⟩
        | cast i =>
          refine ⟨Or.inr ⟨i, fun j hj => hinit j (Fin.castSucc_lt_castSucc_iff.2 hj), hlt⟩,
            fun h => ?_⟩
          exact absurd (congrFun h i) (ne_of_lt hlt)

section elim

variable {ι : Type} {N : ℕ} (A : ι → Fin (N + 1) → ℚ) (b : ι → ℚ)

/-- Rows of the eliminated system: the rows not involving `x_N`, one row for each pair
(lower bound, upper bound) on `x_N`, and one row for each upper bound (compared with the lower
bound `x_N ≥ 1`). -/
def ElimIdx : Type :=
  {i // A i (Fin.last N) = 0} ⊕ ({i // 0 < A i (Fin.last N)} × {i // A i (Fin.last N) < 0}) ⊕
    {i // A i (Fin.last N) < 0}

noncomputable instance [Fintype ι] : Fintype (ElimIdx A) := by
  unfold ElimIdx; infer_instance

/-- Coefficients of the eliminated system. -/
def elimA : ElimIdx A → Fin N → ℚ
  | .inl i => fun j => A i.1 j.castSucc
  | .inr (.inl (i, k)) => fun j =>
      A i.1 j.castSucc / A i.1 (Fin.last N) - A k.1 j.castSucc / A k.1 (Fin.last N)
  | .inr (.inr k) => fun j => A k.1 j.castSucc

/-- Right-hand sides of the eliminated system. -/
def elimB : ElimIdx A → ℚ
  | .inl i => b i.1
  | .inr (.inl (i, k)) => b i.1 / A i.1 (Fin.last N) - b k.1 / A k.1 (Fin.last N)
  | .inr (.inr k) => b k.1 - A k.1 (Fin.last N)

/-- The partial sum `∑_{j < N} a_{ij} x_j`. -/
noncomputable def rowSum (i : ι) (x' : Fin N → ℝ) : ℝ := ∑ j : Fin N, (A i j.castSucc : ℝ) * x' j

/-- The bound on `x_N` given by row `i`: `(bᵢ - ∑_{j<N} a_{ij} x_j) / a_{iN}`. -/
noncomputable def bound (i : ι) (x' : Fin N → ℝ) : ℝ :=
  ((b i : ℝ) - rowSum A i x') / (A i (Fin.last N) : ℝ)

lemma sum_snoc (i : ι) (x' : Fin N → ℝ) (t : ℝ) :
    ∑ j, (A i j : ℝ) * (Fin.snoc x' t : Fin (N + 1) → ℝ) j =
      rowSum A i x' + (A i (Fin.last N) : ℝ) * t := by
  rw [Fin.sum_univ_castSucc]
  simp [rowSum, Fin.snoc_castSucc, Fin.snoc_last]

lemma row_pos_iff {i : ι} (hi : 0 < A i (Fin.last N)) (x' : Fin N → ℝ) (t : ℝ) :
    (b i : ℝ) ≤ rowSum A i x' + (A i (Fin.last N) : ℝ) * t ↔ bound A b i x' ≤ t := by
  have hc : (0 : ℝ) < A i (Fin.last N) := by exact_mod_cast hi
  rw [bound, div_le_iff₀ hc]
  constructor <;> intro h <;> linarith

lemma row_neg_iff {i : ι} (hi : A i (Fin.last N) < 0) (x' : Fin N → ℝ) (t : ℝ) :
    (b i : ℝ) ≤ rowSum A i x' + (A i (Fin.last N) : ℝ) * t ↔ t ≤ bound A b i x' := by
  have hc : (A i (Fin.last N) : ℝ) < 0 := by exact_mod_cast hi
  rw [bound, le_div_iff_of_neg hc]
  constructor <;> intro h <;> linarith

lemma elim_row (r : ElimIdx A) (x' : Fin N → ℝ) :
    ((elimB A b r : ℚ) : ℝ) ≤ ∑ j, (elimA A r j : ℝ) * x' j ↔
      match r with
      | .inl i => (b i.1 : ℝ) ≤ rowSum A i.1 x'
      | .inr (.inl (i, k)) => bound A b i.1 x' ≤ bound A b k.1 x'
      | .inr (.inr k) => 1 ≤ bound A b k.1 x' := by
  rcases r with i | ⟨i, k⟩ | k
  · simp [elimA, elimB, rowSum]
  · have hi : (0 : ℝ) < A i.1 (Fin.last N) := by exact_mod_cast i.2
    have hk : (A k.1 (Fin.last N) : ℝ) < 0 := by exact_mod_cast k.2
    have hsum : ∑ j, (elimA A (.inr (.inl (i, k))) j : ℝ) * x' j =
        rowSum A i.1 x' / A i.1 (Fin.last N) - rowSum A k.1 x' / A k.1 (Fin.last N) := by
      simp only [elimA, rowSum, Rat.cast_sub, Rat.cast_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    simp only [elimB, bound, Rat.cast_sub, Rat.cast_div, sub_div]
    constructor <;> intro h <;> linarith
  · have hk : (A k.1 (Fin.last N) : ℝ) < 0 := by exact_mod_cast k.2
    simp only [elimA, elimB, Rat.cast_sub, bound]
    rw [le_div_iff_of_neg hk, one_mul]
    change _ ≤ rowSum A k.1 x' ↔ _
    constructor <;> intro h <;> linarith

/-- The smallest value of `x_N` compatible with `x'`: the largest lower bound. -/
noncomputable def lowestLast [Fintype ι] (x' : Fin N → ℝ) : ℝ :=
  (insert 1 ((univ : Finset {i // 0 < A i (Fin.last N)}).image fun i => bound A b i.1 x')).max'
    (Finset.insert_nonempty _ _)

variable [Fintype ι]

omit [Fintype ι] in
/-- Projection: a solution of the original system yields a solution of the eliminated one. -/
lemma isFMSol_elim {x : Fin (N + 1) → ℝ} (hx : IsFMSol A b x) :
    IsFMSol (elimA A) (elimB A b) (Fin.init x) := by
  have hx' : IsFMSol A b (Fin.snoc (Fin.init x) (x (Fin.last N))) := by
    rwa [Fin.snoc_init_self]
  obtain ⟨hrow, hone⟩ := hx'
  set t := x (Fin.last N)
  have hrow' : ∀ i, (b i : ℝ) ≤ rowSum A i (Fin.init x) + (A i (Fin.last N) : ℝ) * t := by
    intro i; rw [← sum_snoc]; exact hrow i
  have ht1 : 1 ≤ t := by simpa using hone (Fin.last N)
  refine ⟨fun r => (elim_row A b r _).2 ?_, fun j => by simpa using hone j.castSucc⟩
  rcases r with i | ⟨i, k⟩ | k
  · simpa [i.2] using hrow' i.1
  · exact ((row_pos_iff A b i.2 _ t).1 (hrow' i.1)).trans ((row_neg_iff A b k.2 _ t).1 (hrow' k.1))
  · exact ht1.trans ((row_neg_iff A b k.2 _ t).1 (hrow' k.1))

lemma one_le_lowestLast (x' : Fin N → ℝ) : 1 ≤ lowestLast A b x' :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma bound_le_lowestLast (x' : Fin N → ℝ) (i : {i // 0 < A i (Fin.last N)}) :
    bound A b i.1 x' ≤ lowestLast A b x' :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem
    (fun i : {i // 0 < A i (Fin.last N)} => bound A b i.1 x') (Finset.mem_univ i)))

lemma lowestLast_eq (x' : Fin N → ℝ) : lowestLast A b x' = 1 ∨
    ∃ i : {i // 0 < A i (Fin.last N)}, lowestLast A b x' = bound A b i.1 x' := by
  have hTmem := Finset.max'_mem (insert 1 ((univ : Finset {i // 0 < A i (Fin.last N)}).image
    fun i => bound A b i.1 x')) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 hTmem with h | h
  · exact Or.inl h
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨i, hi.symm⟩

lemma lowestLast_le (x' : Fin N → ℝ) (t : ℝ) (h1 : 1 ≤ t)
    (h : ∀ i : {i // 0 < A i (Fin.last N)}, bound A b i.1 x' ≤ t) : lowestLast A b x' ≤ t := by
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.1 hy with hy | hy
  · rw [hy]; exact h1
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact h i

lemma snoc_apply_castSucc {N : ℕ} (x' : Fin N → ℝ) (t : ℝ) (j : Fin N) :
    (Fin.snoc x' t : Fin (N + 1) → ℝ) j.castSucc = x' j := Fin.snoc_castSucc ..

lemma snoc_apply_last {N : ℕ} (x' : Fin N → ℝ) (t : ℝ) :
    (Fin.snoc x' t : Fin (N + 1) → ℝ) (Fin.last N) = t := Fin.snoc_last ..

lemma one_le_snoc {N : ℕ} {x' : Fin N → ℝ} {t : ℝ} (h' : ∀ j, 1 ≤ x' j) (ht : 1 ≤ t) :
    ∀ j, 1 ≤ (Fin.snoc x' t : Fin (N + 1) → ℝ) j := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [snoc_apply_last]; exact ht
  · rw [snoc_apply_castSucc]; exact h' j

/-- Lifting: a solution `x'` of the eliminated system extends to a solution of the original
system by the largest lower bound, and this is the smallest possible value of `x_N`. -/
lemma isFMSol_snoc_lowestLast {x' : Fin N → ℝ} (hx' : IsFMSol (elimA A) (elimB A b) x') :
    IsFMSol A b (Fin.snoc x' (lowestLast A b x')) ∧
      ∀ t, IsFMSol A b (Fin.snoc x' t) → lowestLast A b x' ≤ t := by
  obtain ⟨hrow, hone⟩ := hx'
  have hrow' := fun r => (elim_row A b r x').1 (hrow r)
  -- the largest lower bound is below every upper bound
  have hTU : ∀ k : {i // A i (Fin.last N) < 0}, lowestLast A b x' ≤ bound A b k.1 x' := by
    intro k
    rcases lowestLast_eq A b x' with h | ⟨i, h⟩
    · rw [h]; exact hrow' (.inr (.inr k))
    · rw [h]; exact hrow' (.inr (.inl (i, k)))
  refine ⟨⟨fun i => ?_, one_le_snoc hone (one_le_lowestLast A b x')⟩, fun t ht => ?_⟩
  · rw [sum_snoc]
    rcases lt_trichotomy (A i (Fin.last N)) 0 with h | h | h
    · exact (row_neg_iff A b h _ _).2 (hTU ⟨i, h⟩)
    · have := hrow' (.inl ⟨i, h⟩)
      rw [h, Rat.cast_zero, zero_mul, add_zero]
      exact this
    · exact (row_pos_iff A b h _ _).2 (bound_le_lowestLast A b x' ⟨i, h⟩)
  · obtain ⟨hrowt, honet⟩ := ht
    refine lowestLast_le A b x' t ?_ fun i => ?_
    · have := honet (Fin.last N); rwa [snoc_apply_last] at this
    · have := hrowt i.1
      rw [sum_snoc] at this
      exact (row_pos_iff A b i.2 _ _).1 this

/-- The largest lower bound is rational if `x'` is. -/
lemma lowestLast_rat (q' : Fin N → ℚ) :
    ∃ t : ℚ, (t : ℝ) = lowestLast A b (fun j => (q' j : ℝ)) := by
  have hTmem := Finset.max'_mem (insert 1 ((univ : Finset {i // 0 < A i (Fin.last N)}).image
    fun i => bound A b i.1 (fun j => (q' j : ℝ)))) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 hTmem with h | h
  · exact ⟨1, by rw [Rat.cast_one]; exact h.symm⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    refine ⟨(b i.1 - ∑ j : Fin N, A i.1 j.castSucc * q' j) / A i.1 (Fin.last N), ?_⟩
    rw [show lowestLast A b (fun j => (q' j : ℝ)) = _ from hi.symm]
    simp [bound, rowSum]

end elim

lemma cast_snoc {N : ℕ} (q' : Fin N → ℚ) (t : ℚ) :
    (fun j => ((Fin.snoc q' t : Fin (N + 1) → ℚ) j : ℝ)) =
      (Fin.snoc (fun j => (q' j : ℝ)) (t : ℝ) : Fin (N + 1) → ℝ) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

/-- **Fourier–Motzkin.** If the system `Ax ≥ b, x ≥ 1` (with rational coefficients) has a real
solution, then it has a lexicographically smallest solution, and this solution is rational. -/
theorem exists_rat_lexMin_isFMSol : ∀ (N : ℕ) {ι : Type} [Fintype ι] (A : ι → Fin N → ℚ)
    (b : ι → ℚ), (∃ x, IsFMSol A b x) →
    ∃ q : Fin N → ℚ, IsFMSol A b (fun j => (q j : ℝ)) ∧
      ∀ y, IsFMSol A b y → LexLE (fun j => (q j : ℝ)) y := by
  intro N
  induction N with
  | zero =>
    intro ι _ A b ⟨x, hx⟩
    refine ⟨Fin.elim0, ⟨fun i => ?_, fun j => j.elim0⟩, fun y _ => trivial⟩
    simpa using hx.1 i
  | succ N ih =>
    intro ι _ A b ⟨x, hx⟩
    obtain ⟨q', hq', hmin⟩ := ih (elimA A) (elimB A b) ⟨_, isFMSol_elim A b hx⟩
    obtain ⟨t, ht⟩ := lowestLast_rat A b q'
    have hlift := isFMSol_snoc_lowestLast A b hq'
    refine ⟨Fin.snoc q' t, ?_, fun y hy => ?_⟩
    · rw [cast_snoc, ht]; exact hlift.1
    · rw [cast_snoc]
      refine ⟨?_, fun heq => ?_⟩
      · rw [Fin.init_snoc]; exact hmin _ (isFMSol_elim A b hy)
      · rw [Fin.init_snoc] at heq
        rw [Fin.snoc_last, ht]
        apply hlift.2
        rw [heq, Fin.snoc_init_self]; exact hy

/-- **The Cone Lemma**, following the proof in the book: if `Ax = 0` (with `A` integral) has a
positive real solution, then `C̄ = {x : Ax = 0, x ≥ 1}` is nonempty; the lexicographically
smallest point of `C̄` is rational; multiplying by a common denominator yields a positive integer
solution. -/
theorem cone_lemma_fourierMotzkin {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℤ)
    (x : n → ℝ) (hx : ∀ j, 0 < x j) (hAx : ∀ i, ∑ j, (A i j : ℝ) * x j = 0) :
    ∃ z : n → ℕ, (∀ j, 0 < z j) ∧ ∀ i, ∑ j, A i j * (z j : ℤ) = 0 := by
  -- `C̄` is nonempty: scale `x` so that all coordinates are at least `1`
  set c : ℝ := ∑ j, 1 / x j
  have hc : ∀ j, 1 ≤ c * x j := by
    intro j
    have : 1 / x j ≤ c := Finset.single_le_sum (f := fun j => 1 / x j)
      (fun j _ => (one_div_pos.2 (hx j)).le) (Finset.mem_univ j)
    calc (1 : ℝ) = 1 / x j * x j := by rw [one_div, inv_mul_cancel₀ (hx j).ne']
      _ ≤ c * x j := mul_le_mul_of_nonneg_right this (hx j).le
  -- the system `Ax ≥ 0, -Ax ≥ 0, x ≥ 1`, with variables indexed by `Fin (card n)`
  let e := Fintype.equivFin n
  let A' : m ⊕ m → Fin (Fintype.card n) → ℚ
    | .inl i => fun j => A i (e.symm j)
    | .inr i => fun j => -A i (e.symm j)
  have hsum : ∀ (i : m) (y : n → ℝ),
      ∑ j : Fin (Fintype.card n), ((A i (e.symm j) : ℚ) : ℝ) * y (e.symm j) =
        ∑ j, (A i j : ℝ) * y j := by
    intro i y
    rw [← e.symm.sum_comp (fun j => (A i j : ℝ) * y j)]
    simp
  have hsol : IsFMSol A' 0 (fun j => c * x (e.symm j)) := by
    refine ⟨fun r => ?_, fun j => hc _⟩
    rcases r with i | i
    · simp only [A', Pi.zero_apply, Rat.cast_zero]
      rw [hsum i (fun j => c * x j)]
      simp_rw [mul_left_comm _ c, ← Finset.mul_sum, hAx i, mul_zero, le_refl]
    · simp only [A', Pi.zero_apply, Rat.cast_zero, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
      rw [hsum i (fun j => c * x j)]
      simp_rw [mul_left_comm _ c, ← Finset.mul_sum, hAx i, mul_zero, neg_zero, le_refl]
  obtain ⟨q, hq, -⟩ := exists_rat_lexMin_isFMSol (Fintype.card n) A' 0 ⟨_, hsol⟩
  refine exists_pos_int_of_pos_rat A (fun j => q (e j)) (fun j => ?_) (fun i => ?_)
  · show 0 < q (e j)
    have : (1 : ℝ) ≤ q (e j) := hq.2 (e j)
    exact_mod_cast (zero_lt_one.trans_le this)
  · have h1 := hq.1 (.inl i)
    have h2 := hq.1 (.inr i)
    have key := hsum i (fun j => (q (e j) : ℝ))
    simp only [A', Pi.zero_apply, Rat.cast_zero, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib,
      Equiv.apply_symm_apply] at h1 h2 key
    have : (∑ j, (A i j : ℝ) * (q (e j) : ℝ)) = 0 := by linarith
    exact_mod_cast this

end Chapter10

end Part_FourierMotzkin

/-! ## Part 3: `PearlLemma` -/

section Part_PearlLemma


/-!
# Segments of a decomposition and the Pearl Lemma

We model the *segment structure* of a decomposition `P = P₁ ∪ ⋯ ∪ Pₙ` of a polyhedron
(or a polygon): every edge `e` of every piece `Pᵢ` is subdivided (by vertices or edges of other
pieces) into *segments*; the lengths of the segments of an edge add up to the length of the edge.
Similarly the segments lying on an edge `f` of the decomposed polyhedron `P` add up to the length
of `f`.

The **Pearl Lemma** says that if `P` and `Q` are equidecomposable, one can place a positive
number of pearls on every segment of both decompositions such that every edge of a piece `Pₖ`
receives the same number of pearls as the corresponding edge of the congruent piece `Qₖ`.
As in the book, it follows from the cone lemma, applied to the lengths of the segments.
We also prove the general form (`pearl_general`), which allows the "extra restrictions" used in the
proof of Bricard's condition for equicomplementable polyhedra.
-/

open Finset

open Classical in
/-- The segment structure of a decomposition of a polyhedron into pieces.

* `ι` indexes the pieces `Pᵢ`, and `E i` is the (finite) set of edges of the piece `Pᵢ`;
* `S` is the set of segments of the decomposition;
* `F` is the set of edges of the decomposed polyhedron `P`. -/
structure Chapter10.Segmentation (ι : Type) (E : ι → Type) (S : Type) (F : Type) [Fintype S] where
  /-- length of the edge `e` of the piece `Pᵢ` -/
  pieceLen : (i : ι) → E i → ℝ
  /-- length of the edge `f` of the decomposed polyhedron -/
  edgeLen : F → ℝ
  /-- length of a segment -/
  segLen : S → ℝ
  segLen_pos : ∀ s, 0 < segLen s
  pieceLen_pos : ∀ i e, 0 < pieceLen i e
  edgeLen_pos : ∀ f, 0 < edgeLen f
  /-- the segments into which the edge `e` of the piece `Pᵢ` is subdivided -/
  segs : (i : ι) → E i → Finset S
  /-- the segments of an edge of a piece add up to that edge -/
  sum_segs : ∀ i e, ∑ s ∈ segs i e, segLen s = pieceLen i e
  /-- the edge of the decomposed polyhedron on which a segment lies (if any) -/
  onEdge : S → Option F
  /-- the segments lying on an edge of the decomposed polyhedron add up to that edge -/
  sum_onEdge : ∀ f, ∑ s with onEdge s = some f, segLen s = edgeLen f

namespace Chapter10

open Classical

variable {ι : Type} {E : ι → Type} {S F : Type} [Fintype S]

lemma Segmentation.segs_nonempty (D : Segmentation ι E S F) (i : ι) (e : E i) :
    (D.segs i e).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have := D.sum_segs i e
  rw [h, Finset.sum_empty] at this
  exact (D.pieceLen_pos i e).ne this

lemma Segmentation.exists_onEdge (D : Segmentation ι E S F) (f : F) :
    ∃ s, D.onEdge s = some f := by
  by_contra h
  push Not at h
  have := D.sum_onEdge f
  rw [Finset.sum_eq_zero (fun s hs => by simp [h s] at hs)] at this
  exact (D.edgeLen_pos f).ne this

/-- **Pearl lemma, general form.** Consider finitely many conditions, each requiring that the
sum of some variables equals the sum of some other variables. If these conditions have a
positive real solution, then they have a positive integer solution. -/
theorem pearl_general {V C : Type} [Fintype V] [Fintype C] (L R : C → Finset V)
    (x : V → ℝ) (hx : ∀ v, 0 < x v) (h : ∀ c, ∑ v ∈ L c, x v = ∑ v ∈ R c, x v) :
    ∃ n : V → ℕ, (∀ v, 0 < n v) ∧ ∀ c, ∑ v ∈ L c, n v = ∑ v ∈ R c, n v := by
  let A : Matrix C V ℤ := fun c v => (if v ∈ L c then 1 else 0) - (if v ∈ R c then 1 else 0)
  have key : ∀ {K : Type} [CommRing K] (y : V → K) (c : C),
      ∑ v, ((A c v : ℤ) : K) * y v = ∑ v ∈ L c, y v - ∑ v ∈ R c, y v := by
    intro K _ y c
    simp only [A, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
  obtain ⟨n, hn, hAn⟩ := cone_lemma A x hx (fun c => by rw [key, h c, sub_self])
  refine ⟨n, hn, fun c => ?_⟩
  have := hAn c
  have h2 := key (fun v => (n v : ℤ)) c
  simp only [Int.cast_id] at h2
  rw [h2, sub_eq_zero] at this
  exact_mod_cast this

/-- **The Pearl Lemma.** If `P` and `Q` are equidecomposable, with decompositions into pieces
`Pᵢ` and `Qᵢ` such that corresponding pieces are congruent (in particular corresponding edges
have the same lengths), then one can place a positive number of pearls on every segment of both
decompositions such that each edge of a piece `Pᵢ` receives the same number of pearls as the
corresponding edge of `Qᵢ`. -/
theorem pearl_lemma [Fintype ι] [∀ i, Fintype (E i)] {S₁ S₂ F₁ F₂ : Type}
    [Fintype S₁] [Fintype S₂] (D₁ : Segmentation ι E S₁ F₁) (D₂ : Segmentation ι E S₂ F₂)
    (hlen : D₁.pieceLen = D₂.pieceLen) :
    ∃ (n₁ : S₁ → ℕ) (n₂ : S₂ → ℕ), (∀ s, 0 < n₁ s) ∧ (∀ s, 0 < n₂ s) ∧
      ∀ i e, ∑ s ∈ D₁.segs i e, n₁ s = ∑ s ∈ D₂.segs i e, n₂ s := by
  obtain ⟨n, hn, hc⟩ := pearl_general (V := S₁ ⊕ S₂) (C := Σ i, E i)
    (fun c => (D₁.segs c.1 c.2).map Function.Embedding.inl)
    (fun c => (D₂.segs c.1 c.2).map Function.Embedding.inr)
    (Sum.elim D₁.segLen D₂.segLen)
    (fun v => by cases v <;> simp [D₁.segLen_pos, D₂.segLen_pos])
    (fun c => by simp [D₁.sum_segs, D₂.sum_segs, hlen])
  refine ⟨n ∘ Sum.inl, n ∘ Sum.inr, fun s => hn _, fun s => hn _, fun i e => ?_⟩
  simpa using hc ⟨i, e⟩

end Chapter10

end Part_PearlLemma

/-! ## Part 4: `Bricard` -/

section Part_Bricard


/-!
# Bricard's condition

**Theorem ("Bricard's condition").** If three-dimensional polyhedra `P` and `Q` with dihedral
angles `α₁, …, α_r` resp. `β₁, …, β_s` are equidecomposable, then there are positive integers
`mᵢ`, `nⱼ` and an integer `k` with
`m₁ α₁ + ⋯ + m_r α_r = n₁ β₁ + ⋯ + n_s β_s + k π`.
The same holds more generally if `P` and `Q` are equicomplementable.

## The model

The proof in the book uses only the following information about a decomposition
`P = P₁ ∪ ⋯ ∪ Pₙ`:

* the segment structure (`Chapter10.Segmentation`): the edges of the pieces are subdivided into
  segments of positive length;
* the dihedral angles of the pieces at their edges, and the dihedral angles of `P` at its edges;
* the *local angle sum* at a segment `s`: adding up the dihedral angles of all piece edges
  containing `s` (all measured in the plane orthogonal to `s`) yields the dihedral angle `αⱼ`
  of `P` if `s` lies on the edge `j` of `P`, and an integer multiple of `π` otherwise (namely `π`
  if `s` lies in the boundary of `P` but not on an edge, and `π` or `2π` if `s` lies in the
  interior of `P`).

These are exactly the facts that the book takes for granted about decompositions of polyhedra;
they are recorded as the fields of the structure `Chapter10.Decomp`.  Congruent pieces are
modelled by identical edge data (same dihedral angles and same edge lengths at corresponding
edges).  A polyhedron enters the statement through its edges, with their dihedral angles and
lengths (`Chapter10.EdgeData`).
-/

open Finset Real

namespace Chapter10

open Classical

open Classical in
/-- A decomposition `P = P₁ ∪ ⋯ ∪ Pₙ` of a polyhedron, recorded through its segment structure,
the dihedral angles of the pieces and of `P`, and the local angle sums at the segments. -/
structure Decomp (ι : Type) (E : ι → Type) (S : Type) (F : Type)
    [Fintype ι] [∀ i, Fintype (E i)] [Fintype S] extends Segmentation ι E S F where
  /-- dihedral angle of the piece `Pᵢ` at its edge `e` -/
  pieceAngle : (i : ι) → E i → ℝ
  /-- dihedral angle of the decomposed polyhedron `P` at its edge `f` -/
  angle : F → ℝ
  /-- at a segment lying on an edge `f` of `P` the dihedral angles of the pieces add up to the
  dihedral angle of `P` at `f` -/
  angleSum_onEdge : ∀ s f, onEdge s = some f →
    ∑ c ∈ (univ : Finset (Σ i, E i)).filter (fun c => s ∈ segs c.1 c.2),
      pieceAngle c.1 c.2 = angle f
  /-- at any other segment the dihedral angles of the pieces add up to `π` or `2π`
  (or, more generally, to some nonnegative integer multiple of `π`) -/
  angleSum_other : ∀ s, onEdge s = none → ∃ k : ℕ,
    ∑ c ∈ (univ : Finset (Σ i, E i)).filter (fun c => s ∈ segs c.1 c.2),
      pieceAngle c.1 c.2 = k * π

/-- The edges of a polyhedron, with their dihedral angles and lengths. -/
structure EdgeData (F : Type) where
  /-- the dihedral angle at an edge -/
  angle : F → ℝ
  /-- the length of an edge -/
  len : F → ℝ

/-- Bricard's condition for two families of dihedral angles: there are positive integers `mᵢ`,
`nⱼ` and an integer `k` with `∑ mᵢ αᵢ = ∑ nⱼ βⱼ + k π`. -/
def BricardCondition {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂] (α : F₁ → ℝ) (β : F₂ → ℝ) :
    Prop :=
  ∃ (m : F₁ → ℕ) (n : F₂ → ℕ) (k : ℤ), (∀ f, 0 < m f) ∧ (∀ g, 0 < n g) ∧
    ∑ f, (m f : ℝ) * α f = ∑ g, (n g : ℝ) * β g + k * π

/-- `P` and `Q` are equidecomposable: they have decompositions into pieces `P₁, …, Pₙ` and
`Q₁, …, Qₙ` such that `Pᵢ` and `Qᵢ` are congruent for all `i`. -/
def Equidecomposable {F₁ F₂ : Type} (P : EdgeData F₁) (Q : EdgeData F₂) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (E : ι → Type) (_ : ∀ i, Fintype (E i))
    (S₁ S₂ : Type) (_ : Fintype S₁) (_ : Fintype S₂)
    (D₁ : Decomp ι E S₁ F₁) (D₂ : Decomp ι E S₂ F₂),
    D₁.angle = P.angle ∧ D₁.edgeLen = P.len ∧ D₂.angle = Q.angle ∧ D₂.edgeLen = Q.len ∧
    D₁.pieceAngle = D₂.pieceAngle ∧ D₁.pieceLen = D₂.pieceLen

/-- Edges of the pieces of `P̃ = P ∪ P'₁ ∪ ⋯ ∪ P'ₘ`: the piece `none` is `P` itself (with edge set
`F`), the piece `some i` is `P'ᵢ` (with edge set `E i`). -/
instance instFintypeOptionElim {ι F : Type} {E : ι → Type} [Fintype F] [∀ i, Fintype (E i)] :
    ∀ o : Option ι, Fintype (o.elim F E)
  | none => inferInstanceAs (Fintype F)
  | some i => inferInstanceAs (Fintype (E i))

/-- `P` and `Q` are equicomplementable: there are equidecomposable polyhedra
`P̃ = P''₁ ∪ ⋯ ∪ P''ₙ` and `Q̃ = Q''₁ ∪ ⋯ ∪ Q''ₙ` (with `P''ᵢ` congruent to `Q''ᵢ`) that also have
decompositions `P̃ = P ∪ P'₁ ∪ ⋯ ∪ P'ₘ` and `Q̃ = Q ∪ Q'₁ ∪ ⋯ ∪ Q'ₘ` with `P'ₖ` congruent to
`Q'ₖ` for all `k`. -/
def Equicomplementable {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂]
    (P : EdgeData F₁) (Q : EdgeData F₂) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (E : ι → Type) (_ : ∀ i, Fintype (E i))
    (κ : Type) (_ : Fintype κ) (E'' : κ → Type) (_ : ∀ i, Fintype (E'' i))
    (G₁ G₂ : Type) (_ : Fintype G₁) (_ : Fintype G₂) (S₁ S₂ T₁ T₂ : Type)
    (_ : Fintype S₁) (_ : Fintype S₂) (_ : Fintype T₁) (_ : Fintype T₂)
    (D₁ : Decomp (Option ι) (fun o => o.elim F₁ E) S₁ G₁)
    (D₂ : Decomp (Option ι) (fun o => o.elim F₂ E) S₂ G₂)
    (D₁'' : Decomp κ E'' T₁ G₁) (D₂'' : Decomp κ E'' T₂ G₂),
    -- the piece `none` of `P̃` is `P`, the piece `none` of `Q̃` is `Q`
    D₁.pieceAngle none = P.angle ∧ D₁.pieceLen none = P.len ∧
    D₂.pieceAngle none = Q.angle ∧ D₂.pieceLen none = Q.len ∧
    -- `P'ᵢ` is congruent to `Q'ᵢ`
    (∀ i (e : E i), D₁.pieceAngle (some i) e = D₂.pieceAngle (some i) e) ∧
    (∀ i (e : E i), D₁.pieceLen (some i) e = D₂.pieceLen (some i) e) ∧
    -- both decompositions of `P̃` (resp. `Q̃`) decompose the same polyhedron
    D₁''.angle = D₁.angle ∧ D₁''.edgeLen = D₁.edgeLen ∧
    D₂''.angle = D₂.angle ∧ D₂''.edgeLen = D₂.edgeLen ∧
    -- `P''ᵢ` is congruent to `Q''ᵢ`
    D₁''.pieceAngle = D₂''.pieceAngle ∧ D₁''.pieceLen = D₂''.pieceLen

section sums

variable {ι : Type} {E : ι → Type} {S F : Type} [Fintype ι] [∀ i, Fintype (E i)] [Fintype S]

/-- The sum of all dihedral angles at the segment `s`. -/
noncomputable def Decomp.angleAt (D : Decomp ι E S F) (s : S) : ℝ :=
  ∑ c ∈ (univ : Finset (Σ i, E i)).filter (fun c => s ∈ D.segs c.1 c.2), D.pieceAngle c.1 c.2

/-- The number of pearls on the edge `e` of the piece `Pᵢ`. -/
noncomputable def Decomp.piecePearls (D : Decomp ι E S F) (n : S → ℕ) (i : ι) (e : E i) : ℕ :=
  ∑ s ∈ D.segs i e, n s

/-- The number of pearls on the edge `f` of the decomposed polyhedron. -/
noncomputable def Decomp.edgePearls (D : Decomp ι E S F) (n : S → ℕ) (f : F) : ℕ :=
  ∑ s with D.onEdge s = some f, n s

/-- `Σ`: the sum of all the dihedral angles at all the pearls in the pieces of the
decomposition. -/
noncomputable def Decomp.pearlSum (D : Decomp ι E S F) (n : S → ℕ) : ℝ :=
  ∑ s, (n s : ℝ) * D.angleAt s

/-- Computing the angle sum piece by piece. -/
theorem Decomp.pearlSum_eq_pieces (D : Decomp ι E S F) (n : S → ℕ) :
    D.pearlSum n = ∑ c : Σ i, E i, D.pieceAngle c.1 c.2 * (D.piecePearls n c.1 c.2 : ℝ) := by
  simp only [pearlSum, angleAt, piecePearls, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Computing the angle sum segment by segment: we get the dihedral angles of the decomposed
polyhedron, each counted as often as there are pearls on the corresponding edge, plus a
nonnegative integer multiple of `π`. -/
theorem Decomp.pearlSum_eq_edges (D : Decomp ι E S F) [Fintype F] (n : S → ℕ) :
    ∃ K : ℕ, D.pearlSum n = ∑ f, D.angle f * (D.edgePearls n f : ℝ) + K * π := by
  have hk : ∀ s, ∃ k : ℕ, D.angleAt s = ((D.onEdge s).elim 0 D.angle) + k * π := by
    intro s
    cases h : D.onEdge s with
    | none =>
      obtain ⟨k, hk⟩ := D.angleSum_other s h
      exact ⟨k, by simp [angleAt, hk]⟩
    | some f => exact ⟨0, by simp [angleAt, D.angleSum_onEdge s f h]⟩
  choose k hk using hk
  refine ⟨∑ s, n s * k s, ?_⟩
  have h1 : ∑ f, D.angle f * (D.edgePearls n f : ℝ) =
      ∑ s, (n s : ℝ) * (D.onEdge s).elim 0 D.angle := by
    simp only [edgePearls, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    cases h : D.onEdge s with
    | none => simp
    | some f =>
      simp only [Option.some.injEq, Option.elim_some]
      simp [mul_comm]
  rw [h1, pearlSum]
  simp_rw [hk]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- An edge of the decomposed polyhedron carries at least one pearl. -/
theorem Decomp.edgePearls_pos (D : Decomp ι E S F) {n : S → ℕ} (hn : ∀ s, 0 < n s) (f : F) :
    0 < D.edgePearls n f := by
  obtain ⟨s, hs⟩ := D.exists_onEdge f
  exact Finset.sum_pos (fun s _ => hn s) ⟨s, by simp [hs]⟩

/-- An edge of a piece carries at least one pearl. -/
theorem Decomp.piecePearls_pos (D : Decomp ι E S F) {n : S → ℕ} (hn : ∀ s, 0 < n s)
    (i : ι) (e : E i) : 0 < D.piecePearls n i e :=
  Finset.sum_pos (fun s _ => hn s) (D.segs_nonempty i e)

end sums

/-- **Bricard's condition** for equidecomposable polyhedra. -/
theorem bricard_of_equidecomposable {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂]
    {P : EdgeData F₁} {Q : EdgeData F₂} (h : Equidecomposable P Q) :
    BricardCondition P.angle Q.angle := by
  obtain ⟨ι, _, E, _, S₁, S₂, _, _, D₁, D₂, hP, -, hQ, -, hang, hlen⟩ := h
  -- place pearls according to the pearl lemma
  obtain ⟨n₁, n₂, hn₁, hn₂, hpearl⟩ := pearl_lemma D₁.toSegmentation D₂.toSegmentation hlen
  -- `Σ₁ = Σ₂`, computed piece by piece
  have hSigma : D₁.pearlSum n₁ = D₂.pearlSum n₂ := by
    rw [D₁.pearlSum_eq_pieces, D₂.pearlSum_eq_pieces, hang]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Decomp.piecePearls]
    rw [hpearl c.1 c.2]
  -- `Σ₁` and `Σ₂` computed edge by edge
  obtain ⟨K₁, hK₁⟩ := D₁.pearlSum_eq_edges n₁
  obtain ⟨K₂, hK₂⟩ := D₂.pearlSum_eq_edges n₂
  refine ⟨D₁.edgePearls n₁, D₂.edgePearls n₂, (K₂ : ℤ) - K₁, D₁.edgePearls_pos hn₁,
    D₂.edgePearls_pos hn₂, ?_⟩
  rw [← hP, ← hQ]
  push_cast
  simp_rw [mul_comm (_ : ℝ) (D₁.angle _), mul_comm (_ : ℝ) (D₂.angle _)]
  linarith

/-- The trivial decomposition `P = P` of a polyhedron into the single piece `P` (and no
further pieces); every edge of `P` is a single segment. -/
noncomputable def Decomp.trivial {F : Type} [Fintype F] (P : EdgeData F)
    (hpos : ∀ f, 0 < P.len f) :
    Decomp (Option Empty) (fun o => o.elim F (fun _ => Empty)) F F where
  pieceLen o := match o with
    | none => P.len
    | some x => x.elim
  edgeLen := P.len
  segLen := P.len
  segLen_pos := hpos
  pieceLen_pos o := match o with
    | none => hpos
    | some x => x.elim
  edgeLen_pos := hpos
  segs o := match o with
    | none => fun f => {f}
    | some x => x.elim
  sum_segs o := match o with
    | none => fun f => by
        change (∑ s ∈ ({f} : Finset F), P.len s) = P.len f
        exact Finset.sum_singleton _ _
    | some x => x.elim
  onEdge := some
  sum_onEdge f := by
    rw [Finset.sum_eq_single f (fun b _ hb => by simp_all) (fun h => by simp at h)]
  pieceAngle o := match o with
    | none => P.angle
    | some x => x.elim
  angle := P.angle
  angleSum_onEdge s f h := by
    cases h
    rw [Finset.sum_eq_single (⟨none, s⟩ : Σ o : Option Empty, o.elim F fun _ => Empty)]
    · rintro ⟨o, e⟩ hc hne
      cases o with
      | none =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact absurd (by rw [Finset.mem_singleton.mp hc]) hne
      | some x => exact x.elim
    · intro h
      apply False.elim
      apply h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change s ∈ ({s} : Finset F)
      exact Finset.mem_singleton_self s
  angleSum_other s h := by simp at h

/-- Every polyhedron (with edges of positive length) is equidecomposable with itself, via the
trivial decomposition. In particular the notion `Equidecomposable` is not vacuous. -/
theorem Equidecomposable.refl {F : Type} [Fintype F] (P : EdgeData F) (hpos : ∀ f, 0 < P.len f) :
    Equidecomposable P P :=
  ⟨Option Empty, inferInstance, _, inferInstance, F, F, inferInstance, inferInstance,
    Decomp.trivial P hpos, Decomp.trivial P hpos, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Equidecomposable polyhedra are equicomplementable (the case `m = 0`). -/
theorem Equidecomposable.equicomplementable {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂]
    {P : EdgeData F₁} {Q : EdgeData F₂} (h : Equidecomposable P Q) :
    Equicomplementable P Q := by
  obtain ⟨ι, _, E, _, S₁, S₂, _, _, D₁, D₂, hPa, hPl, hQa, hQl, hang, hlen⟩ := h
  have hP : ∀ f, 0 < P.len f := fun f => hPl ▸ D₁.edgeLen_pos f
  have hQ : ∀ f, 0 < Q.len f := fun f => hQl ▸ D₂.edgeLen_pos f
  exact ⟨Empty, inferInstance, fun _ => Empty, inferInstance, ι, inferInstance, E, inferInstance,
    F₁, F₂, inferInstance, inferInstance, F₁, F₂, S₁, S₂, inferInstance, inferInstance,
    inferInstance, inferInstance, Decomp.trivial P hP, Decomp.trivial Q hQ, D₁, D₂,
    rfl, rfl, rfl, rfl, fun i => i.elim, fun i => i.elim, hPa, hPl, hQa, hQl, hang, hlen⟩

/-- **Bricard's condition** for equicomplementable polyhedra. -/
theorem bricard_of_equicomplementable {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂]
    {P : EdgeData F₁} {Q : EdgeData F₂} (h : Equicomplementable P Q) :
    BricardCondition P.angle Q.angle := by
  obtain ⟨ι, _, E, _, κ, _, E'', _, G₁, G₂, _, _, S₁, S₂, T₁, T₂, _, _, _, _, D₁, D₂, D₁'', D₂'',
    hPa, hPl, hQa, hQl, hca, hcl, h1a, h1l, h2a, h2l, h''a, h''l⟩ := h
  -- pearls on all four decompositions, with the extra restrictions on the edges of `P̃`, `Q̃`
  obtain ⟨n, hn, hc⟩ := pearl_general (V := (S₁ ⊕ S₂) ⊕ (T₁ ⊕ T₂))
    (C := (Σ i, E i) ⊕ (Σ i, E'' i) ⊕ G₁ ⊕ G₂)
    (fun c => match c with
      | .inl c => (D₁.segs (some c.1) c.2).map (.trans .inl .inl)
      | .inr (.inl c) => (D₁''.segs c.1 c.2).map (.trans .inl .inr)
      | .inr (.inr (.inl g)) => ({s | D₁.onEdge s = some g} : Finset S₁).map (.trans .inl .inl)
      | .inr (.inr (.inr g)) => ({s | D₂.onEdge s = some g} : Finset S₂).map (.trans .inr .inl))
    (fun c => match c with
      | .inl c => (D₂.segs (some c.1) c.2).map (.trans .inr .inl)
      | .inr (.inl c) => (D₂''.segs c.1 c.2).map (.trans .inr .inr)
      | .inr (.inr (.inl g)) => ({s | D₁''.onEdge s = some g} : Finset T₁).map (.trans .inl .inr)
      | .inr (.inr (.inr g)) => ({s | D₂''.onEdge s = some g} : Finset T₂).map (.trans .inr .inr))
    (Sum.elim (Sum.elim D₁.segLen D₂.segLen) (Sum.elim D₁''.segLen D₂''.segLen))
    (fun v => by
      rcases v with (v | v) | (v | v) <;>
        simp [D₁.segLen_pos, D₂.segLen_pos, D₁''.segLen_pos, D₂''.segLen_pos])
    (fun c => by
      rcases c with c | c | g | g
      · simp only [Finset.sum_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, Sum.elim_inl, Sum.elim_inr]
        exact (D₁.sum_segs (some c.1) c.2).trans
          ((hcl c.1 c.2).trans (D₂.sum_segs (some c.1) c.2).symm)
      · simp only [Finset.sum_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, Sum.elim_inl, Sum.elim_inr]
        rw [D₁''.sum_segs, D₂''.sum_segs, h''l]
      · simp only [Finset.sum_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, Sum.elim_inl, Sum.elim_inr]
        rw [D₁.sum_onEdge, D₁''.sum_onEdge, h1l]
      · simp only [Finset.sum_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply, Sum.elim_inl, Sum.elim_inr]
        rw [D₂.sum_onEdge, D₂''.sum_onEdge, h2l])
  set n₁ : S₁ → ℕ := fun s => n (.inl (.inl s))
  set n₂ : S₂ → ℕ := fun s => n (.inl (.inr s))
  set p₁ : T₁ → ℕ := fun s => n (.inr (.inl s))
  set p₂ : T₂ → ℕ := fun s => n (.inr (.inr s))
  have hcP : ∀ i (e : E i), D₁.piecePearls n₁ (some i) e = D₂.piecePearls n₂ (some i) e := by
    intro i e; simpa [Decomp.piecePearls] using hc (.inl ⟨i, e⟩)
  have hc'' : ∀ i (e : E'' i), D₁''.piecePearls p₁ i e = D₂''.piecePearls p₂ i e := by
    intro i e; simpa [Decomp.piecePearls] using hc (.inr (.inl ⟨i, e⟩))
  have hcG₁ : ∀ g, D₁.edgePearls n₁ g = D₁''.edgePearls p₁ g := by
    intro g; simpa [Decomp.edgePearls] using hc (.inr (.inr (.inl g)))
  have hcG₂ : ∀ g, D₂.edgePearls n₂ g = D₂''.edgePearls p₂ g := by
    intro g; simpa [Decomp.edgePearls] using hc (.inr (.inr (.inr g)))
  -- `Σ'₁ = Σ''₁ + ℓ₁ π` and `Σ'₂ = Σ''₂ + ℓ₂ π`
  obtain ⟨K₁, hK₁⟩ := D₁.pearlSum_eq_edges n₁
  obtain ⟨K₁'', hK₁''⟩ := D₁''.pearlSum_eq_edges p₁
  obtain ⟨K₂, hK₂⟩ := D₂.pearlSum_eq_edges n₂
  obtain ⟨K₂'', hK₂''⟩ := D₂''.pearlSum_eq_edges p₂
  have e1 : D₁.pearlSum n₁ - D₁''.pearlSum p₁ = ((K₁ : ℝ) - K₁'') * π := by
    rw [hK₁, hK₁'', h1a]; simp_rw [hcG₁]; ring
  have e2 : D₂.pearlSum n₂ - D₂''.pearlSum p₂ = ((K₂ : ℝ) - K₂'') * π := by
    rw [hK₂, hK₂'', h2a]; simp_rw [hcG₂]; ring
  -- `Σ''₁ = Σ''₂`
  have e3 : D₁''.pearlSum p₁ = D₂''.pearlSum p₂ := by
    rw [D₁''.pearlSum_eq_pieces, D₂''.pearlSum_eq_pieces, h''a]
    exact Finset.sum_congr rfl fun c _ => by rw [hc'' c.1 c.2]
  -- `Σ'₁` and `Σ'₂`, piece by piece: the contribution of `P` resp. `Q` plus equal contributions
  -- of the pieces `P'ᵢ` resp. `Q'ᵢ`
  have e4 : D₁.pearlSum n₁ = ∑ f, P.angle f * (D₁.piecePearls n₁ none f : ℝ) +
      ∑ i, ∑ e : E i, D₁.pieceAngle (some i) e * (D₁.piecePearls n₁ (some i) e : ℝ) := by
    rw [D₁.pearlSum_eq_pieces, Fintype.sum_sigma, Fintype.sum_option, ← hPa]
    rfl
  have e5 : D₂.pearlSum n₂ = ∑ f, Q.angle f * (D₂.piecePearls n₂ none f : ℝ) +
      ∑ i, ∑ e : E i, D₁.pieceAngle (some i) e * (D₁.piecePearls n₁ (some i) e : ℝ) := by
    rw [D₂.pearlSum_eq_pieces, Fintype.sum_sigma, Fintype.sum_option, ← hQa]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
    change D₂.pieceAngle (some i) (e : E i) *
        (D₂.piecePearls n₂ (some i) (e : E i) : ℝ) =
      D₁.pieceAngle (some i) (e : E i) * (D₁.piecePearls n₁ (some i) (e : E i) : ℝ)
    rw [hca i e, hcP i e]
  refine ⟨D₁.piecePearls n₁ none, D₂.piecePearls n₂ none, ((K₁ : ℤ) - K₁'') - (K₂ - K₂''),
    D₁.piecePearls_pos (fun s => hn _) none, D₂.piecePearls_pos (fun s => hn _) none, ?_⟩
  push_cast
  simp_rw [mul_comm (_ : ℝ) (P.angle _), mul_comm (_ : ℝ) (Q.angle _)]
  linarith

end Chapter10

end Part_Bricard

/-! ## Part 5: `Irrational` -/

section Part_Irrational


/-!
# Irrationality of `(1/π) arccos (1/√n)`

The examples of this chapter use the following result from Chapter 8 ("Some irrational numbers",
Theorem 3): *for every odd integer `n ≥ 3`, the number `(1/π) arccos (1/√n)` is irrational.*
We include its proof (following the book) to make the formalization self-contained.

Proof: with `φ = arccos (1/√n)` we have `cos (k φ) = A_k / √n ^ k`, where `A₀ = A₁ = 1` and
`A_{k+2} = 2 A_{k+1} - n A_k` (from `cos ((k+2)φ) + cos (k φ) = 2 cos φ cos ((k+1) φ)`).
Modulo `n` we get `A_{k+1} ≡ 2^k`, so `A_k` is coprime to `n`. If `φ = (a/b) π` with `b ≥ 1`, then
`cos (b φ) = ±1`, so `A_b² = n^b`, which is impossible since `n ≥ 3` is coprime to `A_b`.
-/

open Real

namespace Chapter10

/-- The integers `A_k` with `cos (k φ) = A_k / √n ^ k` for `cos φ = 1/√n`. -/
def cosNum (n : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | k + 2 => 2 * cosNum n (k + 1) - n * cosNum n k

lemma cos_mul_eq_cosNum (n : ℕ) (hn : 0 < n) (φ : ℝ) (hφ : cos φ = 1 / √n) (k : ℕ) :
    cos (k * φ) = cosNum n k / √n ^ k := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hss : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have key : ∀ k : ℕ, cos (k * φ) = cosNum n k / √n ^ k ∧
      cos ((k + 1 : ℕ) * φ) = cosNum n (k + 1) / √n ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [cosNum, hφ]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : cos (((k + 1 + 1 : ℕ) : ℝ) * φ) =
          2 * cos φ * cos (((k + 1 : ℕ) : ℝ) * φ) - cos ((k : ℝ) * φ) := by
        have ha : ((k + 1 + 1 : ℕ) : ℝ) * φ = ((k + 1 : ℕ) : ℝ) * φ + φ := by push_cast; ring
        have hb : (k : ℝ) * φ = ((k + 1 : ℕ) : ℝ) * φ - φ := by push_cast; ring
        rw [ha, hb, cos_add, cos_sub]; ring
      rw [h1, ih.1, ih.2, hφ]
      simp only [cosNum]
      push_cast
      field_simp
      rw [pow_succ, pow_succ, pow_succ]
      ring_nf
      rw [show √(n : ℝ) ^ 4 = (n : ℝ) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hss],
        hss]
      ring
  exact (key k).1

lemma cosNum_modEq (n : ℤ) (k : ℕ) : cosNum n (k + 1) ≡ 2 ^ k [ZMOD n] := by
  have key : ∀ k : ℕ, cosNum n (k + 1) ≡ 2 ^ k [ZMOD n] ∧ cosNum n (k + 2) ≡ 2 ^ (k + 1) [ZMOD n] := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [cosNum], ?_⟩
      simp only [cosNum]
      exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show 2 * cosNum n (k + 2) - n * cosNum n (k + 1) ≡ 2 ^ (k + 2) [ZMOD n]
      have h2 : 2 * cosNum n (k + 2) ≡ 2 * 2 ^ (k + 1) [ZMOD n] := ih.2.mul_left 2
      have h3 : n * cosNum n (k + 1) ≡ 0 [ZMOD n] :=
        (Int.modEq_zero_iff_dvd).mpr (dvd_mul_right _ _)
      have := h2.sub h3
      rw [sub_zero] at this
      convert this using 1; ring
  exact (key k).1

lemma isCoprime_cosNum (n : ℤ) (hn : Odd n) (k : ℕ) : IsCoprime (cosNum n k) n := by
  cases k with
  | zero => exact isCoprime_one_left
  | succ k =>
    have h2 : IsCoprime (2 ^ k : ℤ) n := by
      apply IsCoprime.pow_left
      obtain ⟨m, rfl⟩ := hn
      exact ⟨-m, 1, by ring⟩
    obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp (cosNum_modEq n k))
    have : cosNum n (k + 1) = 2 ^ k + n * (-t) := by linarith
    rw [this]
    exact h2.add_mul_left_left (-t)

/-- **Chapter 8, Theorem 3.** For every odd integer `n ≥ 3`, the number `(1/π) arccos (1/√n)`
is irrational. -/
theorem irrational_arccos_inv_sqrt_div_pi (n : ℕ) (hodd : Odd n) (h3 : 3 ≤ n) :
    Irrational (arccos (1 / √n) / π) := by
  rintro ⟨q, hq⟩
  set φ := arccos (1 / √n) with hφdef
  have hn : 0 < n := by omega
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs1 : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
  have hcos : cos φ = 1 / √n := by
    rw [hφdef, cos_arccos]
    · have : 0 < 1 / √(n : ℝ) := by positivity
      linarith
    · rw [div_le_one hs]; exact hs1
  -- `b φ = a π`
  have hb : (q.den : ℝ) * φ = q.num * π := by
    have := Rat.cast_def (K := ℝ) q
    rw [hq] at this
    field_simp at this
    linarith
  -- hence `cos (b φ) ^ 2 = 1`
  have hsq : cos ((q.den : ℕ) * φ) ^ 2 = 1 := by
    rw [hb, ← sin_sq_add_cos_sq ((q.num : ℝ) * π), sin_int_mul_pi]; ring
  rw [cos_mul_eq_cosNum n hn φ hcos, div_pow, ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by positivity), div_eq_one_iff_eq (by positivity)] at hsq
  have hint : (cosNum n q.den) ^ 2 = (n : ℤ) ^ q.den := by exact_mod_cast hsq
  -- `n ∣ A_b²`, but `A_b` is coprime to `n`
  have hdvd : (n : ℤ) ∣ (cosNum n q.den) ^ 2 := by
    rw [hint]; exact dvd_pow_self _ q.den_nz
  have hcop : IsCoprime ((cosNum n q.den) ^ 2) (n : ℤ) :=
    (isCoprime_cosNum n (by exact_mod_cast hodd.natCast) q.den).pow_left
  have hunit : IsUnit (n : ℤ) := hcop.isUnit_of_dvd' hdvd (dvd_refl _)
  rw [Int.isUnit_iff] at hunit
  omega

/-- `(1/π) arccos (1/3)` is irrational (the case `n = 9`). -/
theorem irrational_arccos_one_third_div_pi : Irrational (arccos (1 / 3) / π) := by
  have := irrational_arccos_inv_sqrt_div_pi 9 (by decide) (by norm_num)
  have h : √((9 : ℕ) : ℝ) = 3 := by
    rw [show ((9 : ℕ) : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h] at this

/-- `(1/π) arccos (1/√3)` is irrational (the case `n = 3`). -/
theorem irrational_arccos_inv_sqrt_three_div_pi : Irrational (arccos (1 / √3) / π) := by
  exact_mod_cast irrational_arccos_inv_sqrt_div_pi 3 (by decide) le_rfl

end Chapter10

end Part_Irrational

/-! ## Part 6: `DihedralAngle` -/

section Part_DihedralAngle


/-!
# Dihedral angles in `ℝ³`

The dihedral angle of a polyhedron at an edge `AB` is the angle between the two facets meeting
at `AB`, measured in a plane orthogonal to `AB`. If `C` and `D` are points of the two facets
(not on the line `AB`), it is the angle between the components of `C - A` and `D - A` that are
orthogonal to `B - A`.
-/

open Real InnerProductGeometry

namespace Chapter10

/-- Euclidean three-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The point `(x, y, z)` of `ℝ³`. -/
def pt (x y z : ℝ) : R3 := !₂[x, y, z]

/-- The component of `w` orthogonal to `v`. -/
noncomputable def orthTo (v w : R3) : R3 := w - (inner ℝ v w / inner ℝ v v) • v

/-- The dihedral angle at the edge `AB` between the half-planes spanned by `AB` and `C`,
resp. by `AB` and `D`. -/
noncomputable def dihedralAngle (A B C D : R3) : ℝ :=
  angle (orthTo (B - A) (C - A)) (orthTo (B - A) (D - A))

lemma inner_pt (a b c x y z : ℝ) :
    inner ℝ (pt a b c) (pt x y z) = a * x + b * y + c * z := by
  simp [pt, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]; ring

lemma pt_sub (a b c x y z : ℝ) : pt a b c - pt x y z = pt (a - x) (b - y) (c - z) := by
  ext i; fin_cases i <;> simp [pt]

lemma smul_pt (u x y z : ℝ) : u • pt x y z = pt (u * x) (u * y) (u * z) := by
  ext i; fin_cases i <;> simp [pt]

lemma dist_pt (a b c x y z : ℝ) :
    dist (pt a b c) (pt x y z) = √((a - x) ^ 2 + (b - y) ^ 2 + (c - z) ^ 2) := by
  rw [dist_eq_norm, norm_eq_sqrt_real_inner, pt_sub, inner_pt]; ring_nf

lemma inner_orthTo (v x y : R3) : inner ℝ (orthTo v x) (orthTo v y) =
    inner ℝ x y - inner ℝ v x * inner ℝ v y / inner ℝ v v := by
  unfold orthTo
  by_cases hv : v = 0
  · subst hv; simp
  · have hn : inner ℝ v v ≠ 0 := by simpa using hv
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm v x]
    field_simp
    ring

/-- A formula for the dihedral angle in terms of inner products. -/
lemma dihedralAngle_eq (A B C D : R3) : dihedralAngle A B C D =
    arccos ((inner ℝ (C - A) (D - A) -
        inner ℝ (B - A) (C - A) * inner ℝ (B - A) (D - A) / inner ℝ (B - A) (B - A)) /
      (√(inner ℝ (C - A) (C - A) - inner ℝ (B - A) (C - A) ^ 2 / inner ℝ (B - A) (B - A)) *
       √(inner ℝ (D - A) (D - A) - inner ℝ (B - A) (D - A) ^ 2 / inner ℝ (B - A) (B - A)))) := by
  unfold dihedralAngle angle
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_orthTo, inner_orthTo,
    inner_orthTo, sq, sq]

lemma orthTo_smul (c : ℝ) (hc : c ≠ 0) (v w : R3) : orthTo (c • v) (c • w) = c • orthTo v w := by
  unfold orthTo
  simp only [real_inner_smul_left, real_inner_smul_right, smul_sub, smul_smul]
  by_cases hv : v = 0
  · subst hv; simp
  · have hn : inner ℝ v v ≠ 0 := by simpa using hv
    congr 2
    field_simp

/-- Dihedral angles are invariant under scaling. -/
lemma dihedralAngle_smul (c : ℝ) (hc : c ≠ 0) (A B C D : R3) :
    dihedralAngle (c • A) (c • B) (c • C) (c • D) = dihedralAngle A B C D := by
  unfold dihedralAngle
  rw [← smul_sub, ← smul_sub, ← smul_sub, orthTo_smul c hc, orthTo_smul c hc]
  rcases lt_or_gt_of_ne hc with h | h
  · rw [angle_smul_smul hc]
  · rw [angle_smul_smul hc]

lemma arccos_inv_sqrt_two : arccos (1 / √2) = π / 4 := by
  rw [show (1 : ℝ) / √2 = √2 / 2 by
    field_simp; rw [Real.sq_sqrt (by norm_num)], ← cos_pi_div_four,
    arccos_cos (by positivity) (by linarith [pi_pos])]

lemma arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

end Chapter10

end Part_DihedralAngle

/-! ## Part 7: `Examples` -/

section Part_Examples


/-!
# Examples: the solution of Hilbert's third problem
-/

open Real

namespace Chapter10

/-! ### Edge data of tetrahedra and cubes -/

/-- The six dihedral angles of the tetrahedron `ABCD`, at the edges
`AB, AC, AD, BC, BD, CD` (in this order). -/
noncomputable def tetraAngles (A B C D : R3) : Fin 6 → ℝ :=
  ![dihedralAngle A B C D, dihedralAngle A C B D, dihedralAngle A D B C,
    dihedralAngle B C A D, dihedralAngle B D A C, dihedralAngle C D A B]

/-- The six edge lengths of the tetrahedron `ABCD`. -/
noncomputable def tetraLens (A B C D : R3) : Fin 6 → ℝ :=
  ![dist A B, dist A C, dist A D, dist B C, dist B D, dist C D]

/-- The edges of the tetrahedron `ABCD` with their dihedral angles and lengths. -/
noncomputable def tetra (A B C D : R3) : EdgeData (Fin 6) := ⟨tetraAngles A B C D, tetraLens A B C D⟩

/-- **Example 1.** The regular tetrahedron `T₀` (here with edge length `2√2 u`). -/
noncomputable def T₀ (u : ℝ) : EdgeData (Fin 6) :=
  tetra (u • pt 1 1 1) (u • pt 1 (-1) (-1)) (u • pt (-1) 1 (-1)) (u • pt (-1) (-1) 1)

/-- **Example 2.** The tetrahedron `T₁` spanned by three orthogonal edges `AB, AC, AD` of
length `u`. -/
noncomputable def T₁ (u : ℝ) : EdgeData (Fin 6) :=
  tetra (u • pt 0 0 0) (u • pt 1 0 0) (u • pt 0 1 0) (u • pt 0 0 1)

/-- **Example 3.** The orthoscheme `T₂`: three consecutive edges `AB, BC, CD` are mutually
orthogonal and of the same length `u`. -/
noncomputable def T₂ (u : ℝ) : EdgeData (Fin 6) :=
  tetra (u • pt 0 0 0) (u • pt 1 0 0) (u • pt 1 1 0) (u • pt 1 1 1)

/-- The edges of the cube `[0, u]³` are indexed by a direction (`Fin 3`) and the two other
coordinates (`Fin 2 × Fin 2`, standing for `0` or `u`). The dihedral angle at an edge is computed
from two adjacent vertices on the two facets containing it. -/
noncomputable def cubeAngle (u : ℝ) : Fin 3 × Fin 2 × Fin 2 → ℝ
  | (0, a, b) => dihedralAngle (u • pt 0 a b) (u • pt 1 a b) (u • pt 0 (1 - a) b) (u • pt 0 a (1 - b))
  | (1, a, b) => dihedralAngle (u • pt a 0 b) (u • pt a 1 b) (u • pt (1 - a) 0 b) (u • pt a 0 (1 - b))
  | (2, a, b) => dihedralAngle (u • pt a b 0) (u • pt a b 1) (u • pt (1 - a) b 0) (u • pt a (1 - b) 0)

/-- The cube `[0, u]³`: twelve edges of length `u`. -/
noncomputable def cube (u : ℝ) : EdgeData (Fin 3 × Fin 2 × Fin 2) := ⟨cubeAngle u, fun _ => u⟩

/-! ### Computing the dihedral angles -/

/-- In a cube, all dihedral angles are `π/2`. -/
theorem cube_angle (u : ℝ) (hu : u ≠ 0) (e) : (cube u).angle e = π / 2 := by
  obtain ⟨i, a, b⟩ := e
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [cube, cubeAngle, dihedralAngle_smul u hu, dihedralAngle_eq, pt_sub, inner_pt]

/-- A prism over an equilateral triangle (side length `1`, height `1`), with bottom vertices
`P₀, P₁, P₂` and top vertices `Q₀, Q₁, Q₂`: dihedral angles at the edges
`P₀P₁, P₁P₂, P₂P₀, Q₀Q₁, Q₁Q₂, Q₂Q₀, P₀Q₀, P₁Q₁, P₂Q₂`. -/
noncomputable def prismAngle : Fin 9 → ℝ :=
  let P₀ := pt 0 0 0; let P₁ := pt 1 0 0; let P₂ := pt (1 / 2) (√3 / 2) 0
  let Q₀ := pt 0 0 1; let Q₁ := pt 1 0 1; let Q₂ := pt (1 / 2) (√3 / 2) 1
  ![dihedralAngle P₀ P₁ P₂ Q₀, dihedralAngle P₁ P₂ P₀ Q₁, dihedralAngle P₂ P₀ P₁ Q₂,
    dihedralAngle Q₀ Q₁ Q₂ P₀, dihedralAngle Q₁ Q₂ Q₀ P₁, dihedralAngle Q₂ Q₀ Q₁ P₂,
    dihedralAngle P₀ Q₀ P₁ P₂, dihedralAngle P₁ Q₁ P₂ P₀, dihedralAngle P₂ Q₂ P₀ P₁]

/-- For a prism over an equilateral triangle, we get the dihedral angles `π/3` and `π/2`. -/
theorem prismAngle_eq :
    prismAngle = ![π / 2, π / 2, π / 2, π / 2, π / 2, π / 2, π / 3, π / 3, π / 3] := by
  ext e
  fin_cases e <;> simp only [prismAngle] <;> simp [dihedralAngle_eq, pt_sub, inner_pt]
  all_goals
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_pt, inner_pt]
    convert arccos_one_half using 2
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num

/-- **Example 1.** All dihedral angles of the regular tetrahedron are `arccos (1/3)`. -/
theorem T₀_angle (u : ℝ) (hu : u ≠ 0) (e) : (T₀ u).angle e = arccos (1 / 3) := by
  fin_cases e <;>
    (simp [T₀, tetra, tetraAngles, dihedralAngle_smul u hu]
     rw [dihedralAngle_eq]; simp only [pt_sub, inner_pt]; norm_num)

/-- **Example 2.** `T₁` has three right dihedral angles (at `AB, AC, AD`) and three dihedral
angles equal to `arccos (1/√3)` (at `BC, BD, CD`). -/
theorem T₁_angle (u : ℝ) (hu : u ≠ 0) :
    (T₁ u).angle = ![π / 2, π / 2, π / 2, arccos (1 / √3), arccos (1 / √3), arccos (1 / √3)] := by
  ext e
  fin_cases e <;>
    (simp [T₁, tetra, tetraAngles, dihedralAngle_smul u hu]
     rw [dihedralAngle_eq]; simp only [pt_sub, inner_pt]; norm_num)
  all_goals
    congr 1
    field_simp
    rw [Real.sq_sqrt (by norm_num)]

/-- **Example 3.** The dihedral angles of `T₂`: three of them equal `π/2` (at `AC, BC, BD`),
two of them equal `π/4` (at `AB, CD`), and one of them is `π/3` (at `AD`). -/
theorem T₂_angle (u : ℝ) (hu : u ≠ 0) :
    (T₂ u).angle = ![π / 4, π / 2, π / 3, π / 2, π / 2, π / 4] := by
  ext e
  fin_cases e <;>
    (simp [T₂, tetra, tetraAngles, dihedralAngle_smul u hu]
     rw [dihedralAngle_eq]; simp only [pt_sub, inner_pt]; norm_num)
  · rw [← one_div, arccos_inv_sqrt_two]
  · rw [show (1 : ℝ) / 3 / (√2 / √3 * (√2 / √3)) = 1 / 2 by
      field_simp; rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]]
    exact arccos_one_half
  · rw [← one_div, arccos_inv_sqrt_two]

/-! ### Bricard's condition fails for these examples -/

/-- Bricard's condition is symmetric. -/
theorem BricardCondition.symm {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂] {α : F₁ → ℝ}
    {β : F₂ → ℝ} (h : BricardCondition α β) : BricardCondition β α := by
  obtain ⟨m, n, k, hm, hn, h⟩ := h
  exact ⟨n, m, -k, hn, hm, by push_cast; linarith⟩

/-- If all dihedral angles of `P` and `Q` are of the form `a φ + q π` (with `a ∈ ℕ`, `q ∈ ℚ`), for
a fixed angle `φ` with `φ / π` irrational, and the `φ`-coefficients cannot be balanced by
positive integers, then Bricard's condition fails. -/
theorem not_bricardCondition {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂] {α : F₁ → ℝ}
    {β : F₂ → ℝ} (φ : ℝ) (hφ : Irrational (φ / π)) (a : F₁ → ℕ) (q : F₁ → ℚ)
    (b : F₂ → ℕ) (r : F₂ → ℚ) (hα : ∀ f, α f = a f * φ + q f * π)
    (hβ : ∀ g, β g = b g * φ + r g * π)
    (hab : ∀ (m : F₁ → ℕ) (n : F₂ → ℕ), (∀ f, 0 < m f) → (∀ g, 0 < n g) →
      ∑ f, m f * a f ≠ ∑ g, n g * b g) :
    ¬ BricardCondition α β := by
  rintro ⟨m, n, k, hm, hn, h⟩
  have hA : ∑ f, (m f : ℝ) * α f =
      ((∑ f, m f * a f : ℕ) : ℝ) * φ + ((∑ f, m f * q f : ℚ) : ℝ) * π := by
    simp_rw [hα]; push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun f _ => by ring
  have hB : ∑ g, (n g : ℝ) * β g =
      ((∑ g, n g * b g : ℕ) : ℝ) * φ + ((∑ g, n g * r g : ℚ) : ℝ) * π := by
    simp_rw [hβ]; push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hne := hab m n hm hn
  set A := ∑ f, m f * a f
  set B := ∑ g, n g * b g
  set Qs := ∑ f, m f * q f
  set Rs := ∑ g, n g * r g
  have hAB : ((A : ℝ) - B) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  apply hφ
  refine ⟨(Rs - Qs + k) / ((A : ℚ) - B), ?_⟩
  push_cast
  rw [div_eq_div_iff hAB pi_pos.ne']
  rw [hA, hB] at h
  linarith

/-- Equicomplementable polyhedra satisfy Bricard's condition in both orders; hence a failure of
Bricard's condition in either order rules out equicomplementability. -/
theorem not_equicomplementable_of_not_bricard {F₁ F₂ : Type} [Fintype F₁] [Fintype F₂]
    {P : EdgeData F₁} {Q : EdgeData F₂} (h : ¬ BricardCondition P.angle Q.angle) :
    (¬ Equicomplementable P Q ∧ ¬ Equidecomposable P Q) ∧
      (¬ Equicomplementable Q P ∧ ¬ Equidecomposable Q P) :=
  ⟨⟨fun hc => h (bricard_of_equicomplementable hc),
    fun hd => h (bricard_of_equicomplementable hd.equicomplementable)⟩,
   ⟨fun hc => h (bricard_of_equicomplementable hc).symm,
    fun hd => h (bricard_of_equicomplementable hd.equicomplementable).symm⟩⟩

/-- **Example 1.** A regular tetrahedron is neither equidecomposable nor equicomplementable with
a cube. -/
theorem T₀_cube (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬ BricardCondition (T₀ u).angle (cube v).angle ∧
      (¬ Equicomplementable (T₀ u) (cube v) ∧ ¬ Equidecomposable (T₀ u) (cube v)) ∧
      (¬ Equicomplementable (cube v) (T₀ u) ∧ ¬ Equidecomposable (cube v) (T₀ u)) := by
  have h : ¬ BricardCondition (T₀ u).angle (cube v).angle :=
    not_bricardCondition (arccos (1 / 3)) irrational_arccos_one_third_div_pi
      (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 1 / 2)
      (fun f => by simp [T₀_angle u hu]) (fun g => by rw [cube_angle v hv]; push_cast; ring)
      (fun m n hm _ => by
        simp only [mul_one, mul_zero, Finset.sum_const_zero]
        exact (Finset.sum_pos (fun f _ => hm f) Finset.univ_nonempty).ne')
  exact ⟨h, not_equicomplementable_of_not_bricard h⟩

/-- **Example 2.** The tetrahedron `T₁` is neither equidecomposable nor equicomplementable with
a cube. -/
theorem T₁_cube (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬ BricardCondition (T₁ u).angle (cube v).angle ∧
      (¬ Equicomplementable (T₁ u) (cube v) ∧ ¬ Equidecomposable (T₁ u) (cube v)) ∧
      (¬ Equicomplementable (cube v) (T₁ u) ∧ ¬ Equidecomposable (cube v) (T₁ u)) := by
  have h : ¬ BricardCondition (T₁ u).angle (cube v).angle :=
    not_bricardCondition (arccos (1 / √3)) irrational_arccos_inv_sqrt_three_div_pi
      ![0, 0, 0, 1, 1, 1] ![1 / 2, 1 / 2, 1 / 2, 0, 0, 0] (fun _ => 0) (fun _ => 1 / 2)
      (fun f => by rw [T₁_angle u hu]; fin_cases f <;> simp <;> ring)
      (fun g => by rw [cube_angle v hv]; push_cast; ring)
      (fun m n hm _ => by
        simp only [mul_zero, Finset.sum_const_zero]
        exact (Finset.sum_pos' (fun f _ => Nat.zero_le _) ⟨3, Finset.mem_univ _,
          by simpa using hm 3⟩).ne')
  exact ⟨h, not_equicomplementable_of_not_bricard h⟩

/-- **Example 3.** The orthoscheme `T₂` is neither equidecomposable nor equicomplementable with
the regular tetrahedron `T₀`. -/
theorem T₂_T₀ (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬ BricardCondition (T₂ u).angle (T₀ v).angle ∧
      (¬ Equicomplementable (T₂ u) (T₀ v) ∧ ¬ Equidecomposable (T₂ u) (T₀ v)) ∧
      (¬ Equicomplementable (T₀ v) (T₂ u) ∧ ¬ Equidecomposable (T₀ v) (T₂ u)) := by
  have h : ¬ BricardCondition (T₂ u).angle (T₀ v).angle :=
    not_bricardCondition (arccos (1 / 3)) irrational_arccos_one_third_div_pi
      (fun _ => 0) ![1 / 4, 1 / 2, 1 / 3, 1 / 2, 1 / 2, 1 / 4] (fun _ => 1) (fun _ => 0)
      (fun f => by rw [T₂_angle u hu]; fin_cases f <;> simp <;> ring)
      (fun g => by simp [T₀_angle v hv])
      (fun m n _ hn => by
        simp only [mul_one, mul_zero, Finset.sum_const_zero]
        exact (Finset.sum_pos (fun g _ => hn g) Finset.univ_nonempty).ne)
  exact ⟨h, not_equicomplementable_of_not_bricard h⟩

/-- **Example 3.** The orthoscheme `T₂` is neither equidecomposable nor equicomplementable with
the tetrahedron `T₁`. -/
theorem T₂_T₁ (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬ BricardCondition (T₂ u).angle (T₁ v).angle ∧
      (¬ Equicomplementable (T₂ u) (T₁ v) ∧ ¬ Equidecomposable (T₂ u) (T₁ v)) ∧
      (¬ Equicomplementable (T₁ v) (T₂ u) ∧ ¬ Equidecomposable (T₁ v) (T₂ u)) := by
  have h : ¬ BricardCondition (T₂ u).angle (T₁ v).angle :=
    not_bricardCondition (arccos (1 / √3)) irrational_arccos_inv_sqrt_three_div_pi
      (fun _ => 0) ![1 / 4, 1 / 2, 1 / 3, 1 / 2, 1 / 2, 1 / 4]
      ![0, 0, 0, 1, 1, 1] ![1 / 2, 1 / 2, 1 / 2, 0, 0, 0]
      (fun f => by rw [T₂_angle u hu]; fin_cases f <;> simp <;> ring)
      (fun g => by rw [T₁_angle v hv]; fin_cases g <;> simp <;> ring)
      (fun m n _ hn => by
        simp only [mul_zero, Finset.sum_const_zero]
        exact (Finset.sum_pos' (fun g _ => Nat.zero_le _) ⟨3, Finset.mem_univ _,
          by simpa using hn 3⟩).ne)
  exact ⟨h, not_equicomplementable_of_not_bricard h⟩

/-- **Hilbert's third problem.** The tetrahedra `T₁` and `T₂` have congruent bases (the
triangles `ABC`, which lie in the plane `z = 0` and have the same side lengths) and the same
height `u` (the apex `D` has `z`-coordinate `u` in both cases), but they are neither
equidecomposable nor equicomplementable. -/
theorem hilbert_third_problem (u : ℝ) (hu : 0 < u) :
    -- congruent bases: the base triangles have the same side lengths ...
    (dist (u • pt 0 0 0) (u • pt 1 0 0) = dist (u • pt 1 0 0) (u • pt 0 0 0) ∧
      dist (u • pt 0 0 0) (u • pt 0 1 0) = dist (u • pt 1 0 0) (u • pt 1 1 0) ∧
      dist (u • pt 1 0 0) (u • pt 0 1 0) = dist (u • pt 0 0 0) (u • pt 1 1 0)) ∧
    -- ... and lie in the plane `z = 0`
    ((u • pt 0 0 0) 2 = 0 ∧ (u • pt 1 0 0) 2 = 0 ∧ (u • pt 0 1 0) 2 = 0 ∧
      (u • pt 1 1 0) 2 = 0) ∧
    -- equal heights: both apexes lie at height `u` above the plane `z = 0`
    ((u • pt 0 0 1) 2 = u ∧ (u • pt 1 1 1) 2 = u) ∧
    -- but `T₁` and `T₂` are neither equicomplementable nor equidecomposable
    (¬ Equicomplementable (T₁ u) (T₂ u) ∧ ¬ Equidecomposable (T₁ u) (T₂ u)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (T₂_T₁ u u hu.ne' hu.ne').2.2⟩
  · rw [dist_comm]
  · simp only [smul_pt, dist_pt]; ring_nf
  · simp only [smul_pt, dist_pt]; ring_nf
  · simp [pt]
  · simp [pt]

end Chapter10

end Part_Examples

/-! ## Part 8: `Appendix` -/

section Part_Appendix


/-!
# Appendix: Polytopes and polyhedra

Basic notions about polytopes in `ℝᵈ`, modelled as `EuclideanSpace ℝ (Fin d)`.
-/

open Set Finset

namespace Chapter10

/-- `ℝᵈ`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- A *convex polytope* in `ℝᵈ` is the convex hull of a finite set
`S = {s₁, …, sₙ}`, i.e. the set of all `∑ λᵢ sᵢ` with `λᵢ ≥ 0`, `∑ λᵢ = 1`. -/
def IsConvexPolytope (P : Set (Rd d)) : Prop :=
  ∃ S : Finset (Rd d), P = convexHull ℝ (S : Set (Rd d))

/-- The convex hull of a finite set, written out as in the book. -/
theorem convexHull_finset_eq (S : Finset (Rd d)) :
    convexHull ℝ (S : Set (Rd d)) =
      {x | ∃ w : Rd d → ℝ, (∀ s ∈ S, 0 ≤ w s) ∧ ∑ s ∈ S, w s = 1 ∧ ∑ s ∈ S, w s • s = x} := by
  rw [Finset.convexHull_eq]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, h0, h1, h2⟩
    exact ⟨w, h0, h1, by rwa [Finset.centerMass_eq_of_sum_1 _ _ h1] at h2⟩
  · rintro ⟨w, h0, h1, h2⟩
    exact ⟨w, h0, h1, by rwa [Finset.centerMass_eq_of_sum_1 _ _ h1]⟩

/-- A `d`-dimensional *simplex* is the convex hull of an affinely independent set of
cardinality `d + 1` (a triangle for `d = 2`, a tetrahedron for `d = 3`). -/
def IsSimplex (P : Set (Rd d)) : Prop :=
  ∃ S : Finset (Rd d), S.card = d + 1 ∧ AffineIndependent ℝ ((↑) : S → Rd d) ∧
    P = convexHull ℝ (S : Set (Rd d))

/-- The unit `d`-cube `C_d = [0, 1]ᵈ`. -/
def unitCube (d : ℕ) : Set (Rd d) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

/-- A (general) *polytope* is a finite union of convex polytopes. -/
def IsPolytope (P : Set (Rd d)) : Prop :=
  ∃ C : Finset (Set (Rd d)), (∀ Q ∈ C, IsConvexPolytope Q) ∧ P = ⋃ Q ∈ C, Q

/-- A *face* of `P` is a subset of the form `P ∩ {x : aᵀx = b}`, where `aᵀx ≤ b` is a linear
inequality that is valid for all points `x ∈ P`. -/
def IsFace (F P : Set (Rd d)) : Prop :=
  ∃ (a : Rd d) (b : ℝ), (∀ x ∈ P, inner ℝ a x ≤ b) ∧ F = P ∩ {x | inner ℝ a x = b}

open Classical in
/-- The dimension of a nonempty subset of `ℝᵈ` (the dimension of its affine hull); we use the
convention that the empty set has dimension `-1`. -/
noncomputable def dim (F : Set (Rd d)) : ℤ :=
  if F.Nonempty then (Module.finrank ℝ (affineSpan ℝ F).direction : ℤ) else -1

/-- A *vertex* is a `0`-dimensional face, i.e. a face consisting of a single point. -/
def IsVertex (P : Set (Rd d)) (v : Rd d) : Prop := IsFace {v} P

/-- The set of vertices of `P`. -/
def vertices (P : Set (Rd d)) : Set (Rd d) := {v | IsVertex P v}

/-- An *edge* is a `1`-dimensional face. -/
def IsEdge (F P : Set (Rd d)) : Prop := IsFace F P ∧ dim F = 1

/-- A *facet* is a `(d-1)`-dimensional face. -/
def IsFacet (F P : Set (Rd d)) : Prop := IsFace F P ∧ dim F = (d : ℤ) - 1

/-- Two polytopes are *congruent* if there is a length-preserving affine map that takes one to
the other (this may reverse the orientation, e.g. a reflection). -/
def Congruent (P Q : Set (Rd d)) : Prop := ∃ f : Rd d ≃ᵃⁱ[ℝ] Rd d, f '' P = Q

/-- Two polytopes are *combinatorially equivalent* if there is a bijection between their faces
that preserves dimension and inclusions. -/
def CombinatoriallyEquivalent (P Q : Set (Rd d)) : Prop :=
  ∃ φ : {F // IsFace F P} ≃ {G // IsFace G Q},
    (∀ F, dim (φ F).1 = dim F.1) ∧ ∀ F G, F.1 ⊆ G.1 ↔ (φ F).1 ⊆ (φ G).1

/-- The *graph* `G(P)` of a polytope: its vertices, two of them being adjacent if the segment
between them is an edge (a `1`-dimensional face). -/
def polytopeGraph (P : Set (Rd d)) : SimpleGraph (vertices P) where
  Adj u v := u ≠ v ∧ IsEdge (segment ℝ (u : Rd d) v) P
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- A set is *centrally symmetric* with center `x₀` if `x₀ + x ∈ P ↔ x₀ - x ∈ P`. -/
def IsCentrallySymmetric (P : Set (Rd d)) : Prop := ∃ x₀ : Rd d, ∀ x, x₀ + x ∈ P ↔ x₀ - x ∈ P

/-! ### Results -/

/-- The unit cube is the convex hull of its `2ᵈ` vertices (the `0/1`-vectors); in particular it
is a convex polytope. -/
theorem unitCube_eq_convexHull :
    unitCube d = convexHull ℝ {x : Rd d | ∀ i, x i = 0 ∨ x i = 1} := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ))
  have h1 : {x : Rd d | ∀ i, x i = 0 ∨ x i = 1} =
      e.symm '' (univ.pi fun _ => ({0, 1} : Set ℝ)) := by
    rw [LinearEquiv.image_symm_eq_preimage]; ext x; simp [e]
  have h2 : unitCube d = e.symm '' (univ.pi fun _ => Icc 0 1) := by
    rw [LinearEquiv.image_symm_eq_preimage]; ext x
    simp only [unitCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]; rfl
  have h3 := LinearMap.image_convexHull (e.symm : (Fin d → ℝ) →ₗ[ℝ] Rd d)
    (univ.pi fun _ => ({0, 1} : Set ℝ))
  simp only [LinearEquiv.coe_coe] at h3
  rw [h1, h2, ← h3, convexHull_pi]
  congr 2
  ext i : 1
  rw [convexHull_pair, segment_eq_Icc zero_le_one]

/-- The vertex set `{0,1}ᵈ` of the unit cube is finite. -/
theorem finite_cube_vertices : {x : Rd d | ∀ i, x i = 0 ∨ x i = 1}.Finite := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ))
  have h1 : {x : Rd d | ∀ i, x i = 0 ∨ x i = 1} =
      e.symm '' (univ.pi fun _ => ({0, 1} : Set ℝ)) := by
    rw [LinearEquiv.image_symm_eq_preimage]; ext x; simp [e]
  rw [h1]
  exact (Set.Finite.pi fun _ => by simp).image _

theorem isConvexPolytope_unitCube : IsConvexPolytope (unitCube d) :=
  ⟨finite_cube_vertices.toFinset, by rw [Set.Finite.coe_toFinset, unitCube_eq_convexHull]⟩

/-- The unit cube is centrally symmetric (with center `(1/2, …, 1/2)`). -/
theorem isCentrallySymmetric_unitCube : IsCentrallySymmetric (unitCube d) := by
  refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), fun x => ?_⟩
  simp only [unitCube, Set.mem_ofPred_eq, Set.mem_Icc, PiLp.add_apply, PiLp.sub_apply]
  constructor <;> intro h i <;> specialize h i <;> simp at h ⊢ <;> constructor <;> linarith

/-- Every convex polytope is a polytope. -/
theorem IsConvexPolytope.isPolytope {P : Set (Rd d)} (h : IsConvexPolytope P) : IsPolytope P :=
  ⟨{P}, by simpa using h, by simp⟩

lemma inner_sum_smul (S : Finset (Rd d)) (w : Rd d → ℝ) (a : Rd d) :
    inner ℝ a (∑ s ∈ S, w s • s) = ∑ s ∈ S, w s * inner ℝ a s := by
  rw [inner_sum]; simp_rw [real_inner_smul_right]

/-- If `aᵀx ≤ b` is valid on the finite set `S`, then the face `conv S ∩ {aᵀx = b}` is the convex
hull of the points of `S` on the hyperplane `aᵀx = b`. -/
theorem convexHull_inter_hyperplane (S : Finset (Rd d)) (a : Rd d) (b : ℝ)
    (hS : ∀ s ∈ S, inner ℝ a s ≤ b) :
    convexHull ℝ (S : Set (Rd d)) ∩ {x | inner ℝ a x = b} =
      convexHull ℝ ((S.filter fun s => inner ℝ a s = b : Finset (Rd d)) : Set (Rd d)) := by
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    rw [convexHull_finset_eq] at hx ⊢
    obtain ⟨w, hw0, hw1, rfl⟩ := hx
    have hsum : ∑ s ∈ S, w s * (b - inner ℝ a s) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
      rw [Set.mem_ofPred_eq, inner_sum_smul] at hxb
      rw [hxb]; ring
    have key := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s hs => mul_nonneg (hw0 s hs) (sub_nonneg.2 (hS s hs)))).1 hsum
    have hw : ∀ s ∈ S, inner ℝ a s ≠ b → w s = 0 := by
      intro s hs hne
      rcases mul_eq_zero.1 (key s hs) with h | h
      · exact h
      · exact absurd (by linarith) hne
    refine ⟨w, fun s hs => hw0 s (Finset.mem_filter.1 hs).1, ?_, ?_⟩
    · rw [Finset.sum_filter, ← hw1]
      refine Finset.sum_congr rfl fun s hs => ?_
      split_ifs with h
      · rfl
      · rw [hw s hs h]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun s hs => ?_
      split_ifs with h
      · rfl
      · rw [hw s hs h, zero_smul]
  · intro hx
    refine ⟨convexHull_mono (Finset.coe_subset.2 (Finset.filter_subset _ _)) hx, ?_⟩
    rw [convexHull_finset_eq] at hx
    obtain ⟨w, hw0, hw1, rfl⟩ := hx
    rw [Set.mem_ofPred_eq, inner_sum_smul]
    calc _ = ∑ s ∈ S.filter (fun s => inner ℝ a s = b), w s * b :=
          Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_filter.1 hs).2]
      _ = b := by rw [← Finset.sum_mul, hw1, one_mul]

/-- All the faces of a convex polytope are themselves convex polytopes. -/
theorem IsFace.isConvexPolytope {F P : Set (Rd d)} (hP : IsConvexPolytope P) (hF : IsFace F P) :
    IsConvexPolytope F := by
  obtain ⟨S, rfl⟩ := hP
  obtain ⟨a, b, hvalid, rfl⟩ := hF
  exact ⟨_, convexHull_inter_hyperplane S a b fun s hs =>
    hvalid s (subset_convexHull ℝ _ (Finset.mem_coe.2 hs))⟩

/-- A linear inequality valid on `S` is valid on `conv S`. -/
lemma inner_le_of_mem_convexHull {S : Finset (Rd d)} {a : Rd d} {b : ℝ}
    (hS : ∀ s ∈ S, inner ℝ a s ≤ b) {y : Rd d} (hy : y ∈ convexHull ℝ (S : Set (Rd d))) :
    inner ℝ a y ≤ b := by
  rw [convexHull_finset_eq] at hy
  obtain ⟨w, hw0, hw1, rfl⟩ := hy
  rw [inner_sum_smul]
  calc ∑ s ∈ S, w s * inner ℝ a s ≤ ∑ s ∈ S, w s * b :=
        Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hS s hs) (hw0 s hs)
    _ = b := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A vertex lies in the polytope. -/
lemma IsVertex.mem {P : Set (Rd d)} {v : Rd d} (hv : IsVertex P v) : v ∈ P := by
  obtain ⟨a, b, -, hF⟩ := hv
  exact (hF.subset (Set.mem_singleton v)).1

/-- A vertex (a `0`-dimensional face) is an extreme point. -/
lemma IsVertex.mem_extremePoints {P : Set (Rd d)} {v : Rd d} (hv : IsVertex P v) :
    v ∈ P.extremePoints ℝ := by
  obtain ⟨a, b, hvalid, hF⟩ := hv
  have hv' := hF.subset (Set.mem_singleton v)
  rw [_root_.mem_extremePoints]
  refine ⟨hv'.1, fun x₁ h₁ x₂ h₂ hseg => ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hx⟩ := hseg
  have hb : inner ℝ a v = b := hv'.2
  rw [← hx, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hb
  have e1 := hvalid x₁ h₁
  have e2 := hvalid x₂ h₂
  have hb' : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
  have k1 : inner ℝ a x₁ = b := by
    by_contra hne
    have hlt := lt_of_le_of_ne e1 hne
    nlinarith [mul_pos hα (sub_pos.2 hlt), mul_nonneg hβ.le (sub_nonneg.2 e2), hb']
  have k2 : inner ℝ a x₂ = b := by
    by_contra hne
    have hlt := lt_of_le_of_ne e2 hne
    nlinarith [mul_pos hβ (sub_pos.2 hlt), mul_nonneg hα.le (sub_nonneg.2 e1), hb']
  have m1 : x₁ ∈ ({v} : Set (Rd d)) := hF ▸ ⟨h₁, k1⟩
  have m2 : x₂ ∈ ({v} : Set (Rd d)) := hF ▸ ⟨h₂, k2⟩
  exact ⟨m1, m2⟩

/-- Every extreme point of a convex polytope is a vertex: it can be cut off by a hyperplane. -/
lemma extremePoints_subset_vertices (S : Finset (Rd d)) :
    (convexHull ℝ (S : Set (Rd d))).extremePoints ℝ ⊆ vertices (convexHull ℝ (S : Set (Rd d))) := by
  intro x hx
  have hxS : x ∈ S := extremePoints_convexHull_subset hx
  set T := S.erase x
  have hxT : x ∉ convexHull ℝ (T : Set (Rd d)) := by
    intro h
    have h1 := inter_extremePoints_subset_extremePoints_of_subset
      (convexHull_mono (Finset.coe_subset.2 (Finset.erase_subset x S))) ⟨h, hx⟩
    have h2 := extremePoints_convexHull_subset h1
    simp at h2
  obtain ⟨f, u, v, hfT, huv, hfx⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ (T : Set (Rd d))) (T.finite_toSet.isCompact_convexHull ℝ)
    (convex_singleton x) isClosed_singleton (Set.disjoint_singleton_right.2 hxT)
  have hfx' : v < f x := hfx x rfl
  set a := (InnerProductSpace.toDual ℝ (Rd d)).symm f
  have ha : ∀ y, inner ℝ a y = f y := fun y => InnerProductSpace.toDual_symm_apply
  have hlt : ∀ s ∈ S, s ≠ x → inner ℝ a s < f x := by
    intro s hs hne
    rw [ha]
    have := hfT s (subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hs⟩)))
    linarith
  have hvalid : ∀ s ∈ S, inner ℝ a s ≤ f x := by
    intro s hs
    by_cases hsx : s = x
    · rw [hsx, ha]
    · exact (hlt s hs hsx).le
  refine ⟨a, f x, fun y hy => inner_le_of_mem_convexHull hvalid hy, ?_⟩
  rw [convexHull_inter_hyperplane S a (f x) hvalid]
  have : (S.filter fun s => inner ℝ a s = f x) = {x} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hfs⟩
      by_contra hne
      exact (hlt s hs hne).ne hfs
    · rintro rfl
      exact ⟨hxS, ha s⟩
  rw [this, Finset.coe_singleton, convexHull_singleton]

/-- The vertices of a convex polytope span it: `conv(V) = P`. -/
theorem convexHull_vertices {P : Set (Rd d)} (hP : IsConvexPolytope P) :
    convexHull ℝ (vertices P) = P := by
  obtain ⟨S, rfl⟩ := hP
  apply Set.Subset.antisymm
  · exact convexHull_min (fun v hv => IsVertex.mem hv) (convex_convexHull ℝ _)
  · have hKM := closure_convexHull_extremePoints (S.finite_toSet.isCompact_convexHull ℝ)
      (convex_convexHull ℝ (S : Set (Rd d)))
    have hfin : ((convexHull ℝ (S : Set (Rd d))).extremePoints ℝ).Finite :=
      S.finite_toSet.subset extremePoints_convexHull_subset
    rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hKM
    calc convexHull ℝ (S : Set (Rd d))
        = convexHull ℝ ((convexHull ℝ (S : Set (Rd d))).extremePoints ℝ) := hKM.symm
      _ ⊆ _ := convexHull_mono (extremePoints_subset_vertices S)

/-- The set of vertices of a convex polytope is the inclusion-minimal set with `conv(V) = P`:
every set whose convex hull is `P` contains all vertices. -/
theorem vertices_subset_of_convexHull_eq {P V : Set (Rd d)} (h : convexHull ℝ V = P) :
    vertices P ⊆ V := by
  intro v hv
  have := hv.mem_extremePoints
  rw [← h] at this
  exact extremePoints_convexHull_subset this

/-- Let `F` be a facet of a `d`-dimensional convex polytope `P`, and `H_F` the hyperplane it
determines. Then one of the two closed halfspaces bounded by `H_F` contains `P`, and the other
one doesn't. -/
theorem facet_halfspace (hd : 1 ≤ d) {F P : Set (Rd d)} (hPd : dim P = d) (hF : IsFacet F P) :
    ∃ (a : Rd d) (b : ℝ), a ≠ 0 ∧ (affineSpan ℝ F : Set (Rd d)) = {x | inner ℝ a x = b} ∧
      P ⊆ {x | inner ℝ a x ≤ b} ∧ ¬ P ⊆ {x | b ≤ inner ℝ a x} := by
  obtain ⟨⟨a, b, hvalid, rfl⟩, hdimF⟩ := hF
  set F := P ∩ {x | inner ℝ a x = b} with hFdef
  -- `F` is nonempty and its affine hull has dimension `d - 1`
  have hFne : F.Nonempty := by
    by_contra h
    simp only [dim, h, ite_false] at hdimF
    omega
  have hFrank : (Module.finrank ℝ (affineSpan ℝ F).direction : ℤ) = d - 1 := by
    simpa [dim, hFne] using hdimF
  have hPne : P.Nonempty := hFne.mono Set.inter_subset_left
  have hPrank : (Module.finrank ℝ (affineSpan ℝ P).direction : ℤ) = d := by
    simpa [dim, hPne] using hPd
  obtain ⟨p, hpP, hpb⟩ := hFne
  -- `a ≠ 0`
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [inner_zero_left, Set.mem_ofPred_eq] at hpb
    subst hpb
    have : F = P := by ext x; simp [hFdef]
    rw [this] at hFrank
    omega
  -- the hyperplane `H = {x | aᵀx = b}`
  set H : AffineSubspace ℝ (Rd d) := AffineSubspace.mk' p (ℝ ∙ a)ᗮ
  have hmemH : ∀ x, x ∈ H ↔ inner ℝ a x = b := by
    intro x
    rw [AffineSubspace.mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right,
      vsub_eq_sub, inner_sub_right, hpb, sub_eq_zero]
  have hHrank : Module.finrank ℝ H.direction = d - 1 := by
    rw [AffineSubspace.direction_mk']
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ a)
    rw [finrank_span_singleton ha, finrank_euclideanSpace_fin] at h1
    omega
  have hle : affineSpan ℝ F ≤ H := by
    rw [affineSpan_le]
    intro x hx
    exact (hmemH x).2 hx.2
  have heq : affineSpan ℝ F = H := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hle
    · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
      rw [hHrank]; omega
    · exact ⟨p, subset_affineSpan ℝ F ⟨hpP, hpb⟩⟩
  refine ⟨a, b, ha, ?_, hvalid, ?_⟩
  · rw [heq]; ext x; exact hmemH x
  · intro hge
    have hPH : affineSpan ℝ P ≤ H := by
      rw [affineSpan_le]
      intro x hx
      exact (hmemH x).2 (le_antisymm (hvalid x hx) (hge hx))
    have := Submodule.finrank_mono (AffineSubspace.direction_le hPH)
    omega

/-! ### Congruent polytopes are combinatorially equivalent -/

lemma affineIsometryEquiv_apply (f : Rd d ≃ᵃⁱ[ℝ] Rd d) (x : Rd d) :
    f x = f.linearIsometryEquiv x + f 0 := by
  have := f.map_vadd 0 x
  simpa using this

/-- An isometry maps faces to faces. -/
lemma IsFace.image {F P : Set (Rd d)} (hF : IsFace F P) (f : Rd d ≃ᵃⁱ[ℝ] Rd d) :
    IsFace (f '' F) (f '' P) := by
  obtain ⟨a, b, hvalid, rfl⟩ := hF
  set L := f.linearIsometryEquiv
  have key : ∀ x, inner ℝ (L a) (f x) = inner ℝ a x + inner ℝ (L a) (f 0) := by
    intro x
    rw [affineIsometryEquiv_apply, inner_add_right, LinearIsometryEquiv.inner_map_map]
  refine ⟨L a, b + inner ℝ (L a) (f 0), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [key]; linarith [hvalid x hx]
  · rw [Set.image_inter f.injective]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [key, hx]
    · intro hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rw [← f.apply_symm_apply y, key] at hy
      linarith

/-- An isometry preserves dimensions. -/
lemma dim_image (F : Set (Rd d)) (f : Rd d ≃ᵃⁱ[ℝ] Rd d) : dim (f '' F) = dim F := by
  unfold dim
  by_cases hF : F.Nonempty
  · rw [ite_eq_left hF, ite_eq_left (hF.image f)]
    congr 1
    have h1 := AffineSubspace.map_span (k := ℝ) f.toAffineEquiv.toAffineMap F
    have h2 := AffineSubspace.map_direction f.toAffineEquiv.toAffineMap (affineSpan ℝ F)
    simp only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv] at h1 h2
    rw [← h1, h2]
    exact LinearEquiv.finrank_map_eq f.toAffineEquiv.linear _
  · rw [ite_eq_right hF, ite_eq_right (by simpa using hF)]

/-- Congruent polytopes are combinatorially equivalent (combinatorial equivalence is much weaker
than congruence). -/
theorem Congruent.combinatoriallyEquivalent {P Q : Set (Rd d)} (h : Congruent P Q) :
    CombinatoriallyEquivalent P Q := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨{ toFun := fun F => ⟨f '' F.1, F.2.image f⟩
            invFun := fun G => ⟨f.symm '' G.1, by
              have := G.2.image f.symm
              rwa [← Set.image_comp, show (f.symm ∘ f) = id from funext f.symm_apply_apply,
                Set.image_id] at this⟩
            left_inv := fun F => Subtype.ext (by
              simp only [← Set.image_comp, show (f.symm ∘ f) = id from funext f.symm_apply_apply,
                Set.image_id])
            right_inv := fun G => Subtype.ext (by
              simp only [← Set.image_comp, show (f ∘ f.symm) = id from funext f.apply_symm_apply,
                Set.image_id]) }, fun F => dim_image _ f, fun F G => ?_⟩
  exact (Set.image_subset_image_iff f.injective).symm

end Chapter10

end Part_Appendix

/-! ## Part 9: `Decompositions` -/

section Part_Decompositions


/-!
# Equidecomposable and equicomplementable polyhedra (geometric definitions)

The geometric notions from the beginning of the chapter, for subsets of `ℝᵈ`:
two polyhedra `P` and `Q` are *equidecomposable* if they can be decomposed into finite sets of
polyhedra `P₁, …, Pₙ` and `Q₁, …, Qₙ` such that `Pᵢ` and `Qᵢ` are congruent for all `i`. They are
*equicomplementable* if there are equidecomposable polyhedra `P̃` and `Q̃` that also have
decompositions `P̃ = P ∪ P'₁ ∪ ⋯ ∪ P'ₘ` and `Q̃ = Q ∪ Q'₁ ∪ ⋯ ∪ Q'ₘ` with `P'ₖ` congruent to
`Q'ₖ` for all `k`.
-/

open Set

namespace Chapter10

variable {d : ℕ}

/-- `P = P₁ ∪ ⋯ ∪ Pₙ` is a *decomposition* of `P`: the pieces are polyhedra (polytopes), their
union is `P`, and their interiors are pairwise disjoint. -/
def IsDecomposition {n : ℕ} (P : Set (Rd d)) (pieces : Fin n → Set (Rd d)) : Prop :=
  (∀ i, IsPolytope (pieces i)) ∧ (⋃ i, pieces i) = P ∧
    Pairwise fun i j => Disjoint (interior (pieces i)) (interior (pieces j))

/-- `P` and `Q` are *equidecomposable*. -/
def GeomEquidecomposable (P Q : Set (Rd d)) : Prop :=
  ∃ (n : ℕ) (Ps Qs : Fin n → Set (Rd d)),
    IsDecomposition P Ps ∧ IsDecomposition Q Qs ∧ ∀ i, Congruent (Ps i) (Qs i)

/-- `P` and `Q` are *equicomplementable* (here `Pt`, `Qt` stand for `P̃`, `Q̃`). -/
def GeomEquicomplementable (P Q : Set (Rd d)) : Prop :=
  ∃ (m : ℕ) (P' Q' : Fin m → Set (Rd d)) (Pt Qt : Set (Rd d)),
    IsDecomposition Pt (Fin.cons P P') ∧ IsDecomposition Qt (Fin.cons Q Q') ∧
      (∀ k, Congruent (P' k) (Q' k)) ∧ GeomEquidecomposable Pt Qt

/-- A finite union of polytopes is a polytope. -/
theorem IsPolytope.iUnion {n : ℕ} {P : Fin n → Set (Rd d)} (h : ∀ i, IsPolytope (P i)) :
    IsPolytope (⋃ i, P i) := by
  classical
  choose C hC hP using h
  refine ⟨Finset.univ.biUnion C, fun Q hQ => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hQ
    exact hC i Q hi
  · rw [Finset.set_biUnion_biUnion]
    simp only [Finset.mem_univ, iUnion_true]
    exact iUnion_congr fun i => hP i

/-- A decomposed set is a polytope. -/
theorem IsDecomposition.isPolytope {n : ℕ} {P : Set (Rd d)} {Ps : Fin n → Set (Rd d)}
    (h : IsDecomposition P Ps) : IsPolytope P := h.2.1 ▸ IsPolytope.iUnion h.1

/-- Every polytope is decomposed into the single piece `P`. -/
theorem isDecomposition_single {P : Set (Rd d)} (hP : IsPolytope P) :
    IsDecomposition P (Fin.cons P Fin.elim0 : Fin 1 → Set (Rd d)) := by
  refine ⟨fun i => ?_, ?_, fun i j hij => (hij (Subsingleton.elim (α := Fin 1) i j)).elim⟩
  · rw [Fin.fin_one_eq_zero i]; exact hP
  · ext x; simp

theorem Congruent.refl (P : Set (Rd d)) : Congruent P P := ⟨AffineIsometryEquiv.refl ℝ _, by simp⟩

theorem Congruent.symm {P Q : Set (Rd d)} (h : Congruent P Q) : Congruent Q P := by
  obtain ⟨f, rfl⟩ := h
  exact ⟨f.symm, by rw [← Set.image_comp]; simp⟩

theorem Congruent.trans {P Q R : Set (Rd d)} (h₁ : Congruent P Q) (h₂ : Congruent Q R) :
    Congruent P R := by
  obtain ⟨f, rfl⟩ := h₁
  obtain ⟨g, rfl⟩ := h₂
  exact ⟨f.trans g, by rw [← Set.image_comp]; rfl⟩

theorem GeomEquidecomposable.symm {P Q : Set (Rd d)} (h : GeomEquidecomposable P Q) :
    GeomEquidecomposable Q P := by
  obtain ⟨n, Ps, Qs, hP, hQ, hc⟩ := h
  exact ⟨n, Qs, Ps, hQ, hP, fun i => (hc i).symm⟩

/-- Clearly, equidecomposable objects are equicomplementable (this is the case `m = 0`). -/
theorem GeomEquidecomposable.geomEquicomplementable {P Q : Set (Rd d)}
    (h : GeomEquidecomposable P Q) : GeomEquicomplementable P Q := by
  obtain ⟨n, Ps, Qs, hP, hQ, hc⟩ := h
  exact ⟨0, Fin.elim0, Fin.elim0, P, Q, isDecomposition_single hP.isPolytope,
    isDecomposition_single hQ.isPolytope, fun k => k.elim0, n, Ps, Qs, hP, hQ, hc⟩

end Chapter10

end Part_Decompositions

/-! ## Part 10: `MinkowskiWeyl` -/

section Part_MinkowskiWeyl


/-!
# Convex polytopes as bounded solution sets of linear inequalities

The appendix states: *Convex polytopes can, equivalently, be defined as the bounded solution
sets of finite systems of linear inequalities. Thus every convex polytope `P ⊆ ℝᵈ` has a
representation of the form `P = {x ∈ ℝᵈ : Ax ≤ b}`. Conversely, every bounded such solution set is
a convex polytope.*

The book does not prove this ("Minkowski–Weyl") theorem. We prove both directions:

* bounded solution sets are convex polytopes: a bounded solution set is compact and convex, so by
  the Krein–Milman theorem it is the convex hull of its extreme points; an extreme point is
  determined by the set of inequalities that are tight at it, so there are only finitely many;
* convex polytopes are solution sets: `conv S` is the projection of the solution set of a finite
  system (in the variables `x` and the convex coefficients `λ`), and projections of solution sets
  are solution sets by Fourier–Motzkin elimination.
-/

open Set Finset Filter Topology

namespace Chapter10

variable {d : ℕ}

/-- The solution set `{x ∈ ℝᵈ : aᵢᵀ x ≤ bᵢ for all i}` of a system of linear inequalities. -/
def solSet {ι : Type} (a : ι → Rd d) (b : ι → ℝ) : Set (Rd d) := {x | ∀ i, inner ℝ (a i) x ≤ b i}

section HtoV

variable {ι : Type} [Finite ι] (a : ι → Rd d) (b : ι → ℝ)

omit [Finite ι] in
lemma isClosed_solSet : IsClosed (solSet a b) := by
  have : solSet a b = ⋂ i, {x | inner ℝ (a i) x ≤ b i} := by ext; simp [solSet]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const

omit [Finite ι] in
lemma convex_solSet : Convex ℝ (solSet a b) := by
  intro x hx y hy α β hα hβ hαβ i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := mul_le_mul_of_nonneg_left (hx i) hα
  have h2 := mul_le_mul_of_nonneg_left (hy i) hβ
  have h3 : α * b i + β * b i = b i := by rw [← add_mul, hαβ, one_mul]
  linarith

/-- An extreme point of a solution set is determined by the set of inequalities that are tight
at it. -/
lemma eq_of_mem_extremePoints_of_tight_eq {x y : Rd d}
    (hx : x ∈ (solSet a b).extremePoints ℝ) (hy : y ∈ (solSet a b).extremePoints ℝ)
    (htight : {i | inner ℝ (a i) x = b i} = {i | inner ℝ (a i) y = b i}) : x = y := by
  have hxK := hx.1
  have hyK := hy.1
  -- for small `t`, the point `x + t (x - y)` still satisfies the non-tight inequalities strictly
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, inner ℝ (a i) x < b i →
      inner ℝ (a i) (x + t • (x - y)) < b i := by
    rw [eventually_all]
    intro i
    by_cases h : inner ℝ (a i) x < b i
    · have hc : Continuous fun t : ℝ => inner ℝ (a i) (x + t • (x - y)) :=
        continuous_const.inner (continuous_const.add (continuous_id.smul continuous_const))
      have : ∀ᶠ t in 𝓝 (0 : ℝ), inner ℝ (a i) (x + t • (x - y)) < b i :=
        hc.continuousAt.eventually_lt continuousAt_const (by simpa using h)
      exact this.mono fun t ht _ => ht
    · exact Eventually.of_forall fun t h' => absurd h' h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set t := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (half_pos hε) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hplus : x + t • (x - y) ∈ solSet a b := by
    intro i
    by_cases h : inner ℝ (a i) x = b i
    · have hyi : inner ℝ (a i) y = b i := by
        have : i ∈ {i | inner ℝ (a i) x = b i} := h
        rw [htight] at this; exact this
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, h, hyi]; simp
    · exact (hball htε i (lt_of_le_of_ne (hxK i) h)).le
  have hminus : x - t • (x - y) ∈ solSet a b := by
    intro i
    rw [inner_sub_right, real_inner_smul_right, inner_sub_right]
    have := hxK i
    have := hyK i
    nlinarith
  have hseg : x ∈ openSegment ℝ (x - t • (x - y)) (x + t • (x - y)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := (_root_.mem_extremePoints.1 hx).2 _ hminus _ hplus hseg
  have h2 : t • (x - y) = 0 := by
    have := this.2
    rw [add_eq_left] at this
    exact this
  rw [smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 ht0.ne'
  · exact sub_eq_zero.1 h2

/-- A solution set has only finitely many extreme points. -/
lemma finite_extremePoints_solSet : ((solSet a b).extremePoints ℝ).Finite :=
  Set.Finite.of_injOn (f := fun x => {i | inner ℝ (a i) x = b i}) (Set.mapsTo_univ _ _)
    (fun _ hx _ hy h => eq_of_mem_extremePoints_of_tight_eq a b hx hy h) Set.finite_univ

/-- **Every bounded solution set of a finite system of linear inequalities is a convex
polytope.** -/
theorem isConvexPolytope_solSet (hb : Bornology.IsBounded (solSet a b)) :
    IsConvexPolytope (solSet a b) := by
  have hcomp : IsCompact (solSet a b) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_solSet a b) hb
  have hKM := closure_convexHull_extremePoints hcomp (convex_solSet a b)
  have hfin := finite_extremePoints_solSet a b
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hKM
  exact ⟨hfin.toFinset, by rw [Set.Finite.coe_toFinset, hKM]⟩

end HtoV

section VtoH

/-- A subset of a real vector space is *polyhedral* if it is the solution set of finitely many
linear inequalities. -/
def IsPolyhedral {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ), X = {x | ∀ i, f i x ≤ b i}

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma IsPolyhedral.preimage {X : Set F} (hX : IsPolyhedral X) (g : E →ₗ[ℝ] F) :
    IsPolyhedral (g ⁻¹' X) := by
  obtain ⟨ι, _, f, b, rfl⟩ := hX
  exact ⟨ι, inferInstance, fun i => (f i).comp g, b, by ext; simp⟩

lemma IsPolyhedral.inter {X Y : Set E} (hX : IsPolyhedral X) (hY : IsPolyhedral Y) :
    IsPolyhedral (X ∩ Y) := by
  obtain ⟨ι, _, f, b, rfl⟩ := hX
  obtain ⟨κ, _, g, c, rfl⟩ := hY
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim f g, Sum.elim b c, ?_⟩
  ext x
  simp [Sum.forall]

lemma isPolyhedral_le (f : E →ₗ[ℝ] ℝ) (b : ℝ) : IsPolyhedral {x | f x ≤ b} :=
  ⟨Unit, inferInstance, fun _ => f, fun _ => b, by ext; simp⟩

lemma isPolyhedral_eq (f : E →ₗ[ℝ] ℝ) (b : ℝ) : IsPolyhedral {x | f x = b} := by
  have : {x | f x = b} = {x | f x ≤ b} ∩ {x | (-f) x ≤ -b} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, LinearMap.neg_apply, neg_le_neg_iff]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  rw [this]
  exact (isPolyhedral_le _ _).inter (isPolyhedral_le _ _)

lemma isPolyhedral_iInter {κ : Type} [Fintype κ] {X : κ → Set E} (hX : ∀ k, IsPolyhedral (X k)) :
    IsPolyhedral (⋂ k, X k) := by
  choose ι _ f b hfb using hX
  refine ⟨Σ k, ι k, inferInstance, fun p => f p.1 p.2, fun p => b p.1 p.2, ?_⟩
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Sigma.forall]
  exact forall_congr' fun k => by rw [hfb k]; rfl

/-- **Fourier–Motzkin elimination** (one variable): the projection of a polyhedral subset of
`E × ℝ` to `E` is polyhedral. -/
lemma IsPolyhedral.image_fst_prod_real {X : Set (E × ℝ)} (hX : IsPolyhedral X) :
    IsPolyhedral (Prod.fst '' X) := by
  classical
  obtain ⟨ι, _, f, b, rfl⟩ := hX
  set g : ι → E →ₗ[ℝ] ℝ := fun i => (f i).comp (LinearMap.inl ℝ E ℝ)
  set c : ι → ℝ := fun i => f i (0, 1)
  have hf : ∀ i x t, f i (x, t) = g i x + c i * t := by
    intro i x t
    have : ((x, t) : E × ℝ) = (x, 0) + t • (0, 1) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [g, c, mul_comm]
  -- upper bounds (`c i > 0`) and lower bounds (`c i < 0`) on `t`
  have hup : ∀ i, 0 < c i → ∀ x t, (g i x + c i * t ≤ b i ↔ t ≤ (b i - g i x) / c i) := by
    intro i hi x t
    rw [le_div_iff₀ hi]; constructor <;> intro h <;> linarith
  have hlo : ∀ i, c i < 0 → ∀ x t, (g i x + c i * t ≤ b i ↔ (b i - g i x) / c i ≤ t) := by
    intro i hi x t
    rw [div_le_iff_of_neg hi]; constructor <;> intro h <;> linarith
  refine ⟨{i // c i = 0} ⊕ ({i // 0 < c i} × {i // c i < 0}), inferInstance,
    Sum.elim (fun i => g i.1) (fun p => (c p.1.1)⁻¹ • g p.1.1 - (c p.2.1)⁻¹ • g p.2.1),
    Sum.elim (fun i => b i.1) (fun p => b p.1.1 / c p.1.1 - b p.2.1 / c p.2.1), ?_⟩
  have hpair : ∀ (i : {i // 0 < c i}) (k : {i // c i < 0}) (x : E),
      ((c i.1)⁻¹ • g i.1 - (c k.1)⁻¹ • g k.1) x ≤ b i.1 / c i.1 - b k.1 / c k.1 ↔
        (b k.1 - g k.1 x) / c k.1 ≤ (b i.1 - g i.1 x) / c i.1 := by
    intro i k x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_div]
    rw [inv_mul_eq_div, inv_mul_eq_div]
    constructor <;> intro h <;> linarith
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Prod.forall, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i => ?_, fun i k => ?_⟩
    · have := ht i.1; rw [hf, i.2, zero_mul, add_zero] at this; exact this
    · rw [hpair]
      have h1 := (hup i.1 i.2 x t).1 (by rw [← hf]; exact ht i.1)
      have h2 := (hlo k.1 k.2 x t).1 (by rw [← hf]; exact ht k.1)
      linarith
  · rintro ⟨h0, hp⟩
    have hp' : ∀ (i : {i // 0 < c i}) (k : {i // c i < 0}),
        (b k.1 - g k.1 x) / c k.1 ≤ (b i.1 - g i.1 x) / c i.1 := fun i k => (hpair i k x).1 (hp i k)
    -- choose `t`: the largest lower bound, or the smallest upper bound, or `0`
    have key : ∃ t : ℝ, (∀ i : {i // 0 < c i}, t ≤ (b i.1 - g i.1 x) / c i.1) ∧
        ∀ k : {i // c i < 0}, (b k.1 - g k.1 x) / c k.1 ≤ t := by
      by_cases hn : Nonempty {i // c i < 0}
      · refine ⟨Finset.univ.sup' Finset.univ_nonempty fun k => (b k.1 - g k.1 x) / c k.1,
          fun i => Finset.sup'_le _ _ fun k _ => hp' i k,
          fun k => Finset.le_sup' (fun k : {i // c i < 0} => (b k.1 - g k.1 x) / c k.1)
            (Finset.mem_univ k)⟩
      · by_cases hpn : Nonempty {i // 0 < c i}
        · exact ⟨Finset.univ.inf' Finset.univ_nonempty
              fun i : {i // 0 < c i} => (b i.1 - g i.1 x) / c i.1,
            fun i => Finset.inf'_le (fun i : {i // 0 < c i} => (b i.1 - g i.1 x) / c i.1)
              (Finset.mem_univ i), fun k => absurd ⟨k⟩ hn⟩
        · exact ⟨0, fun i => absurd ⟨i⟩ hpn, fun k => absurd ⟨k⟩ hn⟩
    obtain ⟨t, htu, htl⟩ := key
    refine ⟨t, fun i => ?_⟩
    rw [hf]
    rcases lt_trichotomy (c i) 0 with h | h | h
    · exact (hlo i h x t).2 (htl ⟨i, h⟩)
    · rw [h, zero_mul, add_zero]; exact h0 ⟨i, h⟩
    · exact (hup i h x t).2 (htu ⟨i, h⟩)

/-- The linear map `((x, w), t) ↦ (x, (t, w))` (with `(t, w)` read as a vector in `ℝⁿ⁺¹`). -/
def consMap (E : Type*) [AddCommGroup E] [Module ℝ E] (n : ℕ) :
    (E × (Fin n → ℝ)) × ℝ →ₗ[ℝ] E × (Fin (n + 1) → ℝ) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  map_add' p q := by
    ext j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp
  map_smul' r p := by
    ext j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- Projections of polyhedral sets along `ℝⁿ` are polyhedral. -/
lemma IsPolyhedral.image_fst_prod_fin : ∀ (n : ℕ) {X : Set (E × (Fin n → ℝ))},
    IsPolyhedral X → IsPolyhedral (Prod.fst '' X)
  | 0, X, hX => by
    have : Prod.fst '' X = (LinearMap.inl ℝ E (Fin 0 → ℝ)) ⁻¹' X := by
      ext x
      simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, Set.mem_preimage,
        LinearMap.inl_apply]
      constructor
      · rintro ⟨v, hv⟩; rwa [Subsingleton.elim v 0] at hv
      · intro h; exact ⟨0, h⟩
    rw [this]; exact hX.preimage _
  | n + 1, X, hX => by
    have hY := hX.preimage (consMap E n)
    have : Prod.fst '' X = Prod.fst '' (Prod.fst '' ((consMap E n) ⁻¹' X)) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Prod.exists, exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨Fin.tail v, v 0, ?_⟩
        simpa [consMap, Fin.cons_self_tail] using hv
      · rintro ⟨w, t, h⟩
        exact ⟨_, h⟩
    rw [this]
    exact IsPolyhedral.image_fst_prod_fin n (IsPolyhedral.image_fst_prod_real hY)

/-- Projections of polyhedral sets along `ℝ^κ` (for a finite type `κ`) are polyhedral. -/
lemma IsPolyhedral.image_fst_prod_pi {κ : Type} [Fintype κ] {X : Set (E × (κ → ℝ))}
    (hX : IsPolyhedral X) : IsPolyhedral (Prod.fst '' X) := by
  set e := Fintype.equivFin κ
  set g : E × (Fin (Fintype.card κ) → ℝ) →ₗ[ℝ] E × (κ → ℝ) :=
    LinearMap.prodMap LinearMap.id (LinearMap.funLeft ℝ ℝ e)
  have : Prod.fst '' X = Prod.fst '' (g ⁻¹' X) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v ∘ e.symm, ?_⟩
      have hg : g (x, v ∘ e.symm) = (x, v) := by
        apply Prod.ext
        · rfl
        · funext k
          simp [g, LinearMap.funLeft]
      change g (x, v ∘ e.symm) ∈ X
      rw [hg]
      exact hv
    · rintro ⟨w, h⟩
      exact ⟨_, h⟩
  rw [this]
  exact IsPolyhedral.image_fst_prod_fin _ (hX.preimage g)

/-- The convex hull of a finite set in `ℝᵈ` is polyhedral. -/
theorem isPolyhedral_convexHull (S : Finset (Rd d)) :
    IsPolyhedral (convexHull ℝ (S : Set (Rd d))) := by
  classical
  -- the linear maps `(x, w) ↦ wₛ`, `(x, w) ↦ ∑ wₛ`, `(x, w) ↦ (x - ∑ wₛ s)ⱼ`
  set coord : S → Rd d × (S → ℝ) →ₗ[ℝ] ℝ := fun s => (LinearMap.proj s).comp (LinearMap.snd ℝ _ _)
  set total : Rd d × (S → ℝ) →ₗ[ℝ] ℝ := ∑ s, coord s
  set Φ : Rd d × (S → ℝ) →ₗ[ℝ] Rd d :=
    LinearMap.fst ℝ _ _ - ∑ s : S, (LinearMap.smulRight (coord s) (s : Rd d))
  set X : Set (Rd d × (S → ℝ)) :=
    (⋂ s, {p | (-coord s) p ≤ 0}) ∩ {p | total p = 1} ∩
      ⋂ j : Fin d, {p | ((EuclideanSpace.proj j : Rd d →L[ℝ] ℝ).toLinearMap.comp Φ) p = 0}
  have hX : IsPolyhedral X :=
    ((isPolyhedral_iInter fun s => isPolyhedral_le _ _).inter (isPolyhedral_eq _ _)).inter
      (isPolyhedral_iInter fun j => isPolyhedral_eq _ _)
  have hΦ : ∀ p : Rd d × (S → ℝ), Φ p = p.1 - ∑ s : S, p.2 s • (s : Rd d) := by
    intro p; simp [Φ, coord]
  have : convexHull ℝ (S : Set (Rd d)) = Prod.fst '' X := by
    ext x
    rw [convexHull_finset_eq]
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨w, hw0, hw1, rfl⟩
      refine ⟨fun s => w s, ⟨⟨Set.mem_iInter.2 fun s => ?_, ?_⟩, Set.mem_iInter.2 fun j => ?_⟩⟩
      · simpa [coord] using hw0 s s.2
      · simp only [Set.mem_ofPred_eq, total, coord, LinearMap.coe_sum, Finset.sum_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_snd, LinearMap.coe_proj,
          Function.eval]
        rw [Finset.sum_coe_sort S w]; exact hw1
      · simp only [Set.mem_ofPred_eq, LinearMap.coe_comp, Function.comp_apply, hΦ]
        rw [Finset.sum_coe_sort S (fun s => w s • s), sub_self, map_zero]
    · rintro ⟨w, ⟨⟨h0, h1⟩, h2⟩⟩
      refine ⟨fun y => if h : y ∈ S then w ⟨y, h⟩ else 0, fun s hs => ?_, ?_, ?_⟩
      · have := Set.mem_iInter.1 h0 ⟨s, hs⟩
        simpa [coord, hs] using this
      · rw [← Finset.sum_coe_sort S]
        simp only [Finset.coe_mem, dite_true]
        simpa [total, coord] using h1
      · have hzero : Φ (x, w) = 0 := by
          ext j
          have := Set.mem_iInter.1 h2 j
          simpa using this
        rw [hΦ, sub_eq_zero] at hzero
        simp only at hzero
        rw [← Finset.sum_coe_sort S]
        simp only [Finset.coe_mem, dite_true]
        exact hzero.symm
  rw [this]
  exact hX.image_fst_prod_pi

/-- **Every convex polytope is the solution set of a finite system of linear inequalities**,
`P = {x ∈ ℝᵈ : Ax ≤ b}` (the rows of `A` being the vectors `aᵢ`). -/
theorem exists_solSet_of_isConvexPolytope {P : Set (Rd d)} (hP : IsConvexPolytope P) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → Rd d) (b : ι → ℝ), P = solSet a b := by
  obtain ⟨S, rfl⟩ := hP
  obtain ⟨ι, _, f, b, hfb⟩ := isPolyhedral_convexHull S
  refine ⟨ι, inferInstance, fun i => (InnerProductSpace.toDual ℝ (Rd d)).symm
    (LinearMap.toContinuousLinearMap (f i)), b, ?_⟩
  rw [hfb]
  ext x
  simp [solSet, InnerProductSpace.toDual_symm_apply]

/-- **Convex polytopes are exactly the bounded solution sets of finite systems of linear
inequalities.** -/
theorem isConvexPolytope_iff {P : Set (Rd d)} :
    IsConvexPolytope P ↔ Bornology.IsBounded P ∧
      ∃ (ι : Type) (_ : Fintype ι) (a : ι → Rd d) (b : ι → ℝ), P = solSet a b := by
  constructor
  · intro hP
    refine ⟨?_, exists_solSet_of_isConvexPolytope hP⟩
    obtain ⟨S, rfl⟩ := hP
    exact (S.finite_toSet.isCompact_convexHull ℝ).isBounded
  · rintro ⟨hb, ι, _, a, b, rfl⟩
    exact isConvexPolytope_solSet a b hb

end VtoH

end Chapter10

end Part_MinkowskiWeyl
