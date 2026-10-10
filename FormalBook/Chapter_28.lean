/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import FormalBook.Mathlib.EdgeFinset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

@[expose] public section

/-!
# Chapter 28: Pigeon-hole and double counting

A proposed formalization of Chapter 28 of *Proofs from THE BOOK* (Aigner–Ziegler).
The supplied proofs are undergoing verification with the repository's pinned Lean toolchain.

* Pigeon-hole principle, including the strong form (1).
* 1. Numbers: Claims 1 and 2, and the sharpness examples.
* 2. Sequences: Erdős–Szekeres (book proof), sharpness for `mn` numbers, the dimension of `Kₙ`
  (`dim K₃ = dim K₄ = 3`, `dim K₁₂ ≤ 4`, monotonicity, and `dim(Kₙ) ≥ log₂ log₂ n`).
* 3. Sums: contiguous block sums divisible by `n`.
* Double counting (3).
* 4. Numbers again: `Hₙ − 1 < t̄(n) ≤ Hₙ` and `log n − 1 < t̄(n) < log n + 1`.
* 5. Graphs: handshaking lemma (4), Reiman's bound (6) for `C₄`-free graphs, the graph `Gp`
  (no `C₄`, `p² + p + 1` vertices, degrees, the trace argument giving `p + 1` points on the
  conic, `p²` solutions of `x² + y² + z² = 0`, and `|E(Gp)| = (n−1)/4 · (1 + √(4n−3))`).
* 6. Sperner's lemma (double-counting proof, abstract form and for the standard
  triangulation) and Brouwer's fixed point theorem for `n = 2` (and `n = 1`).
-/

/-! ===================== Part: Basic ===================== -/

/-!
# Pigeon-hole and double counting — basic results

Sections 1, 3, the double counting principle, Section 4 (numbers again) and the
first part of Section 5 (graphs) of Chapter 28.
-/


namespace chapter28

/-- Reduce an `if` whose condition holds. -/
theorem ite_of_pos {α : Sort*} {c : Prop} [Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a := by
  simp [hc]

/-- Reduce an `if` whose condition fails. -/
theorem ite_of_neg {α : Sort*} {c : Prop} [Decidable c] (hc : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  simp [hc]

/-- Reduce a dependent `if` whose condition fails. -/
theorem dite_of_neg {α : Sort*} {c : Prop} [Decidable c] (hc : ¬ c) (a : c → α) (b : ¬ c → α) :
    (if h : c then a h else b h) = b hc := by
  simp [hc]

theorem pigeon_hole_principle (n r : ℕ) (h : r < n) (object_to_boxes : Fin n → Fin r) :
  ∃ box : Fin r, ∃ object₁ object₂ : Fin n,
  object₁ ≠ object₂ ∧
  object_to_boxes object₁ = box ∧
  object_to_boxes object₂ = box := by
  have ⟨object₁, object₂, h_object⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt object_to_boxes (by convert h <;> simp)
  use object_to_boxes object₁
  use object₁
  use object₂
  tauto



variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v

/-- **Handshaking lemma**: The sum of vertex degrees equals twice the number of edges.

This is also available in Mathlib as `SimpleGraph.sum_degrees_eq_twice_card_edges`,
which uses darts (oriented edges) as the intermediate counting object. Our proof
follows the book's double-counting argument more faithfully: we count incidence
pairs (v, e) with v ∈ e, swap the summation order via
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`, then observe each edge
contributes exactly 2. -/
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  calc  ∑ v, d(v)
    _ = ∑ v, #I(v)             := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v, #{e ∈ E | v ∈ e}  := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ E, #{v | v ∈ e}  := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ e ∈ E, 2             := Finset.sum_congr rfl (λ e he ↦ by
      induction e using Sym2.ind with | h x y =>
      have hne : x ≠ y := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
      have : ({v | v ∈ s(x, y)} : Finset α) = {x, y} := by
        ext v; simp
      rw [this, Finset.card_pair hne])
    _ = 2 * ∑ e ∈ E, 1         := (Finset.mul_sum E (λ _ ↦ 1) 2).symm
    _ = 2 * #E                 := by rw [Finset.card_eq_sum_ones E]

section claims

/-- **Claim 1 (Coprime pair):** From any n+1 numbers in {0,...,2n-1} (representing {1,...,2n}),
two must be coprime (as values +1). -/
theorem claim1_coprime (n : ℕ)
    (S : Finset (Fin (2 * n))) (hS : n < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Coprime (a.val + 1) (b.val + 1) := by
  let box : Fin (2 * n) → Fin n := fun x => ⟨x.val / 2, by omega⟩
  obtain ⟨a, ha, b, hb, hab, hbox⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := box) (by simpa using hS) (fun x _ => Finset.mem_univ _)
  refine ⟨a, ha, b, hb, hab, ?_⟩
  have hq : a.val / 2 = b.val / 2 := by
    have := congr_arg Fin.val hbox; simpa using this
  -- Same box ⇒ consecutive values ⇒ coprime
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · have hcons : b.val = a.val + 1 := by omega
    rw [hcons]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  · have hcons : a.val = b.val + 1 := by omega
    rw [hcons]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm

/
-- Claim 2: From {1, 2, ..., 2n}, any n+1 chosen numbers contain two where one divides the other. -/
theorem claim2_divisible (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS_sub : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * n)
    (hS_card : S.card = n + 1) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  -- Map each element to its odd part (x / 2^(x.factorization 2)) then to (oddPart-1)/2.
  -- n+1 elements into n boxes → two share a box → same odd part → one divides the other.
  let op : ℕ → ℕ := fun x => x / 2 ^ (x.factorization 2)
  have hmap : ∀ x ∈ S, (op x - 1) / 2 ∈ Finset.range n := by
    intro x hx; simp [op]; have := hS_sub x hx
    exact Nat.div_lt_of_lt_mul (by have := Nat.div_le_self x (2 ^ x.factorization 2); omega)
  have hlt : (Finset.range n).card < S.card := by simp; omega
  obtain ⟨a, ha, b, hb, hne, hbox⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmap
  have ha_odd : ¬ 2 ∣ op a := Nat.not_dvd_ordCompl (by norm_num) (by have := hS_sub a ha; omega)
  have hb_odd : ¬ 2 ∣ op b := Nat.not_dvd_ordCompl (by norm_num) (by have := hS_sub b hb; omega)
  have ha_pos : 0 < op a :=
    Nat.div_pos (Nat.ordProj_le 2 (by have := hS_sub a ha; omega)) (by positivity)
  have hb_pos : 0 < op b :=
    Nat.div_pos (Nat.ordProj_le 2 (by have := hS_sub b hb; omega)) (by positivity)
  have hop_eq : op a = op b := by omega
  have hdvd : a ∣ b ∨ b ∣ a := by
    set ja := a.factorization 2; set jb := b.factorization 2
    have ha' : a = 2 ^ ja * (op a) := (Nat.ordProj_mul_ordCompl_eq_self a 2).symm
    have hb' : b = 2 ^ jb * (op b) := (Nat.ordProj_mul_ordCompl_eq_self b 2).symm
    rw [← hop_eq] at hb'
    rcases le_or_gt ja jb with hle | hlt
    · left; rw [ha', hb']; exact mul_dvd_mul_right (Nat.pow_dvd_pow 2 hle) _
    · right; rw [ha', hb']; exact mul_dvd_mul_right (Nat.pow_dvd_pow 2 hlt.le) _
  rcases hdvd with h | h
  · exact ⟨a, ha, b, hb, hne, h⟩
  · exact ⟨b, hb, a, ha, Ne.symm hne, h⟩

/-- **Claim 4 (Contiguous sum divisible by n):** Given n integers, there exists a nonempty
contiguous subsequence whose sum is divisible by n. -/
theorem claim4_contiguous_sum (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ) :
    ∃ (l r : Fin n), l ≤ r ∧ (n : ℤ) ∣ ∑ i ∈ Finset.Icc l r, a i := by
  set s : Fin (n + 1) → ℤ :=
    fun i => ∑ j : Fin n, if j.val < i.val then a j else 0 with hs_def
  have hnn : (0 : ℤ) < ↑n := by omega
  let f : Fin (n+1) → Fin n := fun i =>
    ⟨(s i % ↑n).toNat, by
      have h1 := Int.emod_nonneg (s i) (ne_of_gt hnn)
      have h2 := Int.emod_lt_of_pos (s i) hnn
      omega⟩
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hmod : s i % ↑n = s j % ↑n := by
    have h0 := congr_arg Fin.val hfij
    simp [f] at h0
    have := Int.emod_nonneg (s i) (ne_of_gt hnn)
    have := Int.emod_nonneg (s j) (ne_of_gt hnn)
    omega
  obtain ⟨i', j', hi'j', hmod'⟩ : ∃ i' j' : Fin (n+1), i' < j' ∧ s i' % ↑n = s j' % ↑n := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hmod⟩
    · exact ⟨j, i, h, hmod.symm⟩
  have hdvd : (n : ℤ) ∣ s j' - s i' := by
    rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact hmod'.symm
  have hi'_lt_n : i'.val < n := by omega
  suffices hsuff : s j' - s i' =
      ∑ k ∈ Finset.Icc (⟨i'.val, hi'_lt_n⟩ : Fin n) ⟨j'.val - 1, by omega⟩, a k by
    exact ⟨⟨i'.val, hi'_lt_n⟩, ⟨j'.val - 1, by omega⟩, by simp [Fin.le_def]; omega, hsuff ▸ hdvd⟩
  simp only [s, ← Finset.sum_sub_distrib]
  trans ∑ k : Fin n, if i'.val ≤ k.val ∧ k.val < j'.val then a k else 0
  · congr 1; ext ⟨k, hk⟩
    by_cases h1 : k < j'.val
    all_goals by_cases h2 : k < i'.val
    all_goals simp_all
    all_goals omega
  · rw [← Finset.sum_filter]; congr 1; ext ⟨k, hk⟩
    simp [Finset.mem_filter, Finset.mem_Icc, Fin.le_def]; omega


end claims

/-! ## Double Counting -/

/-- Double counting: the sum over rows of the number of related columns equals
the sum over columns of the number of related rows. This is a direct wrapper
around Mathlib's `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
theorem double_counting {α β : Type*}
    (R : Finset α) (C : Finset β) (r : α → β → Prop) [∀ a b, Decidable (r a b)] :
    (∑ p ∈ R, (Finset.bipartiteAbove r C p).card) =
    (∑ q ∈ C, (Finset.bipartiteBelow r R q).card) :=
  Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r

/-! ## 5. Graphs — C₄-free edge bound -/

/-- In a C₄-free graph, the sum of C(d(v), 2) over all vertices is at most C(n, 2).

This is the key combinatorial inequality: each pair of vertices can have at most one
common neighbor (otherwise they'd form a 4-cycle), so the number of "cherries"
(paths of length 2) is at most the number of vertex pairs. -/
theorem sum_choose_deg_le_choose_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hC4 : ∀ (a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    ∑ v : V, (G.degree v).choose 2 ≤ (Fintype.card V).choose 2 := by
  -- Each C(d(v),2) counts 2-element subsets of neighbors
  have key : ∀ v : V, (G.degree v).choose 2 = #((G.neighborFinset v).powersetCard 2) := by
    intro v; rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
  simp_rw [key]
  -- LHS = #(Σ v, (neighborFinset v).powersetCard 2)
  -- RHS = #(univ.powersetCard 2)
  calc ∑ v : V, #((G.neighborFinset v).powersetCard 2)
      = #(Finset.univ.sigma (fun v => (G.neighborFinset v).powersetCard 2)) := by
          rw [Finset.card_sigma]
    _ ≤ #((Finset.univ : Finset V).powersetCard 2) := ?_
    _ = (Fintype.card V).choose 2 := by rw [Finset.card_powersetCard, Finset.card_univ]
  -- Injection from sigma to powersetCard 2 univ
  apply Finset.card_le_card_of_injOn Sigma.snd
  · -- maps into target
    intro ⟨v, p⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powersetCard] at hx ⊢
    exact ⟨hx.2.1.trans (Finset.subset_univ _), hx.2.2⟩
  · -- injective (C₄-free condition)
    intro ⟨v₁, p₁⟩ hx₁ ⟨v₂, p₂⟩ hx₂ (hfx : p₁ = p₂)
    subst hfx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powersetCard] at hx₁
      hx₂
    have hp₁ := hx₁.2
    have hp₂ := hx₂.2
    suffices v₁ = v₂ by subst this; rfl
    by_contra hne
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hp₁.2
    have ha₁ : G.Adj v₁ a := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₁.1 (Finset.mem_insert_self a {b})
    have hb₁ : G.Adj v₁ b := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₁.1 (Finset.mem_insert.2 (Or.inr
        (Finset.mem_singleton_self b)))
    have ha₂ : G.Adj v₂ a := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₂.1 (Finset.mem_insert_self a {b})
    have hb₂ : G.Adj v₂ b := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₂.1 (Finset.mem_insert.2 (Or.inr
        (Finset.mem_singleton_self b)))
    have hv₁a : v₁ ≠ a := G.ne_of_adj ha₁
    have hv₁b : v₁ ≠ b := G.ne_of_adj hb₁
    have hv₂a : v₂ ≠ a := G.ne_of_adj ha₂
    have hv₂b : v₂ ≠ b := G.ne_of_adj hb₂
    exact hC4 v₁ a v₂ b hv₁a hne hv₁b (Ne.symm hv₂a) hab hv₂b
      ⟨ha₁, ha₂.symm, hb₂, hb₁.symm⟩

/-- If a simple graph on n vertices contains no 4-cycle (C₄), then
|E| ≤ ⌊n/4 · (1 + √(4n − 3))⌋.

The proof uses `sum_choose_deg_le_choose_card` together with the handshaking lemma
and Cauchy–Schwarz / Jensen. -/
theorem c4_free_edge_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hC4 : ∀ (a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (n : ℕ) (hn : Fintype.card V = n) :
    G.edgeFinset.card ≤ ⌊(n : ℝ) / 4 * (1 + Real.sqrt (4 * n - 3))⌋₊ := by
  -- Let e = G.edgeFinset.card
  set e := G.edgeFinset.card with he_def
  -- Step 0: Get the key inequality from C₄-free condition
  have hchoose := sum_choose_deg_le_choose_card G hC4
  -- Step 1: Cast everything to ℝ
  -- We need: (e : ℝ) ≤ n/4 * (1 + √(4n-3))
  -- Then Nat.floor gives us the result
  suffices h : (e : ℝ) ≤ (n : ℝ) / 4 * (1 + Real.sqrt (4 * (n : ℝ) - 3)) by
    exact Nat.le_floor h
  -- Step 2: From sum_choose to sum_sq bound (in ℝ)
  -- ∑ C(d(v), 2) ≤ C(n, 2) means ∑ d(v)*(d(v)-1) ≤ n*(n-1)
  -- i.e., ∑ d(v)² - ∑ d(v) ≤ n*(n-1)
  -- i.e., ∑ d(v)² ≤ n*(n-1) + 2*e  (using handshaking)
  have hhand : ∑ v : V, G.degree v = 2 * e := handshaking
  have sum_sq_bound : ∑ v : V, ((G.degree v : ℝ) ^ 2) ≤ (n : ℝ) * ((n : ℝ) - 1) + 2 * (e : ℝ) := by
    have h_real : (∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      by
      have h1 : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) - 1) = 2 * (k.choose 2 : ℝ) := by
        intro k; rw [Nat.cast_choose_two (K := ℝ)]; ring
      have hc : (∑ v : V, (G.degree v).choose 2 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) := by
        exact_mod_cast (hn ▸ hchoose)
      calc ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)
          = ∑ v : V, 2 * ((G.degree v).choose 2 : ℝ) := by simp_rw [h1]
        _ = 2 * ∑ v : V, ((G.degree v).choose 2 : ℝ) := by rw [Finset.mul_sum]
        _ ≤ 2 * ((n.choose 2 : ℕ) : ℝ) := by linarith
        _ = (n : ℝ) * ((n : ℝ) - 1) := by rw [← h1]
    -- d*(d-1) = d² - d
    have h_eq : ∀ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) =
        (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) := by intro v; ring
    simp_rw [h_eq] at h_real
    -- h_real: ∑ (d² - d) ≤ n*(n-1)
    -- i.e., ∑ d² - ∑ d ≤ n*(n-1)
    have h_sub : ∑ v : V, ((G.degree v : ℝ) ^ 2 - (G.degree v : ℝ)) =
        (∑ v : V, (G.degree v : ℝ) ^ 2) - (∑ v : V, (G.degree v : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
    rw [h_sub] at h_real
    have h5 : (∑ v : V, (G.degree v : ℝ)) = 2 * (e : ℝ) := by exact_mod_cast hhand
    linarith
  -- Step 3: Cauchy-Schwarz: (∑ d(v))² ≤ n * ∑ d(v)²
  have n_eq : Fintype.card V = n := hn
  have cauchy : (∑ v : V, (G.degree v : ℝ)) ^ 2 ≤
      (Fintype.card V : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun v : V => (G.degree v : ℝ))
    rwa [Finset.card_univ] at h
  rw [n_eq] at cauchy
  -- Step 4: Combine: (2e)² ≤ n * (n(n-1) + 2e)
  have sum_deg_real : (∑ v : V, (G.degree v : ℝ)) = 2 * (e : ℝ) := by
    exact_mod_cast hhand
  rw [sum_deg_real] at cauchy
  -- cauchy: (2*e)² ≤ n * ∑ d(v)²
  -- sum_sq_bound: ∑ d(v)² ≤ n*(n-1) + 2*e
  -- So: 4*e² ≤ n * (n*(n-1) + 2*e) = n²*(n-1) + 2*n*e
  have key : 4 * (e : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 1) + 2 * (n : ℝ) * (e : ℝ) := by
    have h1 : (2 * (e : ℝ)) ^ 2 = 4 * (e : ℝ) ^ 2 := by ring
    rw [h1] at cauchy
    calc 4 * (e : ℝ) ^ 2
        ≤ (n : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := cauchy
      _ ≤ (n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) + 2 * (e : ℝ)) := by
            apply mul_le_mul_of_nonneg_left sum_sq_bound (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ 2 * ((n : ℝ) - 1) + 2 * (n : ℝ) * (e : ℝ) := by ring
  -- Step 5: Solve quadratic: 4e² - 2ne - n²(n-1) ≤ 0
  -- e ≤ (2n + √(4n² + 16n²(n-1))) / 8 = (2n + 2n√(4n-3)) / 8 = n/4 * (1 + √(4n-3))
  -- Equivalently: e ≤ n/4 * (1 + √(4n-3))
  -- This means: 4e ≤ n * (1 + √(4n-3))
  -- i.e., 4e - n ≤ n * √(4n-3)
  -- Squaring (if 4e - n ≤ 0, done; otherwise): (4e - n)² ≤ n² * (4n - 3)
  -- (4e-n)² = 16e² - 8ne + n² ≤ 4n²(n-1) + 8ne - 8ne + n² = 4n³ - 4n² + n² = 4n³ - 3n²
  -- = n²(4n-3) ✓
  by_cases hn0 : n = 0
  · subst hn0
    have hcard : Fintype.card V = 0 := hn
    have he0 : e = 0 := by
      rw [he_def]
      have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
      rw [hcard] at h
      have : Nat.choose 0 2 = 0 := by decide
      rw [this] at h; omega
    simp [he0]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  -- We want: e ≤ n/4 * (1 + √(4n-3))
  -- Suffices: 4*e ≤ n + n * √(4n-3)
  suffices h4e : 4 * (e : ℝ) ≤ (n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) by
    linarith [mul_comm ((n : ℝ) / 4) (1 + Real.sqrt (4 * (n : ℝ) - 3)),
              show (n : ℝ) / 4 * (1 + Real.sqrt (4 * (n : ℝ) - 3)) =
                ((n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3)) / 4 by ring]
  -- If 4e ≤ n, done since n * √(4n-3) ≥ 0
  by_cases h4e_le : 4 * (e : ℝ) ≤ (n : ℝ)
  · linarith [mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg (4 * (n : ℝ) - 3))]
  push Not at h4e_le
  -- Otherwise 4e > n, so 4e - n > 0. We square both sides.
  rw [show 4 * (e : ℝ) ≤ (n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) ↔
      4 * (e : ℝ) - (n : ℝ) ≤ (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) by constructor <;> intro h <;>
        linarith]
  -- Need: 4n - 3 ≥ 0 for sqrt to be meaningful
  have h4n3 : (0 : ℝ) ≤ 4 * (n : ℝ) - 3 := by
    have : 1 ≤ n := Nat.pos_of_ne_zero hn0
    linarith [show (1 : ℝ) ≤ (n : ℝ) from Nat.one_le_cast.mpr this]
  -- Square both sides (LHS > 0, RHS ≥ 0)
  have hlhs_pos : 0 < 4 * (e : ℝ) - (n : ℝ) := by linarith
  -- Suffices to show (4e - n)² ≤ n² * (4n - 3)
  -- Then take sqrt of both sides
  have hsq : (4 * (e : ℝ) - (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 * (4 * (n : ℝ) - 3) := by
    nlinarith [sq_nonneg (e : ℝ), sq_nonneg (n : ℝ),
               show (0 : ℝ) ≤ (e : ℝ) from Nat.cast_nonneg e,
               show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hrhs_nn : 0 ≤ (n : ℝ) ^ 2 * (4 * (n : ℝ) - 3) := by
    apply mul_nonneg (sq_nonneg _) h4n3
  calc 4 * (e : ℝ) - (n : ℝ)
      ≤ |4 * (e : ℝ) - (n : ℝ)| := le_abs_self _
    _ = Real.sqrt ((4 * (e : ℝ) - (n : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) ^ 2 * (4 * (n : ℝ) - 3)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((n : ℝ) ^ 2) * Real.sqrt (4 * (n : ℝ) - 3) :=
        Real.sqrt_mul (sq_nonneg _) _
    _ = (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) := by
        rw [Real.sqrt_sq (le_of_lt hn_pos)]

/-! ## 4. Numbers again -/

/-- **Double counting for divisor sums:**
    Σ_{j=1}^{n} (number of divisors of j) = Σ_{i=1}^{n} ⌊n/i⌋.

    Both sides count pairs (i, j) with 1 ≤ i ≤ n, 1 ≤ j ≤ n, and i ∣ j.
    LHS groups by j (divisors of j), RHS groups by i (multiples of i up to n). -/
theorem sum_divisor_count (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card = ∑ i ∈ Finset.Icc 1 n, n / i := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (· ∣ ·)
    (s := Finset.Icc 1 n) (t := Finset.Icc 1 n)
  suffices h1 : ∀ i ∈ Finset.Icc 1 n,
      (Finset.bipartiteAbove (· ∣ ·) (Finset.Icc 1 n) i).card = n / i by
    suffices h2 : ∀ j ∈ Finset.Icc 1 n,
        (Finset.bipartiteBelow (· ∣ ·) (Finset.Icc 1 n) j).card = (Nat.divisors j).card by
      rw [← Finset.sum_congr rfl h1, key, Finset.sum_congr rfl h2]
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hj0 : j ≠ 0 := by omega
      congr 1
      simp only [Finset.bipartiteBelow]
      rw [← Nat.filter_dvd_eq_divisors hj0]
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨hd1, hdn⟩, hdj⟩
        exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hdj), hdj⟩
      · rintro ⟨hd_lt, hdj⟩
        refine ⟨⟨?_, ?_⟩, hdj⟩
        · by_contra h; push Not at h; interval_cases d; simp at hdj; exact hj0 hdj
        · exact le_trans (Nat.le_of_dvd (by omega) hdj) hj.2
  · intro i hi
    have hioc : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext x; simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.lt_iff_add_one_le]
    rw [show Finset.bipartiteAbove (· ∣ ·) (Finset.Icc 1 n) i =
        {j ∈ Finset.Icc 1 n | i ∣ j} from rfl, ← hioc]
    exact Nat.Ioc_filter_dvd_card_eq_div n i

/-- The average number of divisors is bounded by the harmonic sum:
  `∑ j in [1,n], t(j) ≤ n * Hₙ` where `t(j) = #(divisors j)` and `Hₙ = ∑ 1/i`. -/
theorem avg_divisor_count_le_harmonic (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) ≤
    ↑n * ∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / ↑i := by
  have h := sum_divisor_count n
  have : (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (n / i : ℤ) := by exact_mod_cast h
  calc (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ)
      = ∑ i ∈ Finset.Icc 1 n, (↑(n / i) : ℚ) := by exact_mod_cast this
    _ ≤ ∑ i ∈ Finset.Icc 1 n, ↑n / ↑i := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.cast_div_le
    _ = ↑n * ∑ i ∈ Finset.Icc 1 n, 1 / ↑i := by
        rw [Finset.mul_sum]
        congr 1; ext i; ring

/-- Lower bound: ∑ t(j) > n·Hₙ − n, i.e., t̄(n) > Hₙ − 1 > log n − 1. -/
theorem avg_divisor_count_lower_bound (n : ℕ) (hn : 0 < n) :
    ↑n * ∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / ↑i - ↑n <
    (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) := by
  have h := sum_divisor_count n
  have hrw : (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) =
      ∑ i ∈ Finset.Icc 1 n, (↑(n / i) : ℚ) := by exact_mod_cast h
  rw [hrw, Finset.mul_sum]
  have hsize : (Finset.Icc 1 n).card = n := by simp [Nat.card_Icc]
  suffices h_diff : ∑ i ∈ Finset.Icc 1 n, (↑n * (1 / ↑i) - ↑(n / i) : ℚ) < ↑n by
    have := Finset.sum_sub_distrib (s := Finset.Icc 1 n)
      (f := fun i => ↑n * (1 / (↑i : ℚ))) (g := fun i => (↑(n / i) : ℚ))
    linarith
  calc ∑ i ∈ Finset.Icc 1 n, (↑n * (1 / ↑i) - ↑(n / i) : ℚ)
      < ∑ _i ∈ Finset.Icc 1 n, (1 : ℚ) := by
        apply Finset.sum_lt_sum
        · intro i hi
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hi_pos : (0 : ℚ) < ↑i := by positivity
          -- Need: n * (1/i) - ↑(n/i) ≤ 1
          -- i.e. n/i - 1 ≤ ↑(n/i), i.e. n/i < ↑(n/i) + 1 + 1... no.
          -- n * (1/i) - ↑(n/i) ≤ 1
          -- ↔ n/i ≤ ↑(n/i) + 1
          -- ↔ n ≤ (↑(n/i) + 1) * i  (since i > 0)
          -- This follows from Nat.lt_div_mul_add: n < n/i * i + i = (n/i) * i + i
          -- So n ≤ (n/i) * i + i - 1 < (n/i + 1) * i
          rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hi_pos]
          have h1 := Nat.lt_div_mul_add (a := n) (by omega : 0 < i)
          have h2 : (↑n : ℚ) < ↑(n / i) * ↑i + ↑i := by exact_mod_cast h1
          linarith
        · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hn⟩, by simp [Nat.div_one]⟩
    _ = ↑n := by simp [hsize]


end chapter28

/-! ===================== Part: PigeonHole ===================== -/

/-!
# The pigeon-hole principle: strong form and sharpness of the claims in Section 1
-/

namespace chapter28

open Finset

/-- **Pigeon-hole principle, strong form (1).** If `f : N → R` with `|R| = r > 0` and
`|N| = n`, then some `a ∈ R` has `|f⁻¹(a)| ≥ ⌈n / r⌉`. -/
theorem pigeon_hole_strong {N R : Type*} [Fintype N] [Fintype R] [DecidableEq R]
    (hR : 0 < Fintype.card R) (f : N → R) :
    ∃ a : R, ⌈(Fintype.card N : ℚ) / Fintype.card R⌉₊ ≤ (univ.filter (fun x => f x = a)).card := by
  by_contra h
  push Not at h
  -- otherwise every fibre has fewer than `n / r` elements …
  have hlt : ∀ a : R, ((univ.filter (fun x => f x = a)).card : ℚ) <
      (Fintype.card N : ℚ) / Fintype.card R := fun a => Nat.lt_ceil.1 (h a)
  have hne : (univ : Finset R).Nonempty := univ_nonempty_iff.2 (Fintype.card_pos_iff.1 hR)
  -- … and hence `n = ∑ₐ |f⁻¹(a)| < r · (n / r) = n`, which cannot be.
  have hsum : (Fintype.card N : ℚ) = ∑ a : R, ((univ.filter (fun x => f x = a)).card : ℚ) := by
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun x _ => mem_univ (f x))]
    simp
  have := Finset.sum_lt_sum_of_nonempty hne (fun a _ => hlt a)
  rw [← hsum, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ (by positivity)] at this
  exact lt_irrefl _ this

/-- Sharpness of Claim 1: `{2, 4, …, 2n}` has `n` elements, no two of which are relatively prime.
(Numbers in `{1, …, 2n}` are represented as `a + 1` for `a : Fin (2n)`.) -/
theorem claim1_sharp (n : ℕ) :
    ∃ S : Finset (Fin (2 * n)), S.card = n ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ Nat.Coprime (a.val + 1) (b.val + 1) := by
  refine ⟨(univ : Finset (Fin n)).map ⟨fun i => ⟨2 * i.val + 1, by omega⟩, ?_⟩, ?_, ?_⟩
  · intro i j h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · simp
  · intro a ha b hb _ hcop
    simp only [mem_map, mem_univ, true_and] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    have h2 : 2 ∣ Nat.gcd (2 * i.val + 1 + 1) (2 * j.val + 1 + 1) :=
      Nat.dvd_gcd ⟨i.val + 1, by ring⟩ ⟨j.val + 1, by ring⟩
    have h3 : Nat.gcd (2 * i.val + 1 + 1) (2 * j.val + 1 + 1) = 1 := hcop
    rw [h3] at h2
    omega

/-- Sharpness of Claim 2: `{n + 1, n + 2, …, 2n}` has `n` elements, none of which divides
another one. -/
theorem claim2_sharp (n : ℕ) :
    ∃ S : Finset ℕ, (∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * n) ∧ S.card = n ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b := by
  refine ⟨Finset.Icc (n + 1) (2 * n), ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_Icc] at hx
    omega
  · simp; omega
  · intro a ha b hb hab hdvd
    simp only [mem_Icc] at ha hb
    obtain ⟨c, rfl⟩ := hdvd
    rcases c with _ | _ | c
    · omega
    · simp at hab
    · nlinarith

end chapter28

/-! ===================== Part: ErdosSzekeres ===================== -/

/-!
# Section 2 of Chapter 28: Sequences

* The Erdős–Szekeres theorem on monotone subsequences, with the book's proof
  (label every element by the length of a longest increasing subsequence starting there,
  and apply the pigeon-hole principle in the strong form (1)).
* The sharpness remark: for `mn` numbers the statement fails in general.
* The dimension of the complete graph `Kₙ` and the bound `dim(Kₙ) ≥ log₂ log₂ n`.
-/

namespace chapter28

open Finset

section ErdosSzekeres

variable {ι : Type*} [LinearOrder ι] [DecidableEq ι]

open Classical in
/-- The increasing subsequences (inside `S`) starting at `i`. -/
noncomputable def incSeqs (f : ι → ℝ) (S : Finset ι) (i : ι) : Finset (Finset ι) :=
  S.powerset.filter (fun t : Finset ι => i ∈ t ∧ (∀ j ∈ t, i ≤ j) ∧ StrictMonoOn f (t : Set ι))

lemma mem_incSeqs {f : ι → ℝ} {S : Finset ι} {i : ι} {t : Finset ι} :
    t ∈ incSeqs f S i ↔ t ⊆ S ∧ i ∈ t ∧ (∀ j ∈ t, i ≤ j) ∧ StrictMonoOn f (t : Set ι) := by
  simp [incSeqs]

/-- The length `tᵢ` of a longest increasing subsequence (inside `S`) starting at `i`. -/
noncomputable def incLen (f : ι → ℝ) (S : Finset ι) (i : ι) : ℕ :=
  (incSeqs f S i).sup Finset.card

lemma incLen_spec (f : ι → ℝ) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    ∃ t ⊆ S, i ∈ t ∧ (∀ j ∈ t, i ≤ j) ∧ StrictMonoOn f (t : Set ι) ∧
      t.card = incLen f S i := by
  have hne : (incSeqs f S i).Nonempty := ⟨{i}, mem_incSeqs.2 (by simp [hi])⟩
  obtain ⟨t, ht, hteq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨h1, h2, h3, h4⟩ := mem_incSeqs.1 ht
  exact ⟨t, h1, h2, h3, h4, hteq.symm⟩

lemma le_incLen (f : ι → ℝ) (S : Finset ι) {i : ι} {t : Finset ι} (htS : t ⊆ S)
    (hit : i ∈ t) (hmin : ∀ j ∈ t, i ≤ j) (hmono : StrictMonoOn f (t : Set ι)) :
    t.card ≤ incLen f S i :=
  Finset.le_sup (f := Finset.card) (mem_incSeqs.2 ⟨htS, hit, hmin, hmono⟩)

lemma one_le_incLen (f : ι → ℝ) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    1 ≤ incLen f S i := by
  simpa using le_incLen f S (t := {i}) (by simpa using hi) (by simp) (by simp) (by simp)

/-- The key observation: if `i < j` and `aᵢ < aⱼ`, then `tᵢ > tⱼ`. -/
lemma incLen_lt_of_lt (f : ι → ℝ) (S : Finset ι) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i < j) (hf : f i < f j) : incLen f S j < incLen f S i := by
  obtain ⟨t, htS, hjt, hmin, hmono, hcard⟩ := incLen_spec f S hj
  have hit : i ∉ t := fun h => (lt_irrefl _ (lt_of_lt_of_le hij (hmin i h)))
  have := le_incLen f S (t := insert i t) (Finset.insert_subset hi htS) (Finset.mem_insert_self _ _)
    (by
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact le_rfl
      · exact hij.le.trans (hmin k hk))
    (by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd hab (lt_irrefl _)
      · rcases (hmin b hb).lt_or_eq with h | h
        · exact hf.trans (hmono (Finset.mem_coe.2 hjt) (Finset.mem_coe.2 hb) h)
        · subst h; exact hf
      · exact absurd (hab.trans_le ((hij.le.trans (hmin a ha)))) (lt_irrefl _)
      · exact hmono ha hb hab)
  rw [Finset.card_insert_of_notMem hit, hcard] at this
  omega

/-- **Erdős–Szekeres (book proof), finset version.** If `f` is injective on a finite set `S`
of indices with `|S| > m n`, then there is an increasing subsequence of length `m + 1` or a
decreasing subsequence of length `n + 1`. -/
theorem erdos_szekeres_book (m n : ℕ) (f : ι → ℝ) (S : Finset ι)
    (hf : Set.InjOn f (S : Set ι)) (hS : m * n < S.card) :
    (∃ t ⊆ S, m < t.card ∧ StrictMonoOn f (t : Set ι)) ∨
    (∃ t ⊆ S, n < t.card ∧ StrictAntiOn f (t : Set ι)) := by
  by_cases h : ∃ i ∈ S, m + 1 ≤ incLen f S i
  · obtain ⟨i, hi, hlen⟩ := h
    obtain ⟨t, htS, -, -, hmono, hcard⟩ := incLen_spec f S hi
    exact Or.inl ⟨t, htS, by omega, hmono⟩
  · push Not at h
    -- the labels `tᵢ` take values in `{1, …, m}`
    have hmaps : ∀ i ∈ S, incLen f S i ∈ Finset.Icc 1 m := fun i hi =>
      Finset.mem_Icc.2 ⟨one_le_incLen f S hi, by have := h i hi; omega⟩
    obtain ⟨s, -, hs⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
      (by simpa [Nat.card_Icc] using hS)
    refine Or.inr ⟨S.filter (fun i => incLen f S i = s), Finset.filter_subset _ _, hs, ?_⟩
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    rcases lt_trichotomy (f a) (f b) with hlt | heq | hgt
    · have := incLen_lt_of_lt f S ha.1 hb.1 hab hlt
      omega
    · exact absurd (hf ha.1 hb.1 heq) hab.ne
    · exact hgt

end ErdosSzekeres

/-- **Claim 3 (Erdős–Szekeres):** In any sequence `a₁, …, a_{mn+1}` of `mn + 1` distinct real
numbers there is an increasing subsequence of length `m + 1` or a decreasing subsequence of
length `n + 1` (or both). -/
theorem claim3_erdos_szekeres (m n : ℕ) (f : Fin (m * n + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (m * n + 1)), m < t.card ∧ StrictMonoOn f t) ∨
    (∃ t : Finset (Fin (m * n + 1)), n < t.card ∧ StrictAntiOn f t) := by
  rcases erdos_szekeres_book m n f Finset.univ hf.injOn (by simp) with
    ⟨t, -, h1, h2⟩ | ⟨t, -, h1, h2⟩
  · exact Or.inl ⟨t, h1, h2⟩
  · exact Or.inr ⟨t, h1, h2⟩

/-- The counterexample sequence of length `mn` used for the sharpness remark:
`n` decreasing blocks, each block an increasing run of length `m`. -/
def esSharpSeq (m : ℕ) (x : ℕ) : ℝ := (x % m : ℕ) - (m : ℝ) * (x / m : ℕ)

/-- **Sharpness remark.** For `mn` numbers the Erdős–Szekeres statement is no longer true in
general: the sequence `esSharpSeq` of length `m n` is injective and has neither an increasing
subsequence of length `m + 1` nor a decreasing subsequence of length `n + 1`. -/
theorem erdos_szekeres_sharp (m n : ℕ) :
    Function.Injective (fun x : Fin (m * n) => esSharpSeq m x) ∧
    (∀ t : Finset (Fin (m * n)), StrictMonoOn (fun x : Fin (m * n) => esSharpSeq m x) t →
      t.card ≤ m) ∧
    (∀ t : Finset (Fin (m * n)), StrictAntiOn (fun x : Fin (m * n) => esSharpSeq m x) t →
      t.card ≤ n) := by
  -- key comparison: different blocks are ordered decreasingly
  have hm : ∀ x : Fin (m * n), 0 < m := fun x => by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd x.2 (by simp)
    · exact h
  have block_lt : ∀ x y : ℕ, 0 < m → x / m < y / m → esSharpSeq m y < esSharpSeq m x := by
    intro x y hm0 hxy
    unfold esSharpSeq
    have h1 : ((y % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt _ hm0
    have h2 : (0 : ℝ) ≤ ((x % m : ℕ) : ℝ) := by positivity
    have h3 : ((x / m : ℕ) : ℝ) + 1 ≤ ((y / m : ℕ) : ℝ) := by exact_mod_cast hxy
    nlinarith
  have same_block : ∀ x y : ℕ, x / m = y / m → x < y → esSharpSeq m x < esSharpSeq m y := by
    intro x y hxy hlt
    unfold esSharpSeq
    rw [hxy]
    have : x % m < y % m := by
      have := Nat.div_add_mod x m; have := Nat.div_add_mod y m
      nlinarith
    have : ((x % m : ℕ) : ℝ) < ((y % m : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    by_contra hne
    simp only at hxy
    rcases lt_trichotomy (x.val / m) (y.val / m) with h | h | h
    · exact (block_lt _ _ (hm x) h).ne' hxy
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
      · exact (same_block _ _ h h').ne hxy
      · exact (same_block _ _ h.symm h').ne' hxy
    · exact (block_lt _ _ (hm x) h).ne hxy
  · intro t ht
    rcases t.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
    · simp
    -- all elements lie in one block, and the map `x ↦ x % m` is injective on `t`
    have hblock : ∀ x ∈ t, ∀ y ∈ t, x.val / m = y.val / m := by
      intro x hx y hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hxy : x < y := by
          rw [Fin.lt_def]; by_contra h'; push Not at h'
          exact absurd (Nat.div_le_div_right h') (not_le.2 h)
        exact (block_lt _ _ (hm x) h).not_gt (ht hx hy hxy)
      · have hxy : y < x := by
          rw [Fin.lt_def]; by_contra h'; push Not at h'
          exact absurd (Nat.div_le_div_right h') (not_le.2 h)
        exact (block_lt _ _ (hm x) h).not_gt (ht hy hx hxy)
    calc t.card ≤ (Finset.range m).card := by
          apply Finset.card_le_card_of_injOn (fun x => x.val % m)
          · intro x _; simpa using Nat.mod_lt _ (hm x)
          · intro x hx y hy hxy
            apply Fin.ext
            rw [← Nat.div_add_mod x.val m, ← Nat.div_add_mod y.val m]
            simp only at hxy
            rw [hblock x hx y hy, hxy]
      _ = m := Finset.card_range m
  · intro t ht
    calc t.card ≤ (Finset.range n).card := by
          apply Finset.card_le_card_of_injOn (fun x => x.val / m)
          · intro x _
            simp only [Finset.coe_range, Set.mem_Iio]
            exact Nat.div_lt_of_lt_mul x.2
          · intro x hx y hy hxy
            by_contra hne
            simp only at hxy
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
            · exact (same_block _ _ hxy h').not_gt (ht hx hy h')
            · exact (same_block _ _ hxy.symm h').not_gt (ht hy hx h')
      _ = n := Finset.card_range n

end chapter28

/-! ===================== Part: KnDimension ===================== -/

/-!
# The dimension of the complete graph `Kₙ` (Section 2 of Chapter 28)

Let `N = {1, …, n}`. Permutations `π₁, …, πₘ` of `N` *represent* `Kₙ` if for every three
distinct numbers `i, j, k` there is a permutation in which `k` comes after both `i` and `j`.
The dimension `dim(Kₙ)` is the smallest such `m`. We encode a permutation by its
*position function* `σ : Equiv.Perm (Fin n)`, where `σ x` is the position of `x`.

Main results:
* `dimK_mono` : `dim(Kₙ) ≤ dim(Kₙ₊₁)`;
* `dimK_three`, `dimK_four` : `dim(K₃) = dim(K₄) = 3`;
* `dimK_twelve_le` : the four permutations from the margin represent `K₁₂`;
* `dimK_ge_log_log` : `dim(Kₙ) ≥ log₂ log₂ n` (inequality (2)).
-/

namespace chapter28

namespace KnDimension

/-- **Erdős-Szekeres on finsets**: Given a finset S of size > m² and a function f injective
    on S, there exists a subset T ⊆ S of size > m on which f is monotone. -/
theorem erdos_szekeres_finset {n m : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n))
    (hcard : m * m < S.card) (hf : Set.InjOn f (↑S : Set (Fin n))) :
    ∃ T ⊆ S, m < T.card ∧
      (StrictMonoOn f (↑T : Set (Fin n)) ∨ StrictAntiOn f (↑T : Set (Fin n))) := by
  rcases erdos_szekeres_book m m f S hf hcard with ⟨T, hTS, hT, hm⟩ | ⟨T, hTS, hT, ha⟩
  · exact ⟨T, hTS, hT, Or.inl hm⟩
  · exact ⟨T, hTS, hT, Or.inr ha⟩

/-- **Iterated Erdős-Szekeres**: Given p injective functions on Fin n and a finset S
    with |S| > 2^(2^p), there exists a subset T ⊆ S with |T| > 2 that is simultaneously
    monotone (each function is either strictly increasing or strictly decreasing on T). -/
theorem iterated_erdos_szekeres :
    ∀ (p : ℕ) {n : ℕ} (fs : Fin p → (Fin n → ℝ)) (S : Finset (Fin n)),
    (∀ i, Set.InjOn (fs i) (↑S : Set (Fin n))) →
    2 ^ 2 ^ p < S.card →
    ∃ T ⊆ S, 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) (↑T : Set (Fin n)) ∨
                    StrictAntiOn (fs i) (↑T : Set (Fin n))
  | 0, _, _, S, _, hS => by
    simp only [Nat.pow_zero, pow_one] at hS
    exact ⟨S, Finset.Subset.refl S, hS, fun i => i.elim0⟩
  | p + 1, _, fs, S, hfs, hS => by
    have harith : 2 ^ 2 ^ p * (2 ^ 2 ^ p) < S.card := by
      have h : 2 ^ 2 ^ (p + 1) = 2 ^ 2 ^ p * (2 ^ 2 ^ p) := by
        rw [pow_succ, pow_mul, sq]
      linarith
    obtain ⟨T₁, hT₁S, hT₁card, hT₁mono⟩ :=
      erdos_szekeres_finset (fs 0) S harith (hfs 0)
    have hfs' : ∀ i : Fin p, Set.InjOn (fs i.succ) (↑T₁ : Set (Fin _)) :=
      fun i => (hfs i.succ).mono (Finset.coe_subset.mpr hT₁S)
    obtain ⟨T₂, hT₂T₁, hT₂card, hT₂mono⟩ :=
      iterated_erdos_szekeres p (fun i => fs i.succ) T₁ hfs' hT₁card
    refine ⟨T₂, hT₂T₁.trans hT₁S, hT₂card, ?_⟩
    intro ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      rcases hT₁mono with h | h
      · exact Or.inl (h.mono (Finset.coe_subset.mpr hT₂T₁))
      · exact Or.inr (h.mono (Finset.coe_subset.mpr hT₂T₁))
    | i + 1, hi =>
      exact hT₂mono ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- **Simultaneous monotone triple**: For n > 2^(2^p) and p injective functions
    Fin n → ℝ, there exists a subset of size > 2 that is monotone for all of them.

    This captures the lower bound dim(Kₙ) ≥ ⌈log₂(⌈log₂ n⌉)⌉: fewer than
    ⌈log₂(⌈log₂ n⌉)⌉ linear orders cannot separate all triples. -/
theorem kn_dimension_bound (p n : ℕ) (hn : 2 ^ 2 ^ p < n)
    (fs : Fin p → (Fin n → ℝ)) (hfs : ∀ i, Function.Injective (fs i)) :
    ∃ T : Finset (Fin n), 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) ↑T ∨ StrictAntiOn (fs i) ↑T := by
  have huniv : 2 ^ 2 ^ p < (Finset.univ : Finset (Fin n)).card := by
    simp [Finset.card_univ, Fintype.card_fin]; exact hn
  obtain ⟨T, _, hT_card, hT_mono⟩ := iterated_erdos_szekeres p fs Finset.univ
    (fun i => (hfs i).injOn) huniv
  exact ⟨T, hT_card, hT_mono⟩

/-- **Ceiling-log formulation**: If p < ⌈log₂(⌈log₂ n⌉)⌉, then p injective functions
    on Fin n cannot separate all triples. This is the dim(Kₙ) ≥ ⌈log₂(⌈log₂ n⌉)⌉ bound. -/
theorem kn_dimension_clog_bound (n p : ℕ) (hp : p < Nat.clog 2 (Nat.clog 2 n))
    (fs : Fin p → (Fin n → ℝ)) (hfs : ∀ i, Function.Injective (fs i)) :
    ∃ T : Finset (Fin n), 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) ↑T ∨ StrictAntiOn (fs i) ↑T := by
  apply kn_dimension_bound _ _ _ _ hfs
  exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mp
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mp hp)

end KnDimension

open Finset

/-- The permutations `π 0, …, π (m-1)` of `Fin n` *represent* `Kₙ`: for every three distinct
`i, j, k` there is a permutation in which `k` comes after both `i` and `j`. Each permutation
is encoded by its position function (`π l x` is the position of `x` in the `l`-th ordering). -/
def RepresentsK (n m : ℕ) (π : Fin m → Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → ∃ l, π l i < π l k ∧ π l j < π l k

/-- The same notion for orderings given by arbitrary (injective) rankings into `ℕ`. -/
def RepresentsKRank (n m : ℕ) (r : Fin m → Fin n → ℕ) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → ∃ l, r l i < r l k ∧ r l j < r l k

instance (n m : ℕ) (r : Fin m → Fin n → ℕ) : Decidable (RepresentsKRank n m r) := by
  unfold RepresentsKRank; infer_instance

/-- An injective ranking of `Fin n` is induced by a permutation (its position function). -/
lemma exists_perm_of_injective {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin n), ∀ x y, σ x < σ y ↔ f x < f y := by
  classical
  set s := (univ : Finset (Fin n)).image f
  have hs : s.card = n := by simp [s, card_image_of_injective _ hf]
  let e := s.orderIsoOfFin hs
  let g : Fin n → Fin n := fun x => e.symm ⟨f x, mem_image_of_mem f (mem_univ x)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    simpa [g] using congrArg Subtype.val (e.symm.injective hxy)
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun x y => ?_⟩
  simp only [Equiv.ofBijective_apply, g, OrderIso.lt_iff_lt]
  exact Subtype.mk_lt_mk

/-- The dimension `dim(Kₙ)`: the smallest number of permutations representing `Kₙ`. -/
noncomputable def dimK (n : ℕ) : ℕ :=
  sInf {m | ∃ π : Fin m → Equiv.Perm (Fin n), RepresentsK n m π}

lemma representsK_of_rank {n m : ℕ} (r : Fin m → Fin n → ℕ) (hr : ∀ l, Function.Injective (r l))
    (h : RepresentsKRank n m r) : ∃ π : Fin m → Equiv.Perm (Fin n), RepresentsK n m π := by
  choose σ hσ using fun l => exists_perm_of_injective (r l) (hr l)
  refine ⟨σ, fun i j k hij hik hjk => ?_⟩
  obtain ⟨l, h1, h2⟩ := h i j k hij hik hjk
  exact ⟨l, (hσ l i k).2 h1, (hσ l j k).2 h2⟩

lemma dimK_le_of_rank {n m : ℕ} (r : Fin m → Fin n → ℕ) (hr : ∀ l, Function.Injective (r l))
    (h : RepresentsKRank n m r) : dimK n ≤ m :=
  Nat.sInf_le (representsK_of_rank r hr h)

/-- `Kₙ` is always represented by `n` permutations (put each `k` last once). -/
lemma dimK_le_self (n : ℕ) : dimK n ≤ n := by
  classical
  apply dimK_le_of_rank (fun l x => if x = l then n else x.val)
  · intro l x y hxy
    simp only at hxy
    split_ifs at hxy with h1 h2 h2
    · exact h1.trans h2.symm
    · exact absurd hxy.symm (ne_of_lt y.2).symm.symm
    · exact absurd hxy (ne_of_lt x.2)
    · exact Fin.ext hxy
  · intro i j k hij hik hjk
    exact ⟨k, by simp [hik, i.2], by simp [hjk, j.2]⟩

lemma dimK_spec (n : ℕ) : ∃ π : Fin (dimK n) → Equiv.Perm (Fin n), RepresentsK n (dimK n) π := by
  have hne : {m | ∃ π : Fin m → Equiv.Perm (Fin n), RepresentsK n m π}.Nonempty := by
    classical
    refine ⟨n, representsK_of_rank (fun l x => if x = l then n else x.val) ?_ ?_⟩
    · intro l x y hxy
      simp only at hxy
      split_ifs at hxy with h1 h2 h2
      · exact h1.trans h2.symm
      · exact absurd hxy.symm (ne_of_lt y.2).symm.symm
      · exact absurd hxy (ne_of_lt x.2)
      · exact Fin.ext hxy
    · intro i j k hij hik hjk
      exact ⟨k, by simp [hik, i.2], by simp [hjk, j.2]⟩
  exact Nat.sInf_mem hne

/-- `dim(Kₙ) ≤ dim(Kₙ₊₁)`: just delete `n + 1` in a representation of `Kₙ₊₁`. -/
theorem dimK_mono (n : ℕ) : dimK n ≤ dimK (n + 1) := by
  obtain ⟨π, hπ⟩ := dimK_spec (n + 1)
  apply dimK_le_of_rank (fun l x => (π l (Fin.castSucc x) : ℕ))
  · intro l x y hxy
    exact Fin.castSucc_injective _ ((π l).injective (Fin.ext hxy))
  · intro i j k hij hik hjk
    obtain ⟨l, h1, h2⟩ := hπ _ _ _ ((Fin.castSucc_injective _).ne hij)
      ((Fin.castSucc_injective _).ne hik) ((Fin.castSucc_injective _).ne hjk)
    exact ⟨l, h1, h2⟩

lemma dimK_monotone : Monotone dimK := monotone_nat_of_le_succ dimK_mono

/-- For `n ≥ 3`, any representation needs at least three permutations: each of three fixed
numbers must come last (among the three) in some permutation, and these permutations are
distinct. -/
theorem three_le_dimK {n : ℕ} (hn : 3 ≤ n) : 3 ≤ dimK n := by
  obtain ⟨π, hπ⟩ := dimK_spec n
  let a : Fin 3 → Fin n := fun t => ⟨t.val, by omega⟩
  have ha : Function.Injective a := fun s t h => Fin.ext (by simpa [a] using congrArg Fin.val h)
  -- for each `t`, a permutation in which `a t` comes after the other two
  have hex : ∀ t : Fin 3, ∃ l, ∀ u : Fin 3, u ≠ t → π l (a u) < π l (a t) := by
    intro t
    fin_cases t
    · obtain ⟨l, h1, h2⟩ := hπ (a 1) (a 2) (a 0) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by
      decide))
      exact ⟨l, fun u hu => by fin_cases u <;> simp_all⟩
    · obtain ⟨l, h1, h2⟩ := hπ (a 0) (a 2) (a 1) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by
      decide))
      exact ⟨l, fun u hu => by fin_cases u <;> simp_all⟩
    · obtain ⟨l, h1, h2⟩ := hπ (a 0) (a 1) (a 2) (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by
      decide))
      exact ⟨l, fun u hu => by fin_cases u <;> simp_all⟩
  choose L hL using hex
  have hinj : Function.Injective L := by
    intro s t hst
    by_contra hne
    have h1 := hL t s hne
    have h2 := hL s t (Ne.symm hne)
    rw [hst] at h2
    exact lt_asymm h1 h2
  simpa using Fintype.card_le_of_injective L hinj

/-- Rankings given by listing the elements of `Fin n` in order. -/
def listRank {n m : ℕ} (L : Fin m → List (Fin n)) : Fin m → Fin n → ℕ :=
  fun l x => (L l).idxOf x

/-- `dim(K₃) = 3`, using `π₁ = (1,2,3)`, `π₂ = (2,3,1)`, `π₃ = (3,1,2)`. -/
theorem dimK_three : dimK 3 = 3 := by
  refine le_antisymm ?_ (three_le_dimK le_rfl)
  apply dimK_le_of_rank (listRank ![[0, 1, 2], [1, 2, 0], [2, 0, 1]]) (by decide) (by decide)

/-- `dim(K₄) = 3`, using `π₁ = (1,2,3,4)`, `π₂ = (2,4,3,1)`, `π₃ = (1,4,3,2)`. -/
theorem dimK_four : dimK 4 = 3 := by
  refine le_antisymm ?_ (three_le_dimK (by norm_num))
  apply dimK_le_of_rank (listRank ![[0, 1, 2, 3], [1, 3, 2, 0], [0, 3, 2, 1]])
    (by decide) (by decide)

/-- The four permutations from the margin represent `K₁₂`, so `dim(K₁₂) ≤ 4`. -/
theorem dimK_twelve_le : dimK 12 ≤ 4 := by
  apply dimK_le_of_rank (listRank ![
    [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 3],
    [1, 2, 3, 7, 6, 5, 4, 11, 10, 9, 8, 0],
    [2, 3, 0, 10, 11, 8, 9, 5, 4, 7, 6, 1],
    [3, 0, 1, 9, 8, 11, 10, 6, 7, 4, 5, 2]]) (by decide) (by decide +kernel)

/-- Consequently `dim(Kₙ) ≤ 4` for all `n ≤ 12`. -/
theorem dimK_le_four {n : ℕ} (hn : n ≤ 12) : dimK n ≤ 4 :=
  (dimK_monotone hn).trans dimK_twelve_le

/-- The key step of (2): `p` permutations cannot represent `Kₙ` when `n > 2^(2^p)`, because
iterated Erdős–Szekeres yields three numbers `a < b < c` which are monotone in every
permutation, so `b` never comes after both `a` and `c`. -/
theorem not_representsK_of_lt {p n : ℕ} (hn : 2 ^ 2 ^ p < n) (π : Fin p → Equiv.Perm (Fin n)) :
    ¬ RepresentsK n p π := by
  intro hπ
  obtain ⟨T, hT, hmono⟩ := KnDimension.kn_dimension_bound p n hn (fun l x => ((π l x : ℕ) : ℝ))
    (fun l x y h => (π l).injective (Fin.ext (Nat.cast_injective (R := ℝ) h)))
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  set lo := T.min' hTne
  set hi := T.max' hTne
  have hloT : lo ∈ T := Finset.min'_mem T hTne
  have hhiT : hi ∈ T := Finset.max'_mem T hTne
  obtain ⟨mid, hmid⟩ : ((T.erase lo).erase hi).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_erase_of_mem hloT
    have h2 := Finset.pred_card_le_card_erase (s := T.erase lo) (a := hi)
    omega
  simp only [Finset.mem_erase] at hmid
  obtain ⟨hmhi, hmlo, hmT⟩ := hmid
  have hlo : lo < mid := lt_of_le_of_ne (Finset.min'_le T mid hmT) (Ne.symm hmlo)
  have hhi : mid < hi := lt_of_le_of_ne (Finset.le_max' T mid hmT) hmhi
  obtain ⟨l, h1, h2⟩ := hπ lo hi mid (hlo.trans hhi).ne hlo.ne (hhi.ne')
  have h1' : ((π l lo : ℕ) : ℝ) < ((π l mid : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : ((π l hi : ℕ) : ℝ) < ((π l mid : ℕ) : ℝ) := by exact_mod_cast h2
  rcases hmono l with hm | hm
  · exact lt_asymm (hm hmT hhiT hhi) h2'
  · exact lt_asymm (hm hloT hmT hlo) h1'

/-- Equivalently: `n ≤ 2^(2^dim(Kₙ))`. -/
theorem le_two_pow_two_pow_dimK (n : ℕ) : n ≤ 2 ^ 2 ^ dimK n := by
  by_contra h
  obtain ⟨π, hπ⟩ := dimK_spec n
  exact not_representsK_of_lt (not_le.1 h) π hπ

/-- In the form used in the book: `dim(Kₙ) ≥ p + 1` for `n = 2^(2^p) + 1`. -/
theorem dimK_ge_succ (p : ℕ) : p + 1 ≤ dimK (2 ^ 2 ^ p + 1) := by
  by_contra h
  have h1 := le_two_pow_two_pow_dimK (2 ^ 2 ^ p + 1)
  have h2 : 2 ^ 2 ^ dimK (2 ^ 2 ^ p + 1) ≤ 2 ^ 2 ^ p :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- **Inequality (2):** `dim(Kₙ) ≥ log₂ log₂ n`. -/
theorem dimK_ge_log_log (n : ℕ) : Real.logb 2 (Real.logb 2 n) ≤ dimK n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have h := le_two_pow_two_pow_dimK n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_pos : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by linarith)
  have h1 : Real.logb 2 n ≤ 2 ^ dimK n := by
    have : (n : ℝ) ≤ 2 ^ (2 ^ dimK n : ℕ) := by exact_mod_cast h
    calc Real.logb 2 n ≤ Real.logb 2 (2 ^ (2 ^ dimK n : ℕ)) :=
          Real.logb_le_logb_of_le (by norm_num) (by linarith) this
      _ = 2 ^ dimK n := by rw [Real.logb_pow]; simp
  calc Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 (2 ^ dimK n) :=
        Real.logb_le_logb_of_le (by norm_num) hlog_pos h1
    _ = dimK n := by rw [Real.logb_pow]; simp

end chapter28

/-! ===================== Part: Divisors ===================== -/

/-!
# Section 4 of Chapter 28: the average number of divisors

With `t(j)` the number of divisors of `j` and `t̄(n) = (1/n) ∑_{j ≤ n} t(j)`, we prove
`Hₙ − 1 < t̄(n) ≤ Hₙ` and
`log n − 1 < Hₙ − 1 − 1/n < t̄(n) ≤ Hₙ < log n + 1` (for `n ≥ 2`).
-/

namespace chapter28

open Finset

/-- The average number of divisors `t̄(n) = (1/n) ∑_{j=1}^{n} t(j)`. -/
noncomputable def avgDivisors (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, ((Nat.divisors j).card : ℝ)

lemma sum_one_div_eq_harmonic (n : ℕ) :
    ∑ i ∈ Icc 1 n, (1 : ℚ) / i = harmonic n := by
  rw [harmonic_eq_sum_Icc]; simp [one_div]

/-- `Hₙ − 1 < t̄(n) ≤ Hₙ`. -/
theorem avgDivisors_bounds {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) - 1 < avgDivisors n ∧ avgDivisors n ≤ harmonic n := by
  have hup := avg_divisor_count_le_harmonic n
  have hlo := avg_divisor_count_lower_bound n hn
  rw [sum_one_div_eq_harmonic] at hup hlo
  set S : ℕ := ∑ j ∈ Icc 1 n, (Nat.divisors j).card with hS
  have hup' : (S : ℝ) ≤ n * (harmonic n : ℝ) := by
    have : ((S : ℚ) : ℝ) ≤ ((n * harmonic n : ℚ) : ℝ) := by
      exact_mod_cast (by push_cast [hS]; exact hup)
    simpa using this
  have hlo' : n * (harmonic n : ℝ) - n < S := by
    have : ((n * harmonic n - n : ℚ) : ℝ) < ((S : ℚ) : ℝ) := by
      exact_mod_cast (by push_cast [hS]; exact hlo)
    simpa using this
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have havg : avgDivisors n = S / n := by
    simp [avgDivisors, hS, div_eq_inv_mul]
  rw [havg]
  constructor
  · rw [lt_div_iff₀ hnr]; linarith
  · rw [div_le_iff₀ hnr]; linarith

/-- `log(n+1) − log n > 1/(n+1)` for `n > 0`. -/
lemma log_succ_sub_log_gt {m : ℕ} (hm : 0 < m) :
    1 / ((m : ℝ) + 1) < Real.log ((m : ℝ) + 1) - Real.log m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_lt_sub_one_of_pos (x := (m : ℝ) / (m + 1)) (by positivity)
    (by rw [Ne, div_eq_one_iff_eq (by positivity)]; linarith)
  rw [Real.log_div hmr.ne' (by positivity)] at h
  have : (m : ℝ) / (m + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by field_simp; ring
  linarith

/-- `log(n+1) − log n < 1/n` for `n > 0`. -/
lemma log_succ_sub_log_lt {m : ℕ} (hm : 0 < m) :
    Real.log ((m : ℝ) + 1) - Real.log m < 1 / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_lt_sub_one_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
    (by rw [Ne, div_eq_one_iff_eq hmr.ne']; linarith)
  rw [Real.log_div (by positivity) hmr.ne'] at h
  have : ((m : ℝ) + 1) / m - 1 = 1 / (m : ℝ) := by field_simp; ring
  linarith

/-- `Hₙ < log n + 1` for `n ≥ 2`. -/
theorem harmonic_lt_log_add_one {n : ℕ} (hn : 2 ≤ n) : (harmonic n : ℝ) < Real.log n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 0 < m := by omega
  have h1 := harmonic_le_one_add_log m
  have h2 := log_succ_sub_log_gt hm
  rw [harmonic_succ]
  push_cast at h1 ⊢
  rw [inv_eq_one_div]
  linarith

/-- `log n < H_{n-1} = Hₙ − 1/n` for `n ≥ 2`. -/
theorem log_lt_harmonic_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log n < (harmonic n : ℝ) - 1 / n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have h1 := log_add_one_le_harmonic m
  have h2 := log_succ_sub_log_lt (m := m + 1) (by omega)
  rw [harmonic_succ, harmonic_succ]
  push_cast at h1 h2 ⊢
  rw [inv_eq_one_div, inv_eq_one_div]
  linarith

/-- **The average number of divisors:**
`log n − 1 < Hₙ − 1 − 1/n < t̄(n) ≤ Hₙ < log n + 1` for all `n ≥ 2`. -/
theorem avgDivisors_log_bounds {n : ℕ} (hn : 2 ≤ n) :
    Real.log n - 1 < (harmonic n : ℝ) - 1 - 1 / n ∧
    (harmonic n : ℝ) - 1 - 1 / n < avgDivisors n ∧
    avgDivisors n ≤ harmonic n ∧
    (harmonic n : ℝ) < Real.log n + 1 := by
  have h := avgDivisors_bounds (n := n) (by omega)
  have hpos : (0 : ℝ) < 1 / n := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  refine ⟨?_, ?_, h.2, harmonic_lt_log_add_one hn⟩
  · linarith [log_lt_harmonic_sub hn]
  · linarith [h.1]

/-- Consequently `|t̄(n) − log n| < 1` for `n ≥ 2`. -/
theorem abs_avgDivisors_sub_log_lt {n : ℕ} (hn : 2 ≤ n) :
    |avgDivisors n - Real.log n| < 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := avgDivisors_log_bounds hn
  rw [abs_lt]; constructor <;> linarith

end chapter28

/-! ===================== Part: ReimanGraph ===================== -/

/-!
# The Reiman graph `Gp` (Section 5 of Chapter 28, second part)
-/

namespace chapter28

/-! ## The Reiman graph Gp: a tight construction for the C₄-free bound

The book constructs a graph Gp for each odd prime p:
- Vertices = points of PG(2,p), i.e., one-dimensional subspaces of (ZMod p)³
- Two vertices [u],[v] are adjacent iff ⟨u,v⟩ = u₁v₁ + u₂v₂ + u₃v₃ = 0
- Gp is C₄-free
- Edge count achieves the bound from `c4_free_edge_bound`

We use Mathlib's `Projectivization` and `Projectivization.orthogonal`.
-/

section ReimanGraph

open scoped LinearAlgebra.Projectivization

variable (p : ℕ) [Fact (Nat.Prime p)]

--set_option trace.Meta.synthInstance true

/-- The projective plane over 𝔽ₚ. -/
abbrev PG2 := ℙ (ZMod p) (Fin 3 → ZMod p)

/-- The Reiman graph Gp: vertices are points of PG(2,p), adjacency is orthogonality. -/
noncomputable def reimanGraph : SimpleGraph (PG2 p) :=
  SimpleGraph.fromRel fun v w => Projectivization.orthogonal v w

/-- Adjacency in Gp: distinct orthogonal points. -/
lemma reimanGraph_adj {v w : PG2 p} :
    (reimanGraph p).Adj v w ↔ v ≠ w ∧ Projectivization.orthogonal v w := by
  rw [reimanGraph, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ => ⟨fun h => h.elim id Projectivization.orthogonal_comm.mp, Or.inl⟩

/-- The number of vertices of Gp is p² + p + 1.
    Note: The tex assumes p is an odd prime, but oddness is not needed for the cardinality
    formula — only that p is a prime (hence ZMod p is a field). -/
theorem reimanGraph_card_vertices :
    Nat.card (PG2 p) = p ^ 2 + p + 1 := by
  have hfr : Module.finrank (ZMod p) (Fin 3 → ZMod p) = 3 := by
    simp
  rw [Projectivization.card_of_finrank _ _ hfr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.card_zmod]
  ring

/-- In PG(2,F), if a point x is orthogonal to two distinct points a and c,
    then x = cross a c.  This is the uniqueness of the intersection of two
    hyperplanes (each hyperplane is the set of points orthogonal to a given point).
    Proof: by the BAC-CAB identity, w × (u × v) = (w·v)u − (u·w)v = 0 when
    w·u = 0 and w·v = 0, so the representatives are proportional. -/
lemma orthogonal_both_eq_cross {F : Type*} [Field F] [DecidableEq F]
    {a c : ℙ F (Fin 3 → F)} (hac : a ≠ c)
    {x : ℙ F (Fin 3 → F)} (hxa : Projectivization.orthogonal x a)
    (hxc : Projectivization.orthogonal x c) :
    x = Projectivization.cross a c := by
  induction x with | h w hw =>
  induction a with | h u hu =>
  induction c with | h v hv =>
  rw [Projectivization.orthogonal_mk hw hu] at hxa
  rw [Projectivization.orthogonal_mk hw hv] at hxc
  rw [Projectivization.cross_mk_of_ne hu hv hac,
      Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hw]
  have key := cross_cross_eq_smul_sub_smul' w u v
  rw [hxc, dotProduct_comm, hxa, zero_smul, zero_smul, sub_self] at key
  exact key

/-- Key lemma for no C₄: if two distinct points v, w are both orthogonal to two distinct
    points a, b, then v = w. Equivalently, the "orthogonal complement" hyperplanes of
    distinct points intersect in at most a single projective point.

    This is the projective geometry fact that two distinct hyperplanes in PG(2,p) meet
    in exactly one point.

    Note: The tex states this for 4 *distinct* vertices (6 pairwise ≠ conditions), but the
    proof only needs a ≠ c and b ≠ d.  The other four ≠ conditions follow from Adj being
    irreflexive (loopless graph). -/
theorem reimanGraph_no_C4 :
    ∀ (a b c d : PG2 p),
      a ≠ c → b ≠ d →
      ¬((reimanGraph p).Adj a b ∧ (reimanGraph p).Adj b c ∧
        (reimanGraph p).Adj c d ∧ (reimanGraph p).Adj d a) := by
  intro a b c d hac hbd
  rintro ⟨h1, h2, h3, h4⟩
  obtain ⟨_, hab_orth⟩ := (reimanGraph_adj p).1 h1
  obtain ⟨_, hbc_orth⟩ := (reimanGraph_adj p).1 h2
  obtain ⟨_, hcd_orth⟩ := (reimanGraph_adj p).1 h3
  obtain ⟨_, hda_orth⟩ := (reimanGraph_adj p).1 h4
  -- b and d are both orthogonal to a and c. Since a ≠ c, both equal cross a c.
  have hb := orthogonal_both_eq_cross hac
    (Projectivization.orthogonal_comm.mp hab_orth) hbc_orth
  have hd := orthogonal_both_eq_cross hac
    hda_orth (Projectivization.orthogonal_comm.mp hcd_orth)
  exact hbd (hb.trans hd.symm)

open Classical in
/-- The projective hyperplane orthogonal to a point has p+1 elements. -/
lemma orthogonal_set_card [Fintype (PG2 p)]
    (v : PG2 p) :
    (Finset.univ.filter (fun w : PG2 p => Projectivization.orthogonal v w)).card = p + 1 := by
  induction v using Projectivization.ind with | h u hu =>
  set φ : Module.Dual (ZMod p) (Fin 3 → ZMod p) :=
    dotProductEquiv (ZMod p) (Fin 3) u with hφ_def
  have hφ_apply : ∀ w, φ w = u ⬝ᵥ w := fun _ => rfl
  have hφ : φ ≠ 0 := by
    intro h; exact hu ((dotProductEquiv (ZMod p) (Fin 3)).map_eq_zero_iff.mp h)
  have : FiniteDimensional (ZMod p) (Fin 3 → ZMod p) := inferInstance
  have hfr : Module.finrank (ZMod p) (LinearMap.ker φ) = 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ; simp at h1; omega
  have : Finite (ZMod p) := inferInstance
  have hcard : Nat.card (ℙ (ZMod p) (LinearMap.ker φ)) = p + 1 := by
    rw [Projectivization.card_of_finrank_two _ _ hfr, Nat.card_zmod]
  have hι_inj : Function.Injective (Projectivization.map (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _)) := Projectivization.map_injective _ _
  have : Fintype (ℙ (ZMod p) (LinearMap.ker φ)) := Fintype.ofFinite _
  rw [show p + 1 = Finset.card (Finset.univ : Finset (ℙ (ZMod p) (LinearMap.ker φ))) from by
    rw [Finset.card_univ, Fintype.card_eq_nat_card]; exact hcard.symm]
  symm
  apply Finset.card_bij (fun w _ => Projectivization.map (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) w)
  · intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    induction w using Projectivization.ind with | h k hk =>
    rw [Projectivization.map_mk, Projectivization.orthogonal_mk hu]
    have hk_mem := k.2; rw [LinearMap.mem_ker, hφ_apply] at hk_mem
    show u ⬝ᵥ _ = 0; exact hk_mem
  · intro a _ b _ hab; exact hι_inj hab
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    induction w using Projectivization.ind with | h k hk =>
    rw [Projectivization.orthogonal_mk hu hk] at hw
    have hk_mem : k ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, hφ_apply]; exact hw
    have hk_ne : (⟨k, hk_mem⟩ : LinearMap.ker φ) ≠ 0 := by
      intro h; apply hk; exact congr_arg Subtype.val h
    exact ⟨Projectivization.mk _ ⟨k, hk_mem⟩ hk_ne, Finset.mem_univ _, by
      rw [Projectivization.map_mk]; rfl⟩

open Classical in
/-- Each vertex's degree: p if self-orthogonal, p+1 otherwise.
    The orthogonal hyperplane of [v] in PG(2,p) has p+1 projective points.
    If v·v = 0, then [v] is among them and the degree is p; otherwise p+1. -/
lemma reimanGraph_degree_eq [Fintype (PG2 p)] [DecidableEq (PG2 p)]
    [DecidableRel (reimanGraph p).Adj] (v : PG2 p) :
    (reimanGraph p).degree v =
      if Projectivization.orthogonal v v then p else p + 1 := by
  rw [SimpleGraph.degree]
  have hN : (reimanGraph p).neighborFinset v =
      Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w) := by
    ext w; rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset, reimanGraph_adj]; simp
  rw [hN]
  set S := Finset.univ.filter (fun w : PG2 p => Projectivization.orthogonal v w)
  have hS_card := orthogonal_set_card p v
  split_ifs with h
  · have hv_in : v ∈ S := by simp [S, h]
    have : (Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w)) =
        S.erase v := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, S]
      tauto
    rw [this, Finset.card_erase_of_mem hv_in, hS_card]; omega
  · have : (Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w)) = S := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      exact ⟨fun ⟨_, hw⟩ => hw, fun hw => ⟨fun heq => h (heq ▸ hw), hw⟩⟩
    rw [this, hS_card]

/- **Edge count of Gp (omitted).**

The precise edge count `|E(Gp)| = (p³+p²+p)/2` requires knowing that a non-degenerate
conic in PG(2,𝔽_p) has exactly p+1 points, equivalently that x²+y²+z²=0 has p² solutions
in 𝔽_p³. This is a classical result from the theory of quadratic forms over finite fields,
typically proved via Gauss sums or character-sum orthogonality. The required character-sum
machinery (Fourier analysis over finite fields, product of Gauss sums giving the exact count)
is not yet available in Mathlib as of 2025.

The key results that ARE proved above without this gap:
  • `reimanGraph_card_vertices`: |V(Gp)| = p²+p+1
  • `reimanGraph_no_C4`: Gp contains no 4-cycle (the main combinatorial content)
  • `reimanGraph_degree_eq`: each vertex has degree p or p+1

Together these already give the Reiman bound  ex(n, C₄) ≥ (1/2)·n^{3/2}·(1-o(1))
since |E| ≈ p·|V|/2 ≈ n^{3/2}/2.
-/

end ReimanGraph

end chapter28

/-! ===================== Part: ReimanEdges ===================== -/

/-!
# The number of edges of the Reiman graph `Gp`

We follow the book: the number of vertices of `Gp` of degree `p` is the number of
self-orthogonal points (points on the conic `x² + y² + z² = 0`), which equals `trace A` for the
symmetric `0/1` matrix `A` with `a_{vw} = 1 ↔ ⟨v, w⟩ = 0`. Since `A² = pI + J` and `A𝟙 = (p+1)𝟙`,
every eigenvalue of `A` is `p + 1` or `±√p`; since the trace is an integer and `√p` is
irrational, `trace A = p + 1`.
-/

namespace chapter28

open Matrix Finset
open scoped LinearAlgebra.Projectivization

section RealAlgebra

/-- The purely numerical part of the eigenvalue argument. If the real numbers `μ i`
(`i` ranging over a set of size `N = p² + p + 1`) are all roots of `(x − (p+1))(x² − p)`,
their squares sum to `N (p + 1)` and their sum is an integer, then their sum is `p + 1`. -/
lemma sum_eq_of_roots {ι : Type*} [Fintype ι] (μ : ι → ℝ) (p : ℕ) (hp : Irrational (√(p : ℝ)))
    (hcard : Fintype.card ι = p ^ 2 + p + 1)
    (hroot : ∀ i, (μ i - (p + 1)) * (μ i ^ 2 - p) = 0)
    (hsq : ∑ i, μ i ^ 2 = (p ^ 2 + p + 1 : ℝ) * (p + 1))
    (hint : ∃ t : ℤ, ∑ i, μ i = t) :
    ∑ i, μ i = p + 1 := by
  classical
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsq_p : √(p : ℝ) ^ 2 = p := Real.sq_sqrt hp0
  -- write every eigenvalue as `(p+1) δ + √p ε`
  set δ : ι → ℝ := fun i => if μ i = p + 1 then 1 else 0
  set ε : ι → ℤ := fun i => if μ i = p + 1 then 0 else if μ i = √(p : ℝ) then 1 else -1
  have hsqrt_pos : 0 < √(p : ℝ) := by
    rcases (Real.sqrt_nonneg (p : ℝ)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by simp [← h]⟩ hp
  have hdecomp : ∀ i, μ i = (p + 1) * δ i + √(p : ℝ) * ε i := by
    intro i
    by_cases h1 : μ i = p + 1
    · simp [δ, ε, h1]
    · have h2 : μ i ^ 2 - p = 0 := by
        rcases mul_eq_zero.1 (hroot i) with h | h
        · exact absurd (by linarith) h1
        · exact h
      have h3 : μ i = √(p : ℝ) ∨ μ i = -√(p : ℝ) :=
        sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [hsq_p]; linarith)
      simp only [δ, ε, ite_of_neg h1]
      rcases h3 with h3 | h3
      · rw [ite_of_pos h3]; simp [h3]
      · rw [ite_of_neg (by rw [h3]; intro h; linarith)]; simp [h3]
  have hsq_i : ∀ i, μ i ^ 2 = (p + 1) ^ 2 * δ i + p * (1 - δ i) := by
    intro i
    simp only [δ]
    by_cases h1 : μ i = p + 1
    · simp [h1]
    · rcases mul_eq_zero.1 (hroot i) with h | h
      · exact absurd (by linarith) h1
      · simp [h1]; linarith
  -- the number `a` of eigenvalues equal to `p + 1`
  set a : ℝ := ∑ i, δ i
  have hN : (Fintype.card ι : ℝ) = p ^ 2 + p + 1 := by exact_mod_cast hcard
  have ha : a = 1 := by
    have h := hsq
    simp_rw [hsq_i] at h
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [hN] at h
    have hpos : (0 : ℝ) < p ^ 2 + p + 1 := by positivity
    have : a * (p ^ 2 + p + 1) = 1 * (p ^ 2 + p + 1) := by
      simp only [a] at h ⊢; nlinarith
    exact mul_right_cancel₀ hpos.ne' this
  -- hence `∑ μ = (p+1) + k √p` with `k ∈ ℤ`, and `k = 0` by irrationality
  obtain ⟨t, ht⟩ := hint
  set k : ℤ := ∑ i, ε i
  have hsum : ∑ i, μ i = (p + 1) * a + √(p : ℝ) * k := by
    simp_rw [hdecomp]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [k, a]
  rw [ha, mul_one] at hsum
  by_cases hk : k = 0
  · rw [hsum, hk]; simp
  · exfalso
    have : √(p : ℝ) * k = ((t - (p + 1) : ℤ) : ℝ) := by push_cast; linarith
    exact (hp.mul_intCast hk).ne_int _ this

end RealAlgebra

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance : Fintype (PG2 p) := Fintype.ofFinite _

noncomputable instance : DecidableEq (PG2 p) := Classical.decEq _

open Classical in
/-- The matrix `A` of the book: `a_{vw} = 1` if `⟨v, w⟩ = 0` and `0` otherwise
(rows and columns are indexed by the points of the projective plane). -/
noncomputable def reimanMatrix : Matrix (PG2 p) (PG2 p) ℝ :=
  fun v w => if Projectivization.orthogonal v w then 1 else 0

lemma reimanMatrix_isHermitian : (reimanMatrix p).IsHermitian := by
  ext v w
  by_cases h : Projectivization.orthogonal v w
  · simp [reimanMatrix, h, Projectivization.orthogonal_comm.1 h]
  · simp [reimanMatrix, h,
      show ¬ Projectivization.orthogonal w v from fun h' => h (Projectivization.orthogonal_comm.1
        h')]

/-- Fact 1: every row of `A` contains exactly `p + 1` ones. -/
lemma reimanMatrix_row_sum (v : PG2 p) : ∑ w, reimanMatrix p v w = p + 1 := by
  classical
  have h := orthogonal_set_card p v
  simp only [reimanMatrix]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  convert congrArg (Nat.cast (R := ℝ)) h using 2
  push_cast; ring_nf

/-- Fact 2: two distinct rows have exactly one common `1`. -/
lemma reimanMatrix_common {v w : PG2 p} (hvw : v ≠ w) :
    ∑ u, reimanMatrix p v u * reimanMatrix p u w = 1 := by
  classical
  have : ∀ u, reimanMatrix p v u * reimanMatrix p u w =
      if u = Projectivization.cross v w then 1 else 0 := by
    intro u
    simp only [reimanMatrix]
    by_cases hu : u = Projectivization.cross v w
    · subst hu
      simp [Projectivization.orthogonal_cross_left hvw, Projectivization.cross_orthogonal_right hvw]
    · rw [ite_of_neg hu]
      by_cases h1 : Projectivization.orthogonal v u
      · by_cases h2 : Projectivization.orthogonal u w
        · exact absurd (orthogonal_both_eq_cross hvw (Projectivization.orthogonal_comm.1 h1) h2) hu
        · simp [h2]
      · simp [h1]
  simp_rw [this]
  simp

/-- `A² = p I + J`. -/
lemma reimanMatrix_sq :
    reimanMatrix p * reimanMatrix p = (p : ℝ) • (1 : Matrix (PG2 p) (PG2 p) ℝ) + of (fun _ _ => 1)
      := by
  ext v w
  rw [Matrix.mul_apply]
  by_cases hvw : v = w
  · subst hvw
    have : ∀ u, reimanMatrix p v u * reimanMatrix p u v = reimanMatrix p v u := by
      intro u
      by_cases h : Projectivization.orthogonal v u
      · simp [reimanMatrix, h, Projectivization.orthogonal_comm.1 h]
      · simp [reimanMatrix, h]
    simp_rw [this, reimanMatrix_row_sum]
    simp
  · rw [reimanMatrix_common p hvw]
    simp [hvw]

/-- `A J = (p + 1) J`. -/
lemma reimanMatrix_mul_J :
    reimanMatrix p * of (fun _ _ => (1 : ℝ)) = ((p : ℝ) + 1) • of (fun _ _ => (1 : ℝ)) := by
  ext v w
  simp [Matrix.mul_apply, reimanMatrix_row_sum]

/-- `A` satisfies `(A − (p+1) I)(A² − p I) = 0`. -/
lemma reimanMatrix_cubic :
    reimanMatrix p * (reimanMatrix p * reimanMatrix p) =
      ((p : ℝ) + 1) • (reimanMatrix p * reimanMatrix p) + (p : ℝ) • reimanMatrix p -
        ((p : ℝ) * (p + 1)) • (1 : Matrix (PG2 p) (PG2 p) ℝ) := by
  rw [reimanMatrix_sq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, reimanMatrix_mul_J]
  rw [smul_add, smul_smul]
  abel_nf
  rw [show ((p : ℝ) + 1) * p = p * (p + 1) by ring]
  abel

/-- Every eigenvalue of `A` is `p + 1`, `√p` or `−√p`. -/
lemma reimanMatrix_eigenvalue_root (i : PG2 p) :
    ((reimanMatrix_isHermitian p).eigenvalues i - (p + 1)) *
      ((reimanMatrix_isHermitian p).eigenvalues i ^ 2 - p) = 0 := by
  set hA := reimanMatrix_isHermitian p
  have hv := hA.mulVec_eigenvectorBasis i
  set μ := hA.eigenvalues i
  set v := (hA.eigenvectorBasis i).ofLp
  have hv0 : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
  have h2 : (reimanMatrix p * reimanMatrix p) *ᵥ v = (μ ^ 2) • v := by
    rw [← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul, sq]
  have h3 : (reimanMatrix p * (reimanMatrix p * reimanMatrix p)) *ᵥ v = (μ ^ 3) • v := by
    rw [← mulVec_mulVec, h2, mulVec_smul, hv, smul_smul]; ring_nf
  have h : (reimanMatrix p * (reimanMatrix p * reimanMatrix p)) *ᵥ v =
      (((p : ℝ) + 1) • (reimanMatrix p * reimanMatrix p) + (p : ℝ) • reimanMatrix p -
        ((p : ℝ) * (p + 1)) • (1 : Matrix (PG2 p) (PG2 p) ℝ)) *ᵥ v :=
    congrArg (fun M => M *ᵥ v) (reimanMatrix_cubic p)
  rw [h3, sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, h2, hv, one_mulVec,
    smul_smul, smul_smul, ← add_smul, ← sub_smul, ← sub_eq_zero, ← sub_smul] at h
  have := (smul_eq_zero.1 h).resolve_right hv0
  linear_combination this

/-- For a real symmetric matrix, `trace (A²) = ∑ λᵢ²`. -/
lemma trace_mul_self_eq_sum_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  set U := hA.eigenvectorUnitary
  set D : Matrix n n ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAD : A = (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) := hA.spectral_theorem
  have hUU : star (U : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self U
  have : A * A = (U : Matrix n n ℝ) * (D * D) * star (U : Matrix n n ℝ) := by
    rw [hAD]
    calc (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) * ((U : Matrix n n ℝ) * D * star ↑U)
        = (U : Matrix n n ℝ) * D * (star (U : Matrix n n ℝ) * (U : Matrix n n ℝ)) * D *
            star (U : Matrix n n ℝ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc (U : Matrix n n ℝ)]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  simp [D, Matrix.trace, diagonal_mul_diagonal, sq]

/-- The number of vertices of `Gp`, as a `Fintype.card`. -/
lemma card_PG2 : Fintype.card (PG2 p) = p ^ 2 + p + 1 := by
  rw [Fintype.card_eq_nat_card]; exact reimanGraph_card_vertices p

/-- **The trace argument:** `trace A = p + 1`. -/
theorem reimanMatrix_trace : (reimanMatrix p).trace = p + 1 := by
  classical
  set hA := reimanMatrix_isHermitian p
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  apply sum_eq_of_roots _ p (hp.out.irrational_sqrt) (card_PG2 p)
    (reimanMatrix_eigenvalue_root p)
  · rw [← trace_mul_self_eq_sum_sq, reimanMatrix_sq]
    simp [Matrix.trace, card_PG2]
    ring
  · refine ⟨(Finset.univ.filter (fun v : PG2 p => Projectivization.orthogonal v v)).card, ?_⟩
    have h := hA.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at h
    rw [← h]
    simp [Matrix.trace, reimanMatrix, Finset.sum_boole]

open Classical in
/-- **Claim.** Exactly `p + 1` points of the projective plane lie on the conic
`x² + y² + z² = 0` (i.e. are self-orthogonal); these are the vertices of degree `p`. -/
theorem card_selfOrthogonal :
    (Finset.univ.filter (fun v : PG2 p => Projectivization.orthogonal v v)).card = p + 1 := by
  have h := reimanMatrix_trace p
  simp only [Matrix.trace, Matrix.diag, reimanMatrix] at h
  rw [Finset.sum_boole] at h
  exact_mod_cast h

/-- **Edge count of `Gp`:** `2 |E(Gp)| = p (p + 1)²`. -/
theorem reimanGraph_two_mul_card_edges [DecidableRel (reimanGraph p).Adj] :
    2 * (reimanGraph p).edgeFinset.card = p * (p + 1) ^ 2 := by
  classical
  rw [← handshaking]
  simp_rw [reimanGraph_degree_eq]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    card_selfOrthogonal]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (PG2 p))) (fun v => Projectivization.orthogonal v v)
  rw [card_selfOrthogonal, Finset.card_univ, card_PG2] at h
  have h2 : (Finset.univ.filter (fun v : PG2 p => ¬ Projectivization.orthogonal v v)).card =
      p ^ 2 := by omega
  rw [h2]
  ring

/-- **Edge count of `Gp`, book form:** with `n = p² + p + 1` vertices,
`|E(Gp)| = (n − 1)/4 · (1 + √(4n − 3))`, which almost agrees with Reiman's bound (6). -/
theorem reimanGraph_card_edges [DecidableRel (reimanGraph p).Adj] :
    ((reimanGraph p).edgeFinset.card : ℝ) =
      ((Fintype.card (PG2 p) : ℝ) - 1) / 4 * (1 + Real.sqrt (4 * Fintype.card (PG2 p) - 3)) := by
  have h := reimanGraph_two_mul_card_edges p
  have h' : (2 : ℝ) * (reimanGraph p).edgeFinset.card = p * (p + 1) ^ 2 := by exact_mod_cast h
  rw [card_PG2]
  push_cast
  have : (4 * ((p : ℝ) ^ 2 + p + 1) - 3) = (2 * p + 1) ^ 2 := by ring
  rw [this, Real.sqrt_sq (by positivity)]
  linarith

/-- The number of solutions of `x² + y² + z² = 0` in `𝔽ₚ³` is exactly `p²`. -/
theorem card_solutions_conic :
    (Finset.univ.filter (fun v : Fin 3 → ZMod p => v ⬝ᵥ v = 0)).card = p ^ 2 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  -- the nonzero solutions are fibred over the self-orthogonal points, each fibre has `p - 1`
  -- elements (the nonzero multiples of a representative)
  set S := Finset.univ.filter (fun v : Fin 3 → ZMod p => v ⬝ᵥ v = 0)
  set S' := S.erase 0
  have h0 : (0 : Fin 3 → ZMod p) ∈ S := by simp [S]
  have hS : S.card = S'.card + 1 := (Finset.card_erase_add_one h0).symm
  let P : Finset (PG2 p) := Finset.univ.filter (fun v => Projectivization.orthogonal v v)
  let f : (Fin 3 → ZMod p) → PG2 p := fun v =>
    if hv : v = 0 then Classical.arbitrary _ else Projectivization.mk (ZMod p) v hv
  have hmaps : ∀ v ∈ S', f v ∈ P := by
    intro v hv
    simp only [S', S, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [P, f, dite_of_neg hv.1, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hv.2
  have hfib : ∀ x ∈ P, (S'.filter (fun v => f v = x)).card = p - 1 := by
    intro x hx
    induction x using Projectivization.ind with | h w hw =>
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
      Projectivization.orthogonal_mk hw hw] at hx
    -- the fibre is the image of the nonzero scalars under `c ↦ c • w`
    have : S'.filter (fun v => f v = Projectivization.mk (ZMod p) w hw) =
        (Finset.univ.filter (fun c : ZMod p => c ≠ 0)).image (fun c => c • w) := by
      ext v
      simp only [S', S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨hv0, -⟩, hfv⟩
        simp only [f, dite_of_neg hv0] at hfv
        obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff _ _ _ hv0 hw).1 hfv
        exact ⟨(c : ZMod p), c.ne_zero, by rw [← hc, Units.smul_def]⟩
      · rintro ⟨c, hc, rfl⟩
        have hcw : c • w ≠ 0 := smul_ne_zero hc hw
        refine ⟨⟨hcw, by simp [smul_dotProduct, dotProduct_smul, hx]⟩, ?_⟩
        simp only [f, dite_of_neg hcw]
        exact (Projectivization.mk_eq_mk_iff' _ _ _ hcw hw).2 ⟨c, rfl⟩
    rw [this, Finset.card_image_of_injective]
    · rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ZMod.card]
    · intro c d hcd
      exact smul_left_injective (ZMod p) hw hcd
  have hS' : S'.card = P.card * (p - 1) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
      smul_eq_mul]
  have hP : P.card = p + 1 := card_selfOrthogonal p
  rw [hS, hS', hP]
  have : (p + 1) * (p - 1) + 1 = p ^ 2 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  exact this

end chapter28

/-! ===================== Part: Sperner ===================== -/

/-!
# Section 6 of Chapter 28: Sperner's lemma (combinatorial core)

We formalize the double-counting proof of Sperner's lemma for an abstract triangulation.
A triangulation is given by a finite family of "small triangles" `tri i` (`i ∈ T`), each a
set of three vertices. Colors are `0, 1, 2` (the book's `1, 2, 3`).

The book's "partial dual graph" argument counts the incidences between small triangles and
edges whose endpoints carry the colors `0` and `1` ("doors"). We represent a door by the
ordered pair `(u, v)` with `col u = 0` and `col v = 1`.

* Every edge lies in at most two small triangles (interior edges in two, boundary edges in
  one), and
* the number of boundary doors is odd,

then the number of tricolored triangles is odd (in particular, nonzero).
We also prove the one-dimensional lemma used for the boundary: along a path whose endpoints
have different colors there is an odd number of color changes.
-/

namespace chapter28

open Finset

variable {ι V : Type*} [DecidableEq V]

/-- A small triangle is *tricolored* if all three colors occur among its vertices. -/
def Tricolored (col : V → Fin 3) (t : Finset V) : Prop := ∀ c : Fin 3, ∃ v ∈ t, col v = c

instance (col : V → Fin 3) (t : Finset V) : Decidable (Tricolored col t) := by
  unfold Tricolored; infer_instance

/-- The number of small triangles containing both `u` and `v`. -/
def pairCount (T : Finset ι) (tri : ι → Finset V) (u v : V) : ℕ :=
  #{i ∈ T | u ∈ tri i ∧ v ∈ tri i}

/-- The doors inside a given small triangle: pairs `(u, v)` of its vertices with
`col u = 0`, `col v = 1`. -/
def doorsIn (col : V → Fin 3) (t : Finset V) : Finset (V × V) :=
  (t ×ˢ t).filter (fun x => col x.1 = 0 ∧ col x.2 = 1)

/-- All doors of the triangulation. -/
def doorPairs (T : Finset ι) (tri : ι → Finset V) (col : V → Fin 3) : Finset (V × V) :=
  T.biUnion (fun i => doorsIn col (tri i))

omit [DecidableEq V] in
/-- In a single triangle, the number of doors is odd iff the triangle is tricolored. -/
lemma card_doorsIn_mod_two (col : V → Fin 3) (t : Finset V) (ht : t.card = 3) :
    #(doorsIn col t) % 2 = if Tricolored col t then 1 else 0 := by
  have hprod : doorsIn col t = (t.filter (fun v => col v = 0)) ×ˢ (t.filter (fun v => col v = 1)) :=
    by
    ext x; simp [doorsIn, and_and_and_comm]
  rw [hprod, card_product]
  set n0 := #(t.filter (fun v => col v = 0))
  set n1 := #(t.filter (fun v => col v = 1))
  set n2 := #(t.filter (fun v => col v = 2))
  have hsum : n0 + n1 + n2 = 3 := by
    rw [← ht, card_eq_sum_card_fiberwise (f := col) (t := univ) (fun _ _ => Finset.mem_coe.2
      (mem_univ _)),
      Fin.sum_univ_three]
  have htri : Tricolored col t ↔ 0 < n0 ∧ 0 < n1 ∧ 0 < n2 := by
    simp only [n0, n1, n2, card_pos, Tricolored, Fin.forall_fin_succ,
      Finset.Nonempty, mem_filter]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, fun i => i.elim0⟩
  by_cases h : Tricolored col t
  · rw [ite_of_pos h]
    obtain ⟨h0, h1, h2⟩ := htri.1 h
    have : n0 = 1 := by omega
    have : n1 = 1 := by omega
    simp [*]
  · rw [ite_of_neg h]
    rw [htri] at h
    have hn0 : n0 ≤ 3 := by omega
    have hn1 : n1 ≤ 3 := by omega
    interval_cases n0 <;> interval_cases n1 <;> omega

/-- **Sperner's lemma (abstract double-counting form).**
If every edge lies in at most two small triangles and the number of doors lying in exactly one
small triangle (the boundary doors) is odd, then the number of tricolored triangles is odd. -/
theorem sperner_odd (T : Finset ι) (tri : ι → Finset V) (col : V → Fin 3)
    (h3 : ∀ i ∈ T, (tri i).card = 3)
    (h2 : ∀ u v, u ≠ v → pairCount T tri u v ≤ 2)
    (hB : Odd #{x ∈ doorPairs T tri col | pairCount T tri x.1 x.2 = 1}) :
    Odd #{i ∈ T | Tricolored col (tri i)} := by
  set D := doorPairs T tri col
  -- double counting the incidences (small triangle, door)
  have hdc : ∑ i ∈ T, #(doorsIn col (tri i)) = ∑ x ∈ D, pairCount T tri x.1 x.2 := by
    have hsub : ∀ i ∈ T, doorsIn col (tri i) = D.bipartiteAbove (fun i x => x ∈ doorsIn col (tri i))
      i := by
      intro i hi
      ext x
      simp only [bipartiteAbove, mem_filter, D, doorPairs, mem_biUnion]
      exact ⟨fun hx => ⟨⟨i, hi, hx⟩, hx⟩, fun hx => hx.2⟩
    rw [sum_congr rfl (fun i hi => congrArg card (hsub i hi)),
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    refine sum_congr rfl (fun x hx => ?_)
    simp only [D, doorPairs, mem_biUnion] at hx
    obtain ⟨j, -, hj⟩ := hx
    simp only [doorsIn, mem_filter, mem_product] at hj
    unfold pairCount bipartiteBelow
    congr 1
    ext i
    simp [doorsIn, hj.2]
  -- each door lies in one or two triangles
  have hcount : ∀ x ∈ D, pairCount T tri x.1 x.2 % 2 =
      if pairCount T tri x.1 x.2 = 1 then 1 else 0 := by
    intro x hx
    simp only [D, doorPairs, mem_biUnion] at hx
    obtain ⟨j, hjT, hj⟩ := hx
    simp only [doorsIn, mem_filter, mem_product] at hj
    have hne : x.1 ≠ x.2 := fun h => by
      have := hj.2.1; rw [h, hj.2.2] at this; exact absurd this (by decide)
    have hle := h2 _ _ hne
    have hpos : 0 < pairCount T tri x.1 x.2 :=
      card_pos.2 ⟨j, mem_filter.2 ⟨hjT, hj.1.1, hj.1.2⟩⟩
    interval_cases (pairCount T tri x.1 x.2) <;> simp
  have hmod : #{i ∈ T | Tricolored col (tri i)} % 2 = #{x ∈ D | pairCount T tri x.1 x.2 = 1} % 2 :=
    by
    calc #{i ∈ T | Tricolored col (tri i)} % 2
        = (∑ i ∈ T, if Tricolored col (tri i) then 1 else 0) % 2 := by rw [sum_boole]; simp
      _ = (∑ i ∈ T, #(doorsIn col (tri i)) % 2) % 2 := by
          rw [sum_congr rfl (fun i hi => (card_doorsIn_mod_two col (tri i) (h3 i hi)).symm)]
      _ = (∑ i ∈ T, #(doorsIn col (tri i))) % 2 := (sum_nat_mod _ _ _).symm
      _ = (∑ x ∈ D, pairCount T tri x.1 x.2) % 2 := by rw [hdc]
      _ = (∑ x ∈ D, pairCount T tri x.1 x.2 % 2) % 2 := sum_nat_mod _ _ _
      _ = (∑ x ∈ D, if pairCount T tri x.1 x.2 = 1 then 1 else 0) % 2 := by
          rw [sum_congr rfl hcount]
      _ = #{x ∈ D | pairCount T tri x.1 x.2 = 1} % 2 := by rw [sum_boole]; simp
  rw [Nat.odd_iff] at hB ⊢
  rw [hmod, hB]

/-- **The one-dimensional Sperner lemma.** If a path of vertices `0, 1, …, k` is colored with two
colors and the endpoints have different colors, then the number of color changes along the
path is odd. -/
theorem odd_card_color_changes (k : ℕ) (s : ℕ → Bool) (h : s 0 ≠ s k) :
    Odd #{i ∈ range k | s i ≠ s (i + 1)} := by
  have key : ∀ k, #{i ∈ range k | s i ≠ s (i + 1)} % 2 = if s 0 = s k then 0 else 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [range_add_one, filter_insert]
      by_cases hk : s k ≠ s (k + 1)
      · rw [ite_of_pos hk, card_insert_of_notMem (by simp)]
        rw [Nat.add_mod, ih]
        cases h0 : s 0 <;> cases h1 : s k <;> cases h2 : s (k + 1) <;> simp_all
      · rw [ite_of_neg hk, ih]
        push Not at hk
        rw [hk]
  have := key k
  rw [ite_of_neg h] at this
  exact Nat.odd_iff.2 this

end chapter28

/-! ===================== Part: SpernerGrid ===================== -/

/-!
# Sperner's lemma for the standard triangulation of a triangle

The big triangle `V₁V₂V₃` is subdivided into `k²` small triangles. A vertex is a pair
`(a, b)` of natural numbers with `a + b ≤ k` (barycentric coordinates `(a, b, k − a − b) / k`);
`V₁ = (k, 0)`, `V₂ = (0, k)`, `V₃ = (0, 0)`.
The small triangles are the "upward" triangles `{(a,b), (a+1,b), (a,b+1)}` with
`a + b + 1 ≤ k` and the "downward" triangles `{(a+1,b), (a,b+1), (a+1,b+1)}` with
`a + b + 2 ≤ k`.

We verify the hypotheses of the abstract Sperner lemma `sperner_odd` for this triangulation:
every edge lies in at most two small triangles, and for a Sperner coloring the boundary doors
are exactly the color changes along the side `V₁V₂`, of which there is an odd number.
-/

namespace chapter28

open Finset

/-- The upward small triangle with lower-left corner `x`. -/
def upTri (x : ℕ × ℕ) : Finset (ℕ × ℕ) := {x, (x.1 + 1, x.2), (x.1, x.2 + 1)}

/-- The downward small triangle with "lower-left corner" `x`. -/
def downTri (x : ℕ × ℕ) : Finset (ℕ × ℕ) := {(x.1 + 1, x.2), (x.1, x.2 + 1), (x.1 + 1, x.2 + 1)}

/-- Indices of upward small triangles. -/
def gridUp (k : ℕ) : Finset (ℕ × ℕ) := (range k ×ˢ range k).filter (fun x => x.1 + x.2 + 1 ≤ k)

/-- Indices of downward small triangles. -/
def gridDown (k : ℕ) : Finset (ℕ × ℕ) := (range k ×ˢ range k).filter (fun x => x.1 + x.2 + 2 ≤ k)

/-- Index set of all small triangles of the `k`-th subdivision. -/
def gridT (k : ℕ) : Finset ((ℕ × ℕ) ⊕ (ℕ × ℕ)) := (gridUp k).disjSum (gridDown k)

/-- The small triangle with a given index. -/
def gridTri : (ℕ × ℕ) ⊕ (ℕ × ℕ) → Finset (ℕ × ℕ) := Sum.elim upTri downTri

lemma mem_gridUp {k : ℕ} {x : ℕ × ℕ} : x ∈ gridUp k ↔ x.1 + x.2 + 1 ≤ k := by
  simp only [gridUp, mem_filter, mem_product, mem_range]; omega

lemma mem_gridDown {k : ℕ} {x : ℕ × ℕ} : x ∈ gridDown k ↔ x.1 + x.2 + 2 ≤ k := by
  simp only [gridDown, mem_filter, mem_product, mem_range]; omega

lemma mem_upTri {x y : ℕ × ℕ} :
    y ∈ upTri x ↔ y = x ∨ y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1) := by
  simp [upTri]

lemma mem_downTri {x y : ℕ × ℕ} :
    y ∈ downTri x ↔ y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1) ∨ y = (x.1 + 1, x.2 + 1) := by
  simp [downTri]

lemma card_upTri (x : ℕ × ℕ) : (upTri x).card = 3 := by
  unfold upTri
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [Prod.ext_iff]
  · simp [Prod.ext_iff]

lemma card_downTri (x : ℕ × ℕ) : (downTri x).card = 3 := by
  unfold downTri
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [Prod.ext_iff]
  · simp [Prod.ext_iff]

lemma card_gridTri {k : ℕ} (i) (_ : i ∈ gridT k) : (gridTri i).card = 3 := by
  cases i with
  | inl x => exact card_upTri x
  | inr x => exact card_downTri x

/-- An upward triangle is determined by any two of its vertices: its corner is their
componentwise minimum. -/
lemma upTri_unique {x u v : ℕ × ℕ} (huv : u ≠ v) (hu : u ∈ upTri x) (hv : v ∈ upTri x) :
    x = (min u.1 v.1, min u.2 v.2) := by
  rw [mem_upTri] at hu hv
  obtain ⟨x1, x2⟩ := x
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    simp_all [Prod.ext_iff]

/-- A downward triangle is determined by any two of its vertices: its upper corner is their
componentwise maximum. -/
lemma downTri_unique {x u v : ℕ × ℕ} (huv : u ≠ v) (hu : u ∈ downTri x) (hv : v ∈ downTri x) :
    (x.1 + 1, x.2 + 1) = (max u.1 v.1, max u.2 v.2) := by
  rw [mem_downTri] at hu hv
  obtain ⟨x1, x2⟩ := x
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    simp_all [Prod.ext_iff]

/-- The number of small triangles containing `u` and `v` splits into upward and downward ones. -/
lemma pairCount_grid (k : ℕ) (u v : ℕ × ℕ) :
    pairCount (gridT k) gridTri u v =
      #{x ∈ gridUp k | u ∈ upTri x ∧ v ∈ upTri x} +
      #{x ∈ gridDown k | u ∈ downTri x ∧ v ∈ downTri x} := by
  unfold pairCount
  rw [← card_disjSum]
  congr 1
  ext i
  cases i with
  | inl x =>
    rw [Finset.mem_filter, gridT, Finset.inl_mem_disjSum, Finset.inl_mem_disjSum,
      Finset.mem_filter]
    exact Iff.rfl
  | inr x =>
    rw [Finset.mem_filter, gridT, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum,
      Finset.mem_filter]
    exact Iff.rfl

lemma upCount_le_one (k : ℕ) {u v : ℕ × ℕ} (huv : u ≠ v) :
    #{x ∈ gridUp k | u ∈ upTri x ∧ v ∈ upTri x} ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  simp only [mem_filter] at hx hy
  rw [upTri_unique huv hx.2.1 hx.2.2, upTri_unique huv hy.2.1 hy.2.2]

lemma downCount_le_one (k : ℕ) {u v : ℕ × ℕ} (huv : u ≠ v) :
    #{x ∈ gridDown k | u ∈ downTri x ∧ v ∈ downTri x} ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  simp only [mem_filter] at hx hy
  have h1 := downTri_unique huv hx.2.1 hx.2.2
  have h2 := downTri_unique huv hy.2.1 hy.2.2
  rw [← h2] at h1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext (by omega) (by omega)

/-- Every edge lies in at most two small triangles. -/
lemma pairCount_grid_le_two (k : ℕ) (u v : ℕ × ℕ) (huv : u ≠ v) :
    pairCount (gridT k) gridTri u v ≤ 2 := by
  rw [pairCount_grid]
  have := upCount_le_one k huv
  have := downCount_le_one k huv
  omega

/-- An edge lying in an upward and a downward triangle is interior: it lies in two triangles. -/
lemma two_le_pairCount_grid {k : ℕ} {u v x y : ℕ × ℕ} (hx : x ∈ gridUp k) (hux : u ∈ upTri x)
    (hvx : v ∈ upTri x) (hy : y ∈ gridDown k) (huy : u ∈ downTri y) (hvy : v ∈ downTri y) :
    2 ≤ pairCount (gridT k) gridTri u v := by
  rw [pairCount_grid]
  have h1 : 0 < #{x ∈ gridUp k | u ∈ upTri x ∧ v ∈ upTri x} :=
    card_pos.2 ⟨x, mem_filter.2 ⟨hx, hux, hvx⟩⟩
  have h2 : 0 < #{x ∈ gridDown k | u ∈ downTri x ∧ v ∈ downTri x} :=
    card_pos.2 ⟨y, mem_filter.2 ⟨hy, huy, hvy⟩⟩
  omega

section Coloring

variable (k : ℕ) (col : ℕ × ℕ → Fin 3)

/-- The vertex number `i` on the side `V₂V₁` (from `V₂ = (0, k)` to `V₁ = (k, 0)`). -/
def sideVertex (i : ℕ) : ℕ × ℕ := (i, k - i)

/-- Whether the `i`-th side vertex has color `0`. -/
def sideColor (i : ℕ) : Bool := decide (col (sideVertex k i) = 0)

/-- The door at position `i` of the side (if there is a color change there). -/
def sideDoor (i : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  if col (sideVertex k i) = 0 then (sideVertex k i, sideVertex k (i + 1))
  else (sideVertex k (i + 1), sideVertex k i)

end Coloring

/-- A *Sperner coloring* of the `k`-th subdivision: vertices on the side opposite to `Vᵢ` do not
get the color of `Vᵢ`. (Then `Vᵢ` gets color `i`, and the side `VᵢVⱼ` only uses colors
`i` and `j`.) -/
structure IsSpernerColoring (k : ℕ) (col : ℕ × ℕ → Fin 3) : Prop where
  side_a : ∀ b, col (0, b) ≠ 0
  side_b : ∀ a, col (a, 0) ≠ 1
  side_c : ∀ a b, a + b = k → col (a, b) ≠ 2

/-- The boundary doors of a Sperner coloring are exactly the color changes along `V₂V₁`. -/
lemma boundary_doors_eq {k : ℕ} {col : ℕ × ℕ → Fin 3} (hcol : IsSpernerColoring k col) :
    {x ∈ doorPairs (gridT k) gridTri col | pairCount (gridT k) gridTri x.1 x.2 = 1} =
      ((range k).filter (fun i => sideColor k col i ≠ sideColor k col (i + 1))).image
        (sideDoor k col) := by
  ext ⟨u, v⟩
  simp only [mem_filter, mem_image, mem_range, doorPairs, mem_biUnion, doorsIn, mem_product]
  constructor
  · rintro ⟨⟨j, hj, ⟨hu, hv⟩, hcu, hcv⟩, hpc⟩
    have huv : u ≠ v := by rintro rfl; rw [hcu] at hcv; exact absurd hcv (by decide)
    -- the edge must lie on the side `a + b = k`
    cases j with
    | inl x =>
      simp only [gridT, inl_mem_disjSum, mem_gridUp] at hj
      simp only [gridTri, Sum.elim_inl, mem_upTri] at hu hv
      obtain ⟨a, b⟩ := x
      simp only at hj hu hv
      -- the corner case analysis
      have key : ∀ y ∈ gridDown k, u ∈ downTri y → v ∈ downTri y → False := by
        intro y hy huy hvy
        have := two_le_pairCount_grid (x := (a, b)) (mem_gridUp.2 hj)
          (by simp only [mem_upTri]; exact hu) (by simp only [mem_upTri]; exact hv) hy huy hvy
        omega
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact absurd rfl huv
      · -- horizontal edge, `u` left
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · exact absurd hcv (hcol.side_b _)
        · exact (key (a, b - 1) (mem_gridDown.2 (by simp; omega))
            (by simp [mem_downTri]; omega) (by simp [mem_downTri]; omega)).elim
      · -- vertical edge, `u` lower
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · exact absurd hcu (hcol.side_a _)
        · exact (key (a - 1, b) (mem_gridDown.2 (by simp; omega))
            (by simp [mem_downTri]; omega) (by simp [mem_downTri]; omega)).elim
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · exact absurd hcv (hcol.side_b _)
        · exact (key (a, b - 1) (mem_gridDown.2 (by simp; omega))
            (by simp [mem_downTri]; omega) (by simp [mem_downTri]; omega)).elim
      · exact absurd rfl huv
      · -- diagonal edge `u = (a+1,b)`, `v = (a,b+1)`
        by_cases hk : a + b + 2 ≤ k
        · exact (key (a, b) (mem_gridDown.2 hk) (by simp [mem_downTri])
            (by simp [mem_downTri])).elim
        · refine ⟨a, ⟨by omega, ?_⟩, ?_⟩
          · have h1 : sideVertex k a = (a, b + 1) := by simp [sideVertex]; omega
            have h2 : sideVertex k (a + 1) = (a + 1, b) := by simp [sideVertex]; omega
            simp [sideColor, h1, h2, hcu, hcv]
          · have h1 : sideVertex k a = (a, b + 1) := by simp [sideVertex]; omega
            have h2 : sideVertex k (a + 1) = (a + 1, b) := by simp [sideVertex]; omega
            simp [sideDoor, h1, h2, hcv]
      · rcases Nat.eq_zero_or_pos a with rfl | ha
        · exact absurd hcu (hcol.side_a _)
        · exact (key (a - 1, b) (mem_gridDown.2 (by simp; omega))
            (by simp [mem_downTri]; omega) (by simp [mem_downTri]; omega)).elim
      · -- diagonal edge `u = (a,b+1)`, `v = (a+1,b)`
        by_cases hk : a + b + 2 ≤ k
        · exact (key (a, b) (mem_gridDown.2 hk) (by simp [mem_downTri])
            (by simp [mem_downTri])).elim
        · refine ⟨a, ⟨by omega, ?_⟩, ?_⟩
          · have h1 : sideVertex k a = (a, b + 1) := by simp [sideVertex]; omega
            have h2 : sideVertex k (a + 1) = (a + 1, b) := by simp [sideVertex]; omega
            simp [sideColor, h1, h2, hcu, hcv]
          · have h1 : sideVertex k a = (a, b + 1) := by simp [sideVertex]; omega
            have h2 : sideVertex k (a + 1) = (a + 1, b) := by simp [sideVertex]; omega
            simp [sideDoor, h1, h2, hcu]
      · exact absurd rfl huv
    | inr x =>
      simp only [gridT, inr_mem_disjSum, mem_gridDown] at hj
      simp only [gridTri, Sum.elim_inr] at hu hv
      obtain ⟨a, b⟩ := x
      exfalso
      -- every edge of a downward triangle also lies in an upward triangle
      have key : ∀ y ∈ gridUp k, u ∈ upTri y → v ∈ upTri y → False := by
        intro y hy huy hvy
        have := two_le_pairCount_grid hy huy hvy (y := (a, b)) (mem_gridDown.2 hj) hu hv
        omega
      rw [mem_downTri] at hu hv
      simp only at hj hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact huv rfl
      · exact key (a, b) (mem_gridUp.2 (by omega)) (by simp [mem_upTri]) (by simp [mem_upTri])
      · exact key (a + 1, b) (mem_gridUp.2 (by omega)) (by simp [mem_upTri])
          (by simp [mem_upTri])
      · exact key (a, b) (mem_gridUp.2 (by omega)) (by simp [mem_upTri]) (by simp [mem_upTri])
      · exact huv rfl
      · exact key (a, b + 1) (mem_gridUp.2 (by omega)) (by simp [mem_upTri])
          (by simp [mem_upTri])
      · exact key (a + 1, b) (mem_gridUp.2 (by omega)) (by simp [mem_upTri])
          (by simp [mem_upTri])
      · exact key (a, b + 1) (mem_gridUp.2 (by omega)) (by simp [mem_upTri])
          (by simp [mem_upTri])
      · exact huv rfl
  · rintro ⟨i, ⟨hi, hchange⟩, hdoor⟩
    have h1 : sideVertex k i = (i, (k - i - 1) + 1) := by simp [sideVertex]; omega
    have h2 : sideVertex k (i + 1) = (i + 1, k - i - 1) := by simp [sideVertex]; omega
    have hx : (i, k - i - 1) ∈ gridUp k := mem_gridUp.2 (by simp; omega)
    -- colors on the side are `0` or `1`
    have hc1 : col (sideVertex k i) ≠ 2 := hcol.side_c _ _ (by omega)
    have hc2 : col (sideVertex k (i + 1)) ≠ 2 := hcol.side_c _ _ (by omega)
    -- the corresponding up triangle contains the door, and no down triangle does
    have hup : ∀ w ∈ ({sideVertex k i, sideVertex k (i + 1)} : Finset (ℕ × ℕ)),
        w ∈ upTri (i, k - i - 1) := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · rw [h1]; simp [mem_upTri]
      · rw [h2]; simp [mem_upTri]
    have hne : sideVertex k i ≠ sideVertex k (i + 1) := by simp [sideVertex]
    have hdown : #{x ∈ gridDown k | sideVertex k i ∈ downTri x ∧
        sideVertex k (i + 1) ∈ downTri x} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro y hy ⟨hy1, hy2⟩
      have := downTri_unique hne hy1 hy2
      rw [mem_gridDown] at hy
      simp only [h1, h2, Prod.mk.injEq] at this
      omega
    have hupc : #{x ∈ gridUp k | sideVertex k i ∈ upTri x ∧ sideVertex k (i + 1) ∈ upTri x} = 1 :=
      le_antisymm (upCount_le_one k hne) (card_pos.2 ⟨_, mem_filter.2 ⟨hx, hup _ (by simp),
        hup _ (by simp)⟩⟩)
    have hdown' : #{x ∈ gridDown k | sideVertex k (i + 1) ∈ downTri x ∧
        sideVertex k i ∈ downTri x} = 0 := by
      simp_rw [and_comm (a := sideVertex k (i + 1) ∈ _)]; exact hdown
    have hupc' : #{x ∈ gridUp k | sideVertex k (i + 1) ∈ upTri x ∧ sideVertex k i ∈ upTri x} = 1 :=
      by
      simp_rw [and_comm (a := sideVertex k (i + 1) ∈ _)]; exact hupc
    unfold sideDoor at hdoor
    unfold sideColor at hchange
    split_ifs at hdoor with h0
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdoor
      have hcv : col (sideVertex k (i + 1)) = 1 := by
        have : col (sideVertex k (i + 1)) ≠ 0 := by simpa [h0] using hchange
        omega
      refine ⟨⟨Sum.inl (i, k - i - 1), by simp [gridT, hx], ⟨hup _ (by simp), hup _ (by simp)⟩,
        h0, hcv⟩, ?_⟩
      rw [pairCount_grid, hupc, hdown]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdoor
      have hcu : col (sideVertex k (i + 1)) = 0 := by simpa [h0] using hchange
      have hcv : col (sideVertex k i) = 1 := by omega
      refine ⟨⟨Sum.inl (i, k - i - 1), by simp [gridT, hx], ⟨hup _ (by simp), hup _ (by simp)⟩,
        hcu, hcv⟩, ?_⟩
      rw [pairCount_grid, hupc', hdown']

/-- **Sperner's lemma for the `k`-th standard subdivision of a triangle.**
For every Sperner coloring the number of tricolored small triangles is odd. -/
theorem grid_sperner (k : ℕ) (col : ℕ × ℕ → Fin 3) (hcol : IsSpernerColoring k col) :
    Odd #{i ∈ gridT k | Tricolored col (gridTri i)} := by
  apply sperner_odd _ _ _ card_gridTri (pairCount_grid_le_two k)
  rw [boundary_doors_eq hcol, card_image_of_injOn]
  · apply odd_card_color_changes
    have h0 : sideColor k col 0 = false := by
      simp [sideColor, sideVertex, hcol.side_a]
    have hk : sideColor k col k = true := by
      have h1 := hcol.side_b k
      have h2 := hcol.side_c k 0 (by simp)
      simp only [sideColor, sideVertex, Nat.sub_self, decide_eq_true_eq]
      omega
    rw [h0, hk]; decide
  · -- the door at position `i` determines `i`
    intro i _ j _ hij
    have key : ∀ i, min (sideDoor k col i).1.1 (sideDoor k col i).2.1 = i := by
      intro i; unfold sideDoor; split_ifs <;> simp [sideVertex]
    rw [← key i, ← key j, hij]

/-- In particular, a tricolored small triangle exists. -/
theorem grid_sperner_exists (k : ℕ) (col : ℕ × ℕ → Fin 3) (hcol : IsSpernerColoring k col) :
    ∃ i ∈ gridT k, Tricolored col (gridTri i) := by
  obtain ⟨m, hm⟩ := grid_sperner k col hcol
  have : 0 < #{i ∈ gridT k | Tricolored col (gridTri i)} := by omega
  obtain ⟨i, hi⟩ := card_pos.1 this
  exact ⟨i, (mem_filter.1 hi).1, (mem_filter.1 hi).2⟩

end chapter28

/-! ===================== Part: Brouwer ===================== -/

/-!
# Brouwer's fixed point theorem in dimension 2, via Sperner's lemma

Following the book, we first prove that every continuous map `f : Δ → Δ` of the triangle
`Δ = conv{e₁, e₂, e₃} ⊆ ℝ³` has a fixed point: color a point `v` by the smallest index `i`
with `f(v)ᵢ < vᵢ`, apply Sperner's lemma to finer and finer triangulations, and pass to a
limit using compactness of `Δ`. Then we transfer the result to the disk `B²`, which is
homeomorphic to `Δ`.
-/

namespace chapter28

open Set Filter Topology Finset

/-- The fixed point property of a set `S`: every continuous self-map of `S` has a fixed point. -/
def HasFixedPointProperty {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  ∀ f : X → X, ContinuousOn f S → MapsTo f S S → ∃ x ∈ S, f x = x

/-- The fixed point property is inherited along a retraction-type pair of maps (in particular
along homeomorphisms). -/
lemma HasFixedPointProperty.transfer {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {S' : Set Y} (φ : X → Y) (ψ : Y → X) (hφ : ContinuousOn φ S)
    (hψ : ContinuousOn ψ S') (hφS : MapsTo φ S S') (hψS : MapsTo ψ S' S)
    (hφψ : ∀ y ∈ S', φ (ψ y) = y) (h : HasFixedPointProperty S) : HasFixedPointProperty S' := by
  intro g hg hgS
  obtain ⟨x, hx, hfx⟩ := h (ψ ∘ g ∘ φ) (hψ.comp (hg.comp hφ hφS) (hgS.comp hφS))
    (hψS.comp (hgS.comp hφS))
  refine ⟨φ x, hφS hx, ?_⟩
  have := congrArg φ hfx
  simp only [Function.comp] at this
  rwa [hφψ _ (hgS (hφS hx))] at this

/-- The standard triangle `Δ = {x ∈ ℝ³ | xᵢ ≥ 0, x₀ + x₁ + x₂ = 1}`. -/
def stdTriangle : Set (Fin 3 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

lemma isClosed_stdTriangle : IsClosed stdTriangle := by
  rw [stdTriangle, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (by fun_prop) continuous_const)

lemma isCompact_stdTriangle : IsCompact stdTriangle := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_stdTriangle
    ((Metric.isBounded_Icc (0 : Fin 3 → ℝ) 1).subset ?_)
  intro x hx
  refine ⟨fun i => hx.1 i, fun i => ?_⟩
  have := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  rw [hx.2] at this
  exact this

lemma convex_stdTriangle : Convex ℝ stdTriangle := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have := hx.1 i; have := hy.1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

/-! ### The coloring `λ(v) = min {i : f(v)ᵢ < vᵢ}` -/

/-- The book's coloring: the smallest index `i` such that `f(v)ᵢ < vᵢ` (with `2` as default). -/
noncomputable def brouwerColor (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : Fin 3 :=
  if f v 0 < v 0 then 0 else if f v 1 < v 1 then 1 else 2

section Coloring

variable {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {v : Fin 3 → ℝ}

lemma sum_fin_three (x : Fin 3 → ℝ) : ∑ i, x i = x 0 + x 1 + x 2 := Fin.sum_univ_three x

/-- If `v` is not a fixed point, then the `i`-th coordinate of `f(v) − v` is negative for the
color `i` of `v`. -/
lemma brouwerColor_spec (hv : v ∈ stdTriangle) (hfv : f v ∈ stdTriangle)
    (hne : f v ≠ v) : f v (brouwerColor f v) < v (brouwerColor f v) := by
  unfold brouwerColor
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · push Not at h0 h1
    have hs1 := hv.2; have hs2 := hfv.2
    rw [sum_fin_three] at hs1 hs2
    rcases (show f v 2 ≤ v 2 by linarith).lt_or_eq with h2 | h2
    · exact h2
    · exfalso
      apply hne
      funext i
      fin_cases i
      · simp; linarith
      · simp; linarith
      · exact h2

lemma brouwerColor_ne_zero (hfv : f v ∈ stdTriangle) (h : v 0 = 0) :
    brouwerColor f v ≠ 0 := by
  unfold brouwerColor
  have := hfv.1 0
  split_ifs with h0 h1 <;> first | (rw [h] at h0; linarith) | decide

lemma brouwerColor_ne_one (hfv : f v ∈ stdTriangle) (h : v 1 = 0) :
    brouwerColor f v ≠ 1 := by
  unfold brouwerColor
  have := hfv.1 1
  split_ifs with h0 h1 <;> first | decide | (rw [h] at h1; linarith)

lemma brouwerColor_ne_two (hv : v ∈ stdTriangle) (hfv : f v ∈ stdTriangle)
    (hne : f v ≠ v) (h : v 2 = 0) : brouwerColor f v ≠ 2 := by
  intro hc
  have := brouwerColor_spec hv hfv hne
  rw [hc, h] at this
  linarith [hfv.1 2]

end Coloring

/-! ### Points of the `k`-th subdivision -/

/-- The vertex `(a, b)` of the `k`-th subdivision, as a point `(a/k, b/k, (k−a−b)/k)` of `Δ`. -/
noncomputable def gridPoint (k : ℕ) (w : ℕ × ℕ) : Fin 3 → ℝ :=
  ![(w.1 : ℝ) / k, (w.2 : ℝ) / k, ((k : ℝ) - w.1 - w.2) / k]

lemma gridPoint_mem {k : ℕ} (hk : 0 < k) {w : ℕ × ℕ} (hw : w.1 + w.2 ≤ k) :
    gridPoint k w ∈ stdTriangle := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hw' : (w.1 : ℝ) + w.2 ≤ k := by exact_mod_cast hw
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [gridPoint] <;> apply div_nonneg <;> linarith [(w.1.cast_nonneg : (0:ℝ) ≤
    w.1), (w.2.cast_nonneg : (0:ℝ) ≤ w.2)]
  · rw [sum_fin_three]; simp only [gridPoint]; simp; field_simp; ring

lemma tri_vertex_le {k : ℕ} {i : (ℕ × ℕ) ⊕ (ℕ × ℕ)} (hi : i ∈ gridT k) {w : ℕ × ℕ}
    (hw : w ∈ gridTri i) : w.1 + w.2 ≤ k := by
  cases i with
  | inl x =>
    simp only [gridT, inl_mem_disjSum, mem_gridUp] at hi
    simp only [gridTri, Sum.elim_inl, mem_upTri] at hw
    rcases hw with rfl | rfl | rfl <;> (try simp) <;> omega
  | inr x =>
    simp only [gridT, inr_mem_disjSum, mem_gridDown] at hi
    simp only [gridTri, Sum.elim_inr, mem_downTri] at hw
    rcases hw with rfl | rfl | rfl <;> (try simp) <;> omega

lemma tri_vertex_close {i : (ℕ × ℕ) ⊕ (ℕ × ℕ)} {w w' : ℕ × ℕ} (hw : w ∈ gridTri i)
    (hw' : w' ∈ gridTri i) : w.1 ≤ w'.1 + 1 ∧ w.2 ≤ w'.2 + 1 := by
  cases i with
  | inl x =>
    simp only [gridTri, Sum.elim_inl, mem_upTri] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;> (try simp) <;> omega
  | inr x =>
    simp only [gridTri, Sum.elim_inr, mem_downTri] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;> (try simp) <;> omega

/-- Vertices of a small triangle of the `k`-th subdivision are at distance at most `2/k`. -/
lemma gridPoint_dist_le {k : ℕ} (hk : 0 < k) {i : (ℕ × ℕ) ⊕ (ℕ × ℕ)} {w w' : ℕ × ℕ}
    (hw : w ∈ gridTri i) (hw' : w' ∈ gridTri i) :
    ‖gridPoint k w - gridPoint k w'‖ ≤ 2 / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨h1, h2⟩ := tri_vertex_close hw hw'
  obtain ⟨h3, h4⟩ := tri_vertex_close hw' hw
  have e1 : (w.1 : ℝ) ≤ w'.1 + 1 := by exact_mod_cast h1
  have e2 : (w.2 : ℝ) ≤ w'.2 + 1 := by exact_mod_cast h2
  have e3 : (w'.1 : ℝ) ≤ w.1 + 1 := by exact_mod_cast h3
  have e4 : (w'.2 : ℝ) ≤ w.2 + 1 := by exact_mod_cast h4
  have key : ∀ t : ℝ, |t| ≤ 2 → ‖t / k‖ ≤ 2 / k := fun t ht => by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hk']
    exact div_le_div_of_nonneg_right ht hk'.le
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  fin_cases j
  · have : gridPoint k w 0 - gridPoint k w' 0 = ((w.1 : ℝ) - w'.1) / k := by
      simp [gridPoint]; ring
    simp only [Fin.zero_eta, Pi.sub_apply, this]
    exact key _ (abs_le.2 ⟨by linarith, by linarith⟩)
  · have : gridPoint k w 1 - gridPoint k w' 1 = ((w.2 : ℝ) - w'.2) / k := by
      simp [gridPoint]; ring
    simp only [Fin.mk_one, Pi.sub_apply, this]
    exact key _ (abs_le.2 ⟨by linarith, by linarith⟩)
  · have : gridPoint k w 2 - gridPoint k w' 2 = (((w'.1 : ℝ) + w'.2) - (w.1 + w.2)) / k := by
      simp [gridPoint]; ring
    simp only [Fin.reduceFinMk, Pi.sub_apply, this]
    exact key _ (abs_le.2 ⟨by linarith, by linarith⟩)

/-! ### Brouwer's theorem for the triangle -/

/-- **Brouwer's fixed point theorem for the triangle `Δ`.** Every continuous map `f : Δ → Δ`
has a fixed point. -/
theorem brouwer_stdTriangle : HasFixedPointProperty (stdTriangle) := by
  intro f hf hmaps
  by_contra hcon
  push Not at hcon
  -- the coloring of the vertices of the `k`-th subdivision
  let col : ℕ → ℕ × ℕ → Fin 3 := fun k w =>
    if w.1 + w.2 ≤ k then brouwerColor f (gridPoint k w) else 2
  have hcol : ∀ n, IsSpernerColoring (n + 1) (col (n + 1)) := by
    intro n
    have hk : 0 < n + 1 := Nat.succ_pos n
    refine ⟨fun b => ?_, fun a => ?_, fun a b hab => ?_⟩
    · simp only [col]
      split_ifs with h
      · exact brouwerColor_ne_zero (hmaps (gridPoint_mem hk h)) (by simp [gridPoint])
      · decide
    · simp only [col]
      split_ifs with h
      · exact brouwerColor_ne_one (hmaps (gridPoint_mem hk h)) (by simp [gridPoint])
      · decide
    · simp only [col]
      have h : a + b ≤ n + 1 := hab.le
      rw [ite_of_pos h]
      have hmem := gridPoint_mem (w := (a, b)) hk h
      refine brouwerColor_ne_two hmem (hmaps hmem) (hcon _ hmem) ?_
      have : ((a : ℝ) + b) = (n + 1 : ℕ) := by exact_mod_cast hab
      simp only [gridPoint]; simp; push_cast at this; rw [sub_sub, this]; simp
  -- a tricolored triangle in every subdivision
  have hex : ∀ n, ∃ i ∈ gridT (n + 1), Tricolored (col (n + 1)) (gridTri i) :=
    fun n => grid_sperner_exists _ _ (hcol n)
  choose I hIT hItri using hex
  choose W hWmem hWcol using hItri
  set p : ℕ → Fin 3 → Fin 3 → ℝ := fun n c => gridPoint (n + 1) (W n c)
  have hpmem : ∀ n c, p n c ∈ stdTriangle := fun n c =>
    gridPoint_mem (Nat.succ_pos n) (tri_vertex_le (hIT n) (hWmem n c))
  have hpcol : ∀ n c, f (p n c) c < p n c c := by
    intro n c
    have h := hWcol n c
    simp only [col, ite_of_pos (tri_vertex_le (hIT n) (hWmem n c))] at h
    have := brouwerColor_spec (hpmem n c) (hmaps (hpmem n c)) (hcon _ (hpmem n c))
    rwa [h] at this
  -- compactness: a convergent subsequence of the vertices of color `0`
  obtain ⟨v, hv, φ, hφ, hlim⟩ := isCompact_stdTriangle.tendsto_subseq
    (fun n => hpmem n 0)
  -- the vertices of the other colors converge to the same point
  have hlim' : ∀ c, Tendsto (fun n => p (φ n) c) atTop (𝓝 v) := by
    intro c
    have hsmall : Tendsto (fun n => p (φ n) c - p (φ n) 0) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => (φ n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1
            (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
        exact this.const_div_atTop 2
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
      have := gridPoint_dist_le (Nat.succ_pos (φ n)) (hWmem (φ n) c) (hWmem (φ n) 0)
      simpa using this
    simpa using hsmall.add hlim
  -- passing to the limit: `f(v)ᵢ ≤ vᵢ` for all `i`
  have hle : ∀ c, f v c ≤ v c := by
    intro c
    have hfl : Tendsto (fun n => f (p (φ n) c)) atTop (𝓝 (f v)) :=
      (hf v hv).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim' c, Eventually.of_forall
        (fun n => hpmem (φ n) c)⟩)
    exact le_of_tendsto_of_tendsto' ((continuous_apply c).continuousAt.tendsto.comp hfl)
      ((continuous_apply c).continuousAt.tendsto.comp (hlim' c)) (fun n => (hpcol (φ n) c).le)
  -- but the coordinates of `f(v)` and `v` both sum to `1`, so `f(v) = v`
  apply hcon v hv
  have hs1 := hv.2; have hs2 := (hmaps hv).2
  rw [sum_fin_three] at hs1 hs2
  have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
  funext i
  fin_cases i <;> simp <;> linarith

/-! ### Transfer to the disk `B²` -/

/-- The affine map from `Δ ⊆ ℝ³` to the plane. -/
noncomputable def simplexToPlane (x : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x 0 - 1 / 3, x 1 - 1 / 3]

/-- Its inverse (barycentric coordinates). -/
noncomputable def planeToSimplex (y : EuclideanSpace ℝ (Fin 2)) : Fin 3 → ℝ :=
  ![y 0 + 1 / 3, y 1 + 1 / 3, 1 / 3 - y 0 - y 1]

/-- The triangle `Δ`, placed in the plane with its barycenter at the origin. -/
def planeTriangle : Set (EuclideanSpace ℝ (Fin 2)) := planeToSimplex ⁻¹' stdTriangle

lemma continuous_simplexToPlane : Continuous simplexToPlane := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => by fin_cases i <;> (simp; fun_prop)

lemma continuous_planeToSimplex : Continuous planeToSimplex :=
  continuous_pi fun i => by fin_cases i <;> simp [planeToSimplex] <;> fun_prop

lemma simplexToPlane_planeToSimplex (y : EuclideanSpace ℝ (Fin 2)) :
    simplexToPlane (planeToSimplex y) = y := by
  ext i; fin_cases i <;> simp [simplexToPlane, planeToSimplex]

lemma planeToSimplex_simplexToPlane {x : Fin 3 → ℝ} (hx : x ∈ stdTriangle) :
    planeToSimplex (simplexToPlane x) = x := by
  have h := hx.2
  rw [sum_fin_three] at h
  funext i
  fin_cases i <;> simp [simplexToPlane, planeToSimplex]
  linarith

lemma planeTriangle_fpp : HasFixedPointProperty planeTriangle :=
  brouwer_stdTriangle.transfer simplexToPlane planeToSimplex
    continuous_simplexToPlane.continuousOn continuous_planeToSimplex.continuousOn
    (fun x hx => by
      show planeToSimplex (simplexToPlane x) ∈ stdTriangle
      rw [planeToSimplex_simplexToPlane hx]; exact hx)
    (fun y hy => hy) (fun y _ => simplexToPlane_planeToSimplex y)

lemma convex_planeTriangle : Convex ℝ planeTriangle := by
  intro y hy z hz a b ha hb hab
  have : planeToSimplex (a • y + b • z) = a • planeToSimplex y + b • planeToSimplex z := by
    funext i
    fin_cases i <;> simp [planeToSimplex] <;> linear_combination (-1 / 3 : ℝ) * hab
  simp only [planeTriangle, Set.mem_preimage]
  rw [this]
  exact convex_stdTriangle hy hz ha hb hab

lemma isClosed_planeTriangle : IsClosed planeTriangle :=
  IsClosed.preimage continuous_planeToSimplex isClosed_stdTriangle

lemma isBounded_planeTriangle : Bornology.IsBounded planeTriangle := by
  refine (isCompact_stdTriangle.image continuous_simplexToPlane).isBounded.subset ?_
  intro y hy
  exact ⟨planeToSimplex y, hy, simplexToPlane_planeToSimplex y⟩

lemma interior_planeTriangle_nonempty : (interior planeTriangle).Nonempty := by
  refine ⟨0, ?_⟩
  set U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | -1 / 3 < y 0} ∩ {y | -1 / 3 < y 1} ∩ {y | y 0 + y 1 < 1 / 3}
  have hc0 : Continuous fun y : EuclideanSpace ℝ (Fin 2) => y 0 := by fun_prop
  have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin 2) => y 1 := by fun_prop
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const hc0).inter (isOpen_lt continuous_const hc1)).inter
      (isOpen_lt (hc0.add hc1) continuous_const)
  have hsub : U ⊆ planeTriangle := by
    rintro y ⟨⟨h0, h1⟩, h2⟩
    change -1 / 3 < y 0 at h0
    change -1 / 3 < y 1 at h1
    change y 0 + y 1 < 1 / 3 at h2
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [planeToSimplex] <;> linarith
    · rw [sum_fin_three]; simp [planeToSimplex]; ring
  exact interior_mono hsub (hU.interior_eq.symm ▸ (by simp [U]; norm_num))

/-- **Brouwer's fixed point theorem for the disk**, in fixed-point-property form: the closed
unit disk `B² ⊆ ℝ²` has the fixed point property (since it is homeomorphic to `Δ`). -/
theorem closedBall_fpp :
    HasFixedPointProperty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨e, -, he, -⟩ := exists_homeomorph_image_eq convex_planeTriangle
    interior_planeTriangle_nonempty
    ((NormedSpace.isVonNBounded_iff ℝ).2 isBounded_planeTriangle)
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0, by simp⟩)
    ((NormedSpace.isVonNBounded_iff ℝ).2 Metric.isBounded_closedBall)
  rw [isClosed_planeTriangle.closure_eq, Metric.isClosed_closedBall.closure_eq] at he
  refine planeTriangle_fpp.transfer e e.symm e.continuous.continuousOn
    e.symm.continuous.continuousOn (fun x hx => he ▸ mem_image_of_mem e hx) ?_
    (fun y _ => e.apply_symm_apply y)
  intro y hy
  rw [← he] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

/-- **Brouwer's fixed point theorem (n = 2).** Every continuous map of the closed unit disk
of `ℝ²` into itself has a fixed point. -/
theorem brouwer_fixed_point_2d
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  obtain ⟨x, hx, hfx⟩ := closedBall_fpp f hf.continuousOn
    (fun x hx => by simpa using hB x (by simpa using hx))
  exact ⟨x, by simpa using hx, hfx⟩

/-- **Brouwer's fixed point theorem (n = 1)**, from the intermediate value theorem. -/
theorem brouwer_fixed_point_1d (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (hmaps : MapsTo f (Icc 0 1) (Icc 0 1)) : ∃ x ∈ Icc (0 : ℝ) 1, f x = x := by
  have hg : ContinuousOn (fun x => f x - x) (Icc 0 1) := hf.sub continuousOn_id
  have h0 := hmaps (left_mem_Icc.2 zero_le_one)
  have h1 := hmaps (right_mem_Icc.2 zero_le_one)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' zero_le_one hg
    (show (0 : ℝ) ∈ Icc (f 1 - 1) (f 0 - 0) from ⟨by linarith [h1.2], by linarith [h0.1]⟩)
  exact ⟨x, hx, by simp only at hgx; linarith⟩

end chapter28
