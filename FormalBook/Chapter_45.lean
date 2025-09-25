/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Powerset
--import Mathlib.Analysis.SpecialFunctions.Exp
--import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation



open SimpleGraph Finset
/-!
# Probability makes counting (sometimes) easy

## Structure
  - Theorem 1
    - proof
  - Ramsey Numbers
  - Theorem 2
    - proof
  - Triangle-free graphs with high chromatic number (TODO)
  - Theorem 3
    - proof
  - Theorem 4 (TODO : Define crossing number)
-/


section
namespace chapter45

variable {α : Type _} [DecidableEq α] {X : Finset α}
variable {d : ℕ} {h_d : d ≥ 2}

/-- `𝓕` is a collection of `d`-sets of `X`-/
def two_colorable (𝓕 : Finset (Finset X)) :=
  ∃ c : X → Fin 2, ∀ A : Finset X,
  A ∈ 𝓕 → ∃ x y : A, (c (x : X) = (0 : Fin 2)) ∧ (c y = (1 : Fin 2))



theorem remark_1 {d : ℕ} : ∃ α : Type, ∃ X : Finset α, ∃ 𝓕 : Finset (Finset X),
  (∀ A ∈ 𝓕, A.card = d) ∧  ¬ two_colorable 𝓕 := by
  use Fin (2 * d + 1)
  use univ
  use (Finset.powerset univ).filter (Finset.card · = d)
  simp only [univ_eq_attach, mem_filter, mem_powerset, and_imp, imp_self, implies_true, true_and]
  unfold two_colorable
  push_neg
  intro coloring
  by_cases h : d ≤ (Finset.univ.filter (coloring · = 1)).card
  · refine (Finset.exists_subset_card_eq h).imp ?_
    simp +contextual [Finset.subset_iff]
  · simp_all only [Fin.isValue, univ_eq_attach, not_le, mem_filter, mem_powerset, ne_eq,
    Subtype.forall, mem_univ, forall_true_left]
    have : d ≤ (Finset.univ.filter (coloring · = 0)).card := by
      rw [← not_lt]
      intro h_2
      have : ∀ a, coloring a = 1 ↔ coloring a ≠ 0 := by omega
      simp_all [Finset.filter_not, Finset.card_sdiff]
      omega
    refine (Finset.exists_subset_card_eq this).imp ?_
    simp +contextual [Finset.subset_iff]


theorem remark_2 {𝓕 𝓢 : Finset (Finset X)}
  (h₁ : two_colorable 𝓕)  (h₂ : 𝓢 ⊆ 𝓕) : two_colorable 𝓢 := by
  apply h₁.imp ?_
  intro coloring h₃ A Amem
  exact h₃ A (h₂ Amem)


open ENNReal NNReal

protected lemma ENNReal.mul_inv_eq_iff_eq_mul {a b c: ENNReal}
  (h0 : b ≠ 0) (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) :
  a * b⁻¹ = c ↔ a = c * b := by
    lift a to ℝ≥0 using ha
    lift b to ℝ≥0 using hb
    lift c to ℝ≥0 using hc
    norm_cast at h0; norm_cast
    apply mul_inv_eq_iff_eq_mul₀ h0

open MeasureTheory


theorem theorem_1 {h_d : d ≥ 2} (𝓕 : Finset (Finset X))
  (H_𝓕 : ∀ (A : Finset X), A ∈ 𝓕 → A.card = d)
  : 𝓕.card ≤ 2 ^ (d-1) → two_colorable 𝓕 := by
  intro bnd
  have I : Fintype ({ x // x ∈ X } → Fin 2) := (by apply Fintype.ofFinite)
  set P : Measure (X → Fin 2) := (PMF.uniformOfFintype (X → Fin 2)).toMeasure with Pdef
  set E : (Finset X) → Finset (X → Fin 2) := (fun A => {c | ∀ x ∈ A, ∀ y ∈ A, c x = c y}) with Edef
  have probaEA (A : Finset X) (hA : A ∈ 𝓕) : P (E A) = (1 / 2)^(@Nat.cast ℤ _ (d-1)) := by
    have forComp : d ≤ #X := by
      rw [← H_𝓕 A hA] ; convert (card_le_univ A) ; simp only [Fintype.card_coe]
    rw [Pdef, PMF.toMeasure_uniformOfFintype_apply]
    · nth_rw 2 [← Nat.card_eq_fintype_card]
      rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card,Fintype.card_coe]
      simp only [coe_sort_coe, Fintype.card_coe]
      have sizeEA : #(E A) = 2 ^ (#X - #A + 1) := by
        have : A.Nonempty := by
          rw [← card_pos, (H_𝓕 A hA)] ; omega
        have charaEA : E A = disjUnion {c | ∀ x ∈ A, c x = 0} {c | ∀ x ∈ A, c x = 1}
          (fun C c₀ c₁ c ohno => by
              obtain ⟨a,ah⟩ := this
              replace c₀ := ((Finset.mem_filter_univ c).mp (c₀ ohno)) a ah
              replace c₁ := ((Finset.mem_filter_univ c).mp (c₁ ohno)) a ah
              rw [c₀] at c₁
              contradiction
              )
          := by grind only [= mem_filter, = mem_disjUnion, mem_univ, cases eager Subtype, cases Or]
        have cardComp {i} : #{c : { x // x ∈ X } → Fin 2 | ∀ x ∈ A, c x = i} = 2 ^ (#X - #A) := by
          rw [show #X = Fintype.card X from by simp only [Fintype.card_coe]]
          rw [← card_compl]
          have main : #{c : { x // x ∈ X } → Fin 2 | ∀ x ∈ A, c x = i}
            = Nat.card ({x // x ∈ Aᶜ} → Fin 2) := by
              rw [Nat.card_eq_fintype_card,← card_univ,eq_comm]
              apply card_bij (fun k _ => (fun x => if hx : x ∈ Aᶜ then k ⟨x,hx⟩ else i ))
              · intro k _
                simp only [Subtype.forall, mem_compl, dite_not, mem_filter, mem_univ,
                  dite_eq_left_iff, true_and]
                grind
              · intro k _ q _ H
                rw [funext_iff] at H
                simp only [mem_compl, dite_not, Subtype.forall] at H
                funext x
                specialize H x.val (by simp only [coe_mem])
                rw [dif_neg (by simp only [Subtype.coe_eta] ; exact (mem_compl.mp x.property)),
                  dif_neg (by simp only [Subtype.coe_eta] ; exact (mem_compl.mp x.property))] at H
                convert H
              · intro k kdef
                use (fun x => k x.val)
                simp only [mem_compl, dite_eq_ite, ite_not, mem_univ, exists_const]
                funext x
                grind only [= mem_filter, mem_univ, cases eager Subtype, cases Or]
          rwa [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe] at main
        rw [pow_add,pow_one,mul_two,charaEA,card_disjUnion, cardComp, cardComp]
      simp only [Nat.cast_pow, Nat.cast_ofNat, one_div]
      rw [sizeEA]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv, ENNReal.mul_inv_eq_iff_eq_mul (by simp) (by simp) (by simp)
            (by rw [← show (2 : ENNReal)⁻¹ ^ (d-1) = 2⁻¹ ^ (@Nat.cast ℤ _ (d-1)) from by simp] ; simp)]
      rw [@Nat.cast_sub _ _ 1 d (by omega), Nat.cast_one, ENNReal.inv_zpow' 2 (d-1)]
      rw [show (2 : ENNReal) ^ #X = 2 ^ (#X : ℤ) from by rw [zpow_natCast]]
      rw [show (2 : ENNReal) ^ (#X - #A + 1) = 2 ^ (@Nat.cast ℤ _ (#X - #A + 1)) from by rw [zpow_natCast]]
      rw [← ENNReal.zpow_add (by simp) (by simp)]
      rw [neg_sub, H_𝓕 A hA]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one, @Nat.cast_sub _ _ d #X forComp]
      ring
    · exact Set.Finite.measurableSet <| finite_toSet (E A)
  sorry



/-! Ramsey Numbers and Theorem 2-/

/--
A complete graph `G` on `N` vertices has the Ramsey property `R(m, n)`, if for each two-coloring of
the edges of `G`, either there is a complete subgraph on `m` vertices  of the first color, or there
is a complete subgraph on `n` vertices in the second color. -/
def ramsey_property (m n : ℕ) (N : ℕ) :=
  ∀ c : (completeGraph (Fin N)).edgeSet → Fin 2,
  ( ∃ g : completeGraph (Fin m) →g completeGraph (Fin N), ∀ e : (completeGraph (Fin m)).edgeSet,
      c (g.mapEdgeSet e) = 0 ) ∨
  ( ∃ h : completeGraph (Fin n) →g completeGraph (Fin N), ∀ e : (completeGraph (Fin n)).edgeSet,
    c (h.mapEdgeSet e) = 1 )


lemma ramsey_exists (m n : ℕ) (h_m : m ≥ 2) (h_n : n ≥ 2) : ∃ N, ramsey_property m n N := by
  sorry

/-
The Ramsey Numbers. Noe that this is only defined for `m, n ≥ 2`
Would it make sense to make this not noncomputable?

-- porting note: check what `Inf` was meant here to be able to complete this section

noncomputable def ramsey (m n : ℕ) :=
   Inf {N : ℕ | ramsey_property m n N }

namespace ramsey

lemma symm (m n : ℕ) (h_m : m ≥ 2) (h_n : n ≥ 2) : ramsey m n = ramsey n m := by
  sorry

lemma two (m : ℕ) (h_m : m ≥ 2) : (ramsey m 2) =m := by
  sorry

lemma bound (m n : ℕ) (h_m : m ≥ 3) (h_n : n ≥ 3) :
  ramsey m n ≤ ramsey (m - 1) n + ramsey m (n - 1) := by
  sorry

end ramsey


/--Theorem 2. Lower bound for `ramsey k k`-/
theorem ramsey_geq_two_pow_half (k : ℕ) (h_k : k ≥ 2) :
  (ramsey k k : ℝ) ≥ real.exp ((real.log 2) + (k: ℝ) / 2) := by
  sorry

/-! Theorem 3-/

/-- Chromatic Number of a graph -- Should be introduced in part about Kneser Graphs-/



noncomputable def girth {V : Type _} (G : SimpleGraph V) :=
  Inf {N : ℕ | N ≥ 1 ∧ ∃ (u : V) (W : G.Walk u u), N = W.length ∧ W.IsCycle}

theorem theorem_3 (k : ℕ) (h_k : k ≥ 2) :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.chromaticNumber > k ∧ girth G > k := by
  sorry


/-! Crossing Number and Theorem 4, TODO: Finish Def. of crossing numbers-/
noncomputable def crossing_number {V : Type _} (G: SimpleGraph V) :=
  Inf {N : ℕ | ∃ (c : V → ℝ × ℝ) (f : G.edgeSet → (Set.Icc (0:ℝ) 1) → ℝ × ℝ),
                  Function.Injective c ∧
                  ∀ (e : G.edgeSet) (v : V) (h : v ∈ (e : Sym2 V)),
                    ({v, Sym2.Mem.other h} :Set V).image c = (Coe.coe ⁻¹' ({0,1} : set ℝ)).image (f e) ∧
                    true }
        -- We'd like that at every point in ℝ× ℝ, at most two paths intersect transversally

/-- Theorem 4, TODO: should infer [fintype G.edge_set]-/
theorem theorem_4 {V : Type _} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] (m n : ℕ)
  (H : m ≥ 4 * n) (h_n : n = Fintype.card V) (h_m : m = Fintype.card G.edgeSet) :
  crossing_number G ≥ m ^ 3 / n ^ 2 / 64 := by
  sorry

 -/
