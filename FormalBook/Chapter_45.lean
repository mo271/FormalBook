/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Powerset
--import Mathlib.Analysis.SpecialFunctions.Exp
--import Mathlib.Analysis.SpecialFunctions.Log.Base


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

variable {α : Type _} {X : Finset α}
variable {d : ℕ} {h_d : d ≥ 2}

/-- `𝓕` is a collection of `d`-sets of `X`-/
def two_colorable (𝓕 : Finset (Finset X)) :=
  ∃ c : X → Fin 2, ∀ A : Finset X,
  A ∈ 𝓕 → ∃ x y : A, (c (x : X) = (0 : Fin 2)) ∧ (c y = (1 : Fin 2))

theorem remark_1 {d : ℕ} : ∃ α : Type, ∃ X : Finset α, ∃ 𝓕 : Finset (Finset X), ¬ two_colorable 𝓕 := by
  use ℕ
  use range (2*d - 1)
  use Finset.powersetCard d univ
  unfold two_colorable
  push_neg
  intro c
  wlog majority : (univ.filter (fun x => c x = 0)).card ≥ d
  · sorry
  · sorry


--include H_𝓕 (H_𝓕 : ∀ (A : Finset X), A ∈ 𝓕 → A.card = d)
theorem theorem_1 (𝓕 : Finset (Finset X)) : 𝓕.card ≤ 2 ^ (d-1) → two_colorable 𝓕 :=
  -- Hello World !
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
