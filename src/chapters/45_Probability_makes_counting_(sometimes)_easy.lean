/-
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching
-/
import tactic
import data.finset.basic
import combinatorics.simple_graph.adj_matrix
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.coloring
import combinatorics.simple_graph.connectivity
import order.well_founded_set
import data.set.basic
import analysis.special_functions.exp
import analysis.special_functions.log.base


open simple_graph
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


variables {α : Type*} {X : finset α}
parameters {d : ℕ} {h_d : d ≥ 2}

/-- `𝓕` is a collection of `d`-sets of `X`-/

variables (𝓕 : finset (finset X)) (H_𝓕 : ∀ A : finset X, A ∈ 𝓕 → A.card = d)

def two_colorable :=
  ∃ c : X → fin 2, ∀ A : finset X, A ∈ 𝓕 → ∃ x y : A, c x = 0 ∧ c y = 0

include H_𝓕
theorem theorem_1 : 𝓕.card ≤ 2 ^ (d-1) → two_colorable 𝓕 :=
begin
  sorry,
end

end

/-! Ramsey Numbers and Theorem 2-/


/--
A complete graph `G` on `N` vertices has the Ramsey property `R(m, n)`, if for each two-coloring of
the edges of `G`, either there is a complete subgraph on `m` vertices  of the first color, or there
is a complete subgraph on `n` vertices in the second color. -/
def ramsey_property (m n : ℕ) (N : ℕ) :=
  ∀ c : (complete_graph (fin N)).edge_set → fin 2,
  ( ∃ g : complete_graph (fin m) →g complete_graph (fin N), ∀ e : (complete_graph (fin m)).edge_set,
      c (g.map_edge_set e) = 0 ) ∨
  ( ∃ h : complete_graph (fin n) →g complete_graph (fin N), ∀ e : (complete_graph (fin n)).edge_set,
    c (h.map_edge_set e) = 1 )


lemma ramsey_exists (m n : ℕ) (h_m : m ≥ 2) (h_n : n ≥ 2) : ∃ N, ramsey_property m n N :=
begin
  sorry,
end

/--
The Ramsey Numbers. Noe that this is only defined for `m, n ≥ 2`
Would it make sense to make this not noncomputable?
-/
noncomputable def ramsey (m n : ℕ) :=
   Inf {N : ℕ | ramsey_property m n N }

namespace ramsey

lemma symm (m n : ℕ) (h_m : m ≥ 2) (h_n : n ≥ 2) : ramsey m n = ramsey n m :=
begin
  sorry,
end

lemma two (m : ℕ) (h_m : m ≥ 2) : ramsey m 2 = m :=
begin
  sorry,
end

lemma bound (m n : ℕ) (h_m : m ≥ 3) (h_n : n ≥ 3) :
  ramsey m n ≤ ramsey (m - 1) n + ramsey m (n - 1) :=
begin
  sorry,
end

end ramsey


/--Theorem 2. Lower bound for `ramsey k k`-/
theorem ramsey_geq_two_pow_half (k : ℕ) (h_k : k ≥ 2) :
  (ramsey k k : ℝ) ≥ real.exp ((real.log 2) + (k: ℝ) / 2) :=
begin
  sorry,
end

/-! Theorem 3-/

/-- Chromatic Number of a graph -- Should be introduced in part about Kneser Graphs-/



noncomputable def girth {V : Type*} (G : simple_graph V) :=
  Inf {N : ℕ | N ≥ 1 ∧ ∃ (u : V) (W : G.walk u u), N = W.length ∧ W.is_cycle}

theorem theorem_3 (k : ℕ) (h_k : k ≥ 2) :
  ∃ (n : ℕ) (G : simple_graph (fin n)), G.chromatic_number > k ∧ girth G > k :=
begin
  sorry,
end


/-! Crossing Number and Theorem 4, TODO: Finish Def. of crossing numbers-/
noncomputable def crossing_number {V : Type*} (G: simple_graph V) :=
  Inf {N : ℕ | ∃ (c : V → ℝ × ℝ) (f : G.edge_set → (set.Icc (0:ℝ) 1) → ℝ × ℝ),
                  function.injective c ∧
                  ∀ (e : G.edge_set) (v : V) (h : v ∈ (e : sym2 V)),
                    ({v, sym2.mem.other h} :set V).image c = (coe ⁻¹' ({0,1} : set ℝ)).image (f e) ∧
                    true }
        -- We'd like that at every point in ℝ× ℝ, at most two paths intersect transversally

/-- Theorem 4, TODO: should infer [fintype G.edge_set]-/
theorem theorem_4 {V : Type*} [fintype V] (G : simple_graph V) [fintype G.edge_set] (m n : ℕ)
  (H : m ≥ 4 * n) (h_n : n = fintype.card V) (h_m : m = fintype.card G.edge_set) :
  crossing_number G ≥ m ^ 3 / n ^ 2 / 64 :=
begin
  sorry,
end