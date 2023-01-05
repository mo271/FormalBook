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

Authors: Moritz Firsching, Christopher Schmidt
-/
import tactic
/-!
# Lattice paths and determinants

## TODO

 - missing definitions:
  - simple directed graphs (trivial to do)
    - acyclic 
    - weights on edge set (trivial to do)
    - Path
    - definition for weight of Path 
  - path matrix
  - path system from A to B
  - weight of path system
  - vertex disjoint


  - Lemma
    - proof
  - Theorem
    - proof

## Defining missing Objects
proceed analogous to combinatorics.simple_graph
-/
open function 

universes u v w
/-
### Simple Directed Graphs 
-/
@[ext]
structure directed_simple_graph (V : Type u) := (adj : V → V → Prop)

noncomputable instance {V : Type u} [fintype V] : fintype (directed_simple_graph V) :=
by { classical,
exact fintype.of_injective directed_simple_graph.adj directed_simple_graph.ext,}
/-
### Directed Walk
-/
namespace directed_simple_graph

variables {V : Type u} {V' : Type v} {V'' : Type w}
variables (G : directed_simple_graph V) (G' : directed_simple_graph V') (G'' : directed_simple_graph V'')

@[derive decidable_eq]
inductive directed_walk : V → V → Type u
| nil {u : V} : directed_walk u u
| cons {u v w: V} (h : G.adj u v) (p : directed_walk v w) : directed_walk u w
/-
### Directed Walk's Attributes
-/
attribute [refl] directed_walk.nil

@[simps] instance directed_walk.inhabited (v : V) : inhabited (G.directed_walk v v) := ⟨directed_walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[pattern, reducible] def adj.to_directed_walk {G : directed_simple_graph V} {u v : V} (h : G.adj u v) : 
  G.directed_walk u v := directed_walk.cons h directed_walk.nil
/-
### Directed Walk's Patterns
-/
namespace directed_walk

variables {G}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.directed_walk u u := directed_walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.directed_walk v w) :
G.directed_walk u w := directed_walk.cons h p
/-
### Directed Walk's Lemmata 
-/
/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `eq.rec`, it gives a canonical way to write it.
The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') : G.directed_walk u' v' :=
eq.rec (eq.rec p hv) hu

@[simp] lemma copy_rfl_rfl {u v} (p : G.directed_walk u v) :
  p.copy rfl rfl = p := rfl

@[simp] lemma copy_copy {u v u' v' u'' v''} (p : G.directed_walk u v)
  (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
  (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') :=
by { subst_vars, refl }

@[simp] lemma copy_nil {u u'} (hu : u = u') : (directed_walk.nil : G.directed_walk u u).copy hu hu = directed_walk.nil :=
by { subst_vars, refl }

lemma copy_cons {u v w u' w'} (h : G.adj u v) (p : G.directed_walk v w) (hu : u = u') (hw : w = w') :
  (directed_walk.cons h p).copy hu hw = directed_walk.cons (by rwa ← hu) (p.copy rfl hw) :=
by { subst_vars, refl }

@[simp]
lemma cons_copy {u v w v' w'} (h : G.adj u v) (p : G.directed_walk v' w') (hv : v' = v) (hw : w' = w) :
  directed_walk.cons h (p.copy hv hw) = (directed_walk.cons (by rwa hv) p).copy rfl hw :=
by { subst_vars, refl }

lemma exists_eq_cons_of_ne : Π {u v : V} (hne : u ≠ v) (p : G.directed_walk u v),
  ∃ (w : V) (h : G.adj u w) (p' : G.directed_walk w v), p = cons h p'
| _ _ hne nil := (hne rfl).elim
| _ _ _ (cons h p') := ⟨_, h, p', rfl⟩
/-
### Directed Walk's Length and Concatenation (Revers [cf. simple_graph.connectivity] is not applyable)
-/
/-- The length of a walk is the number of edges/darts along it. -/
def length : Π {u v : V}, G.directed_walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : Π {u v w : V}, G.directed_walk u v → G.directed_walk v w → G.directed_walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (p.append q)
/-
### Directed Walk's ... TBC (simple_graph.connectivity l. 163 - 195)
-/
/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def get_vert : Π {u v : V} (p : G.walk u v) (n : ℕ), V
| u v nil _ := u
| u v (cons _ _) 0 := u
| u v (cons _ q) (n+1) := q.get_vert n

@[simp] lemma get_vert_zero {u v} (w : G.walk u v) : w.get_vert 0 = u :=
by { cases w; refl }

lemma get_vert_of_length_le {u v} (w : G.walk u v) {i : ℕ} (hi : w.length ≤ i) :
  w.get_vert i = v :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { refl },
  { cases i,
    { cases hi, },
    { exact IH (nat.succ_le_succ_iff.1 hi) } }
end

@[simp] lemma get_vert_length {u v} (w : G.walk u v) : w.get_vert w.length = v :=
w.get_vert_of_length_le rfl.le

lemma adj_get_vert_succ {u v} (w : G.walk u v) {i : ℕ} (hi : i < w.length) :
  G.adj (w.get_vert i) (w.get_vert (i+1)) :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { cases hi, },
  { cases i,
    { simp [get_vert, hxy] },
    { exact IH (nat.succ_lt_succ_iff.1 hi) } },
end


/-
# TBC
-/
/-
### Directed Walk's Properties (Support, Edges)
-/
/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.directed_walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. 
This is defined to be the list of edges underlying `simple_graph.walk.darts`. -/
def edges : Π {u v : V} (p : G.directed_walk u v) : list (V × V) :=
| u v nil := []
| u v (cons h p) := (u, v) :: p.edges
/-
### Directed Trail
-/
/-- A `directed_trail` is a directed_walk with no repeating edges. -/
structure is_trail {u v : V} (p : G.directed_walk u v) : Prop :=
(edges_nodup : p.edges.nodup)

/-
### Directed Path
-/
/-- A `directed_path` is a directed_walk with no repeating vertices. -/
structure is_path {u v : V} (p : G.directed_walk u v) extends to_trail : is_trail p : Prop :=
(support_nodup : p.support.nodup)

end directed_walk

end directed_simple_graph


/- 
### Weights for Simple Directed Graphs
-/
universe x
variables {W : Type x}
def weight (v1 v2 : V) : V → V → W := sorry