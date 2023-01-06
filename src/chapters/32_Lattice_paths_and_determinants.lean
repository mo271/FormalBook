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
import data.rel
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
### Directed Simple Graph
-/
@[ext]
structure directed_simple_graph (V : Type u) := (adj : V → V → Prop)

noncomputable instance {V : Type u} [fintype V] : fintype (directed_simple_graph V) :=
by { classical,
exact fintype.of_injective directed_simple_graph.adj directed_simple_graph.ext,}

namespace directed_simple_graph

variables {V : Type u} {V' : Type v} {V'' : Type w}
variables (G : directed_simple_graph V) (G' : directed_simple_graph V') (G'' : directed_simple_graph V'')
/-
#### Directed Simple Graph Support
-/
/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : set V := rel.dom G.adj

lemma mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.adj v w := iff.rfl
/-
#### Directed Simple Graph Neighbors
-/
/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

instance neighbor_set.mem_decidable (v : V) [decidable_rel G.adj] :
  decidable_pred (∈ G.neighbor_set v) := by { unfold neighbor_set, apply_instance }

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def common_neighbors (v w : V) : set V := G.neighbor_set v ∩ G.neighbor_set w
/-
#### Directed Simple Graph Darts
-/
/- A `dart` is an oriented edge, implemented as an ordered pair of adjacent vertices. -/
@[ext, derive decidable_eq]
structure dart extends V × V :=
(is_adj : G.adj fst snd)

/-- The first vertex for the dart. -/
abbreviation dart.fst (d : G.dart) : V := d.fst

/-- The second vertex for the dart. -/
abbreviation dart.snd (d : G.dart) : V := d.snd

lemma dart.to_prod_injective : function.injective (dart.to_prod : G.dart → V × V) := dart.ext

instance dart.fintype [fintype V] [decidable_rel G.adj] : fintype G.dart :=
fintype.of_equiv (Σ v, G.neighbor_set v)
{ to_fun := λ s, ⟨(s.fst, s.snd), s.snd.property⟩,
  inv_fun := λ d, ⟨d.fst, d.snd, d.is_adj⟩,
  left_inv := λ s, by ext; simp,
  right_inv := λ d, by ext; simp }

/-- The edge associated to the dart. UNNECESSARY ?! But using that for directed_walk.edges -/
def dart.edge (d : G.dart) : V × V := d.to_prod
/-
### Directed Walk
-/
@[derive decidable_eq]
inductive directed_walk : V → V → Type u
| nil {u : V} : directed_walk u u
| cons {u v w: V} (h : G.adj u v) (p : directed_walk v w) : directed_walk u w
/-
#### Directed Walk Nil
-/
attribute [refl] directed_walk.nil

@[simps] instance directed_walk.inhabited (v : V) : inhabited (G.directed_walk v v) := ⟨directed_walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[pattern, reducible] def adj.to_directed_walk {G : directed_simple_graph V} {u v : V} (h : G.adj u v) :
  G.directed_walk u v := directed_walk.cons h directed_walk.nil
/-
#### Directed Walk nil' and cons'
-/
namespace directed_walk

variables {G}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.directed_walk u u := directed_walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.directed_walk v w) :
G.directed_walk u w := directed_walk.cons h p
/-
#### Directed Walk Copy
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
#### Directed Walk Length and Concatenation (Revers [cf. simple_graph.connectivity] is not applyable)
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
#### Directed Walk getting Vertices using Length
-/
/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def get_vert : Π {u v : V} (p : G.directed_walk u v) (n : ℕ), V
| u v nil _ := u
| u v (cons _ _) 0 := u
| u v (cons _ q) (n+1) := q.get_vert n

@[simp] lemma get_vert_zero {u v} (w : G.directed_walk u v) : w.get_vert 0 = u :=
by { cases w; refl }

lemma get_vert_of_length_le {u v} (w : G.directed_walk u v) {i : ℕ} (hi : w.length ≤ i) :
  w.get_vert i = v :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { refl },
  { cases i,
    { cases hi, },
    { exact IH (nat.succ_le_succ_iff.1 hi) } }
end

@[simp] lemma get_vert_length {u v} (w : G.directed_walk u v) : w.get_vert w.length = v :=
w.get_vert_of_length_le rfl.le

lemma adj_get_vert_succ {u v} (w : G.directed_walk u v) {i : ℕ} (hi : i < w.length) :
  G.adj (w.get_vert i) (w.get_vert (i+1)) :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { cases hi, },
  { cases i,
    { simp [get_vert, hxy] },
    { exact IH (nat.succ_lt_succ_iff.1 hi) } },
end
/-
#### Directed Walk Concatenation Lemmata (Reverse [cf. simple_grqaph.connectivity] is not applyable)
-/
@[simp] lemma cons_append {u v w x : V} (h : G.adj u v) (p : G.directed_walk v w) (q : G.directed_walk w x) :
  (cons h p).append q = cons h (p.append q) := rfl

@[simp] lemma cons_nil_append {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h nil).append p = cons h p := rfl

@[simp] lemma append_nil : Π {u v : V} (p : G.directed_walk u v), p.append nil = p
| _ _ nil := rfl
| _ _ (cons h p) := by rw [cons_append, append_nil]

@[simp] lemma nil_append {u v : V} (p : G.directed_walk u v) : nil.append p = p := rfl

lemma append_assoc : Π {u v w x : V} (p : G.directed_walk u v) (q : G.directed_walk v w) (r : G.directed_walk w x),
  p.append (q.append r) = (p.append q).append r
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by { dunfold append, rw append_assoc, }

@[simp] lemma append_copy_copy {u v w u' v' w'} (p : G.directed_walk u v) (q : G.directed_walk v w)
  (hu : u = u') (hv : v = v') (hw : w = w') :
  (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by { subst_vars, refl }
/-
#### Directed Walk Lenght of different "Objects"
-/
@[simp] lemma length_nil {u : V} : (nil : G.directed_walk u u).length = 0 := rfl

@[simp] lemma length_cons {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma length_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).length = p.length :=
by { subst_vars, refl }

@[simp] lemma length_append : Π {u v w : V} (p : G.directed_walk u v) (q : G.directed_walk v w),
  (p.append q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ _) _ := by simp [length_append, add_left_comm, add_comm]

lemma eq_of_length_eq_zero : Π {u v : V} {p : G.directed_walk u v}, p.length = 0 → u = v
| _ _ nil _ := rfl

@[simp] lemma exists_length_eq_zero_iff {u v : V} : (∃ (p : G.directed_walk u v), p.length = 0) ↔ u = v :=
begin
  split,
  { rintro ⟨p, hp⟩,
    exact eq_of_length_eq_zero hp, },
  { rintro rfl,
    exact ⟨nil, rfl⟩, },
end

@[simp] lemma length_eq_zero_iff {u : V} {p : G.directed_walk u u} : p.length = 0 ↔ p = nil :=
by cases p; simp
/-
#### Directed Walk Support, Darts and edges TBC (simple_graph.connectivity l. 294 - 411)
-/
/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.directed_walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts : Π {u v : V}, G.directed_walk u v → list G.dart
| u v nil := []
| u v (cons h p) := ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_directed_graph.directed_walk.darts`. -/
def edges {u v : V} (p : G.directed_walk u v) : list (V × V) := p.darts.map (dart.edge G)

@[simp] lemma support_nil {u : V} : (nil : G.directed_walk u u).support = [u] := rfl

@[simp] lemma support_cons {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).support = u :: p.support := rfl

@[simp] lemma support_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).support = p.support := by { subst_vars, refl }

lemma support_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  (p.append p').support = p.support ++ p'.support.tail :=
by induction p; cases p'; simp [*]

-- first define reverse...
--@[simp]
--lemma support_reverse {u v : V} (p : G.directed_walk u v) : p.reverse.support = p.support.reverse :=
--by induction p; simp [support_append, *]

lemma support_ne_nil {u v : V} (p : G.directed_walk u v) : p.support ≠ [] :=
by cases p; simp

lemma tail_support_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  (p.append p').support.tail = p.support.tail ++ p'.support.tail :=
by rw [support_append, list.tail_append_of_ne_nil _ _ (support_ne_nil _)]

lemma support_eq_cons {u v : V} (p : G.directed_walk u v) : p.support = u :: p.support.tail :=
by cases p; simp

@[simp] lemma start_mem_support {u v : V} (p : G.directed_walk u v) : u ∈ p.support :=
by cases p; simp

@[simp] lemma end_mem_support {u v : V} (p : G.directed_walk u v) : v ∈ p.support :=
by induction p; simp [*]

lemma mem_support_iff {u v w : V} (p : G.directed_walk u v) :
  w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
by cases p; simp

lemma mem_support_nil_iff {u v : V} : u ∈ (nil : G.directed_walk v v).support ↔ u = v := by simp

@[simp]
lemma mem_tail_support_append_iff {t u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail :=
by rw [tail_support_append, list.mem_append]

@[simp] lemma end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.directed_walk u v) :
  v ∈ p.support.tail :=
by { obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p, simp }

@[simp]
lemma mem_support_append_iff {t u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support :=
begin
  simp only [mem_support_iff, mem_tail_support_append_iff],
  by_cases h : t = v; by_cases h' : t = u;
  subst_vars;
  try { have := ne.symm h' };
  simp [*],
end

@[simp]
lemma subset_support_append_left {V : Type u} {G : directed_simple_graph V} {u v w : V}
  (p : G.directed_walk u v) (q : G.directed_walk v w) :
  p.support ⊆ (p.append q).support :=
by simp only [support_append, list.subset_append_left]

@[simp]
lemma subset_support_append_right {V : Type u} {G : directed_simple_graph V} {u v w : V}
  (p : G.directed_walk u v) (q : G.directed_walk v w) :
  q.support ⊆ (p.append q).support :=
by { intro h, simp only [mem_support_append_iff, or_true, implies_true_iff] { contextual := tt }}

lemma coe_support {u v : V} (p : G.directed_walk u v) :
  (p.support : multiset V) = {u} + p.support.tail :=
by cases p; refl

lemma coe_support_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  ((p.append p').support : multiset V) = {u} + p.support.tail + p'.support.tail :=
by rw [support_append, ←multiset.coe_add, coe_support]

lemma coe_support_append' [decidable_eq V] {u v w : V} (p : G.directed_walk u v)
  (p' : G.directed_walk v w) :
    ((p.append p').support : multiset V) = p.support + p'.support - {v} :=
begin
  rw [support_append, ←multiset.coe_add],
  simp only [coe_support],
  rw add_comm {v},
  simp only [← add_assoc, add_tsub_cancel_right],
end

lemma chain_adj_support : Π {u v w : V} (h : G.adj u v) (p : G.directed_walk v w),
  list.chain G.adj u p.support
| _ _ _ h nil := list.chain.cons h list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_adj_support h' p)

lemma chain'_adj_support : Π {u v : V} (p : G.directed_walk u v), list.chain' G.adj p.support
| _ _ nil := list.chain.nil
| _ _ (cons h p) := chain_adj_support h p

lemma chain_dart_adj_darts : Π {d : G.dart} {v w : V} (h : d.snd = v) (p : G.directed_walk v w),
  list.chain G.dart_adj d p.darts
| _ _ _ h nil := list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_dart_adj_darts (by exact rfl) p)

lemma chain'_dart_adj_darts : Π {u v : V} (p : G.directed_walk u v), list.chain' G.dart_adj p.darts
| _ _ nil := trivial
| _ _ (cons h p) := chain_dart_adj_darts rfl p












/-
# TBC
-/
/-
### Directed Walk Support and Edges
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
