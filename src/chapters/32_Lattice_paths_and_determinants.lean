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
import data.real.basic
import data.list.defs
import logic.equiv.defs
import group_theory.perm.sign 

--open finset 
open_locale big_operators 
/-!
# Lattice paths and determinants

## TODO

 - missing definitions:
  - simple directed graphs (trivial to do)
    - acyclic
    - weights on edge set (trivial to do)
    - definition for weight of Path
  - path matrix
  - path system from A to B
  - weight of path system
  - vertex disjoint


  - Lemma
    - proof
  - Theorem
    - proof

## Defining missing Objects analogous to mathlib (cf. simple_graphs)
-/
open function

universes u v 
/-
### Directed Simple Graph
-/
/-- A `directed simple graph`. -/
@[ext]
structure directed_simple_graph (V : Type u) := (adj : V → V → Prop)

noncomputable instance {V : Type u} [fintype V] : fintype (directed_simple_graph V) :=
by { classical,
exact fintype.of_injective directed_simple_graph.adj directed_simple_graph.ext,}

namespace directed_simple_graph

variables {V : Type u} {V' : Type v}
variables (G : directed_simple_graph V) (G' : directed_simple_graph V')
/-
#### Directed Loopless Simple Graph (no self adjacency)
-/
/-- A `directed loopless simple graph`. -/
@[ext]
structure directed_loopless_simple_graph (V : Type u) extends directed_simple_graph V :=
(loopless : irreflexive adj . obviously)

namespace directed_loopless_simple_graphs

variables {a b : V} 
variables {g : directed_loopless_simple_graph V}

@[simp] protected lemma irrefl {v : V} : ¬g.adj v v := g.loopless v 

lemma ne_of_adj (h : g.adj a b) : a ≠ b := by { rintro rfl, exact directed_loopless_simple_graphs.irrefl h}

protected lemma adj.ne {g : directed_loopless_simple_graph V} {a b : V} (h : g.adj a b) : a ≠ b := ne_of_adj h

protected lemma adj.ne' {g : directed_loopless_simple_graph V} {a b : V} (h : g.adj a b) : b ≠ a := (adj.ne h).symm

end directed_loopless_simple_graphs
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

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
@[reducible]
def locally_finite := Π (v : V), fintype (G.neighbor_set v)

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
iff.rfl
/-
#### Directed Simple Graph Dart
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

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def dart_adj (d d' : G.dart) : Prop := d.snd = d'.fst
/-
#### Directed Simple Graph Edge Set 
-/
/-- Give `directed_simple_graph V` the induced partial order from the one already defined on  `V → V → Prop`. -/
instance : partial_order (directed_simple_graph V) := partial_order.lift adj ext

def edge_set : directed_simple_graph V ↪o set (V × V) :=
order_embedding.of_map_le_iff (λ (G : directed_simple_graph V), {p : V × V | G.adj p.1 p.2}) $
begin
  intros G G',
  rw [set.le_eq_subset, set.set_of_subset_set_of, prod.forall],
  refl,
end

@[simp] lemma mem_edge_set {v w : V} : (v, w) ∈ G.edge_set ↔ G.adj v w := iff.rfl

/-- `from_edge_set` constructs a `directed_simple_graph` from a set of edges. -/
@[simps] 
def from_edge_set (s : set (V × V)) : directed_simple_graph V := 
{ adj := λ v w, (v, w) ∈ s }
/-
#### Directed Simple Graph Edge Deletion 
-/
/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : has_sdiff (directed_simple_graph V) := ⟨λ x y, { adj := x.adj \ y.adj,}⟩

/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present. -/
def delete_edges (s : set (V × V)) : directed_simple_graph V := G \ from_edge_set s

@[simp] lemma adj_sdiff (G G' : directed_simple_graph V) (v w : V) :
  (G \ G').adj v w ↔ G.adj v w ∧ ¬ G'.adj v w := iff.rfl

@[simp] lemma delete_edges_adj (s : set (V × V)) (v w : V) :
  (G.delete_edges s).adj v w ↔ G.adj v w ∧ ¬ (v,w) ∈ s := iff.rfl

@[simp] lemma delete_edges_delete_edges (s s' : set (V × V)) :
  (G.delete_edges s).delete_edges s' = G.delete_edges (s ∪ s') :=
by { ext, simp [and_assoc, not_or_distrib] }

@[simp] lemma delete_edges_empty_eq : G.delete_edges ∅ = G :=
by { ext, simp }

instance : has_bot (directed_simple_graph V) := ⟨{ adj := ⊥ }⟩

@[simp]
lemma not_adj_bot (v w : V) : ¬ (⊥ : directed_simple_graph V).adj v w := false.elim

@[simp] lemma delete_edges_univ_eq : G.delete_edges set.univ = ⊥ :=
by { ext, simp }
/-
#### Directed Simple Graphs Maps
-/
section maps 
/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.
The notation `G →g G'` represents the type of graph homomorphisms. -/
abbreviation hom := rel_hom G.adj G'.adj

/--
A graph embedding is an embedding `f` such that for vertices `v w : V`, `G.adj f(v) f(w) ↔ G.adj v w `. 
Its image is an induced subgraph of G'. The notation `G ↪g G'` represents the type of graph embeddings. -/
abbreviation embedding := rel_embedding G.adj G'.adj

/--
A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.
The notation `G ≃g G'` represents the type of graph isomorphisms. -/
abbreviation iso := rel_iso G.adj G'.adj

infix ` →g ` : 50 := hom
infix ` ↪g ` : 50 := embedding
infix ` ≃g ` : 50 := iso

namespace hom 
variables {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbreviation id : G →g G := rel_hom.id _

lemma map_adj {v w : V} (h : G.adj v w) : G'.adj (f v) (f w) := f.map_rel' h

end hom

end maps 

end directed_simple_graph
/-
#### Directed Simple Subgraph
-/
namespace directed_simple_graph

/-- A subgraph of a `directed_simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.
Thinking of `V → V → Prop` as `set (V × V)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure directed_subgraph {V : Type u} (G : directed_simple_graph V) extends directed_simple_graph V :=
(verts : set V)
(adj_sub : ∀ {v w : V}, adj v w → G.adj v w)
(edge_vert : ∀ {v w : V}, adj v w → v ∈ verts ∧ w ∈ verts)

variables {V : Type u}

/-- The one-vertex subgraph. -/
@[simps]
protected def singleton_directed_subgraph (G : directed_simple_graph V) (v : V) : G.directed_subgraph :=
{ verts := {v},
  adj := ⊥,
  adj_sub := by simp [-set.bot_eq_empty],
  edge_vert := by simp [-set.bot_eq_empty] }

/-- The one-edge subgraph. -/
@[simps]
def directed_subgraph_of_adj (G : directed_simple_graph V) {v w : V} (hvw : G.adj v w) : G.directed_subgraph :=
{ verts := {v, w},
  adj := λ a b, (v, w) = (a, b),
  adj_sub := λ a b h, by 
  { simp only [prod.mk.inj_iff] at h,
    rw [←h.1, ← h.2],
    exact hvw, },
  edge_vert := λ a b h, by 
  { simp only [set.mem_insert_iff, set.mem_singleton_iff], 
    simp only [prod.mk.inj_iff] at h,
    split, 
    { left, exact eq.symm h.1},
    { right, exact eq.symm h.2}, }}

namespace directed_subgraph

variables (G : directed_simple_graph V)

protected lemma adj.adj_sub {H : G.directed_subgraph} {u v : V} (h : H.adj u v) : G.adj u v := 
H.adj_sub h

protected lemma adj.fst_mem {H : G.directed_subgraph} {u v : V} (h : H.adj u v) : u ∈ H.verts :=
(H.edge_vert h).1

protected lemma adj.snd_mem {H : G.directed_subgraph} {u v : V} (h : H.adj u v) : v ∈ H.verts :=
(H.edge_vert h).2

/-- Coercion from `G' : directed_subgraph G` to a `directed_simple_graph ↥G'.verts`. -/
@[simps] protected def coe (G' : directed_subgraph G) : directed_simple_graph G'.verts :=
{adj := λ v w, G'.adj v w}

@[simp] lemma coe_adj_sub (G' : directed_subgraph G) (u v : G'.verts) (h : (G'.coe G).adj u v) : G.adj u v :=
G'.adj_sub h

/- Given `h : H.adj u v`, then `h.coe : H.coe.adj ⟨u, _⟩ ⟨v, _⟩`. -/
protected lemma adj.coe {H : G.directed_subgraph} {u v : V} (h : H.adj u v) :
  (H.coe G).adj ⟨u, (H.edge_vert h).1⟩ ⟨v, (H.edge_vert h).2⟩ := h

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def is_spanning (G' : directed_subgraph G) : Prop := ∀ (v : V), v ∈ G'.verts

lemma is_spanning_iff {G' : directed_subgraph G} : G'.is_spanning G ↔ G'.verts = set.univ :=
set.eq_univ_iff_forall.symm

/-- Coercion from `subgraph G` to `directed_simple_graph V`.  If `G'` is a spanning
subgraph, then `G'.spanning_coe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps] protected def spanning_coe (G' : directed_subgraph G) : directed_simple_graph V :=
{ adj := G'.adj}

@[simp] lemma adj.of_spanning_coe {G' : directed_subgraph G} {u v : G'.verts}
  (h : (G'.spanning_coe G).adj u v) : G.adj u v := G'.adj_sub h

@[simps] def spanning_coe_equiv_coe_of_spanning (G' : directed_subgraph G) (h : is_spanning G G') :
  G'.spanning_coe G  ≃g G'.coe G :=
{ to_fun := λ v, ⟨v, h v⟩,
  inv_fun := λ v, v,
  left_inv := λ v, rfl,
  right_inv := λ ⟨v, hv⟩, rfl,
  map_rel_iff' := λ v w, iff.rfl }

/-- The relation that one subgraph is a subgraph of another. -/
def is_directed_subgraph (x y : directed_subgraph G) : Prop := x.verts ⊆ y.verts ∧ ∀ {v w : V}, x.adj v w → y.adj v w

/-- The union of two subgraphs. -/
def union (x y : directed_subgraph G) : directed_subgraph G :=
{ verts := x.verts ∪ y.verts,
  adj := x.adj ⊔ y.adj,
  adj_sub := λ v w h, or.cases_on h (λ h, x.adj_sub h) (λ h, y.adj_sub h),
  edge_vert := λ v w h, by
  { simp only [set.mem_union],
    simp only [pi.sup_apply, set.sup_eq_union] at h,
    cases h with p q;
    split,
    { left, exact (x.edge_vert p).1, },
    { left, exact (x.edge_vert p).2, }, 
    { right, exact (y.edge_vert q).1, },
    { right, exact (y.edge_vert q).2, }, }, }

/-- The intersection of two subgraphs. -/
def inter (x y : directed_subgraph G) : directed_subgraph G :=
{ verts := x.verts ∩ y.verts,
  adj := x.adj ⊓ y.adj,
  adj_sub := λ v w h, x.adj_sub h.1,
  edge_vert := λ v w h, by 
  { simp only [set.mem_inter_iff],
    simp only [pi.inf_apply, set.inf_eq_inter] at h,
    cases h with p q;
    split;
    split,
    { exact (x.edge_vert p).1, },
    { exact (y.edge_vert q).1, }, 
    { exact (x.edge_vert p).2, },
    { exact (y.edge_vert q).2, }, }, }
  --⟨x.edge_vert h.1, y.edge_vert h.2⟩ }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : directed_subgraph G :=
{ verts := set.univ,
  adj := G.adj,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, by
  { simp only [set.mem_univ, and_self], }, }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : directed_subgraph G :=
{ verts := ∅,
  adj := ⊥,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h}

instance : lattice (directed_subgraph G) :=
{ le := is_directed_subgraph G,
  sup := union G,
  inf := inter G,
  le_refl := λ x, ⟨rfl.subset, λ _ _ h, h⟩,
  le_trans := λ x y z hxy hyz, ⟨hxy.1.trans hyz.1, λ _ _ h, hyz.2 (hxy.2 h)⟩,
  le_antisymm := begin
    intros x y hxy hyx,
    ext1 v,
    { ext v w,
      exact iff.intro (λ h, hxy.2 h) (λ h, hyx.2 h), },
    { exact set.subset.antisymm hxy.1 hyx.1, },
  end,
  sup_le := λ x y z hxy hyz,
            ⟨set.union_subset hxy.1 hyz.1,
              (λ v w h, h.cases_on (λ h, hxy.2 h) (λ h, hyz.2 h))⟩,
  le_sup_left := λ x y, ⟨set.subset_union_left x.verts y.verts, (λ v w h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.verts y.verts, (λ v w h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ v w h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.verts y.verts, (λ v w h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.verts y.verts, (λ v w h, h.2)⟩ }

end directed_subgraph 

end directed_simple_graph
/-
### Directed Walk
-/
namespace directed_simple_graph

variables {V : Type u} {V' : Type v}
variables (G : directed_simple_graph V) (G' : directed_simple_graph V)

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
### Acyclic Graph
-/
/-- A `directed acyclic simple graph`.-/
@[ext]
structure directed_acyclic_simple_graph {u : V}(V : Type u) 
  extends directed_loopless_simple_graph V :=
(acyclic : ∀ p : G.directed_walk u u, p = nil)
/-
#### Directed Walk to Graph
-/
/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp] protected def to_directed_subgraph : Π {u v : V}, G.directed_walk u v → G.directed_subgraph
| u _ nil := G.singleton_directed_subgraph u
| _ _ (cons h p) := G.directed_subgraph_of_adj h ⊔ p.to_directed_subgraph

@[simp] protected def to_directed_graph {u v : V} (p : G.directed_walk u v) : directed_simple_graph V :=
p.to_directed_subgraph.to_directed_simple_graph 
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
#### Directed Walk Concatenation Lemmata (Reverse [cf. simple_graph.connectivity] is not applyable)
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
#### Directed Walk Support, Darts, Edges, Edges Set
-/
/-- The `support` of a directed walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.directed_walk u v → list V
| u _ nil := [u]
| u _ (cons h p) := u :: p.support

/-- The `darts` of a directed walk is the list of darts it visits in order. -/
def darts : Π {u v : V}, G.directed_walk u v → list G.dart
| u v nil := []
| u v (cons h p) := ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a directed walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_directed_graph.directed_walk.darts`. -/
def edges {u v : V} (p : G.directed_walk u v) : list (V × V) := p.darts.map (dart.edge G) 
/-
#### Directed Walk Support Lemmata
-/
@[simp] lemma support_nil {u : V} : (nil : G.directed_walk u u).support = [u] := rfl

@[simp] lemma support_cons {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).support = u :: p.support := rfl

@[simp] lemma support_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).support = p.support := by { subst_vars, refl }

lemma support_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  (p.append p').support = p.support ++ p'.support.tail :=
by induction p; cases p'; simp [*]

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

@[simp] lemma support_nonempty {u v : V} (p : G.directed_walk u v) : {w | w ∈ p.support}.nonempty :=
⟨u, by simp⟩

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
/-
#### Directed Walk Darts Lemmata
-/
lemma chain_dart_adj_darts : Π {d : G.dart} {v w : V} (h : d.snd = v) (p : G.directed_walk v w),
  list.chain G.dart_adj d p.darts
| _ _ _ h nil := list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_dart_adj_darts (by exact rfl) p)

lemma chain'_dart_adj_darts : Π {u v : V} (p : G.directed_walk u v), list.chain' G.dart_adj p.darts
| _ _ nil := trivial
| _ _ (cons h p) := chain_dart_adj_darts rfl p
/-
#### Directed Walk Edges Lemmata
-/
/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
lemma edges_subset_edge_set : Π {u v : V} (p : G.directed_walk u v) ⦃e : V × V⦄
  (h : e ∈ p.edges), e ∈ G.edge_set
| _ _ (cons h' p') e h := by rcases h with ⟨rfl, h⟩; solve_by_elim

lemma adj_of_mem_edges {u v x y : V} (p : G.directed_walk u v) (h : (x, y) ∈ p.edges) : G.adj x y :=
edges_subset_edge_set p h
/-
#### Directed Walk Darts Lemmata (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
@[simp] lemma darts_nil {u : V} : (nil : G.directed_walk u u).darts = [] := rfl

@[simp] lemma darts_cons {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

@[simp] lemma darts_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).darts = p.darts := by { subst_vars, refl }

@[simp] lemma darts_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  (p.append p').darts = p.darts ++ p'.darts :=
by induction p; simp [*]

lemma cons_map_snd_darts {u v : V} (p : G.directed_walk u v) :
  u :: p.darts.map (dart.snd G) = p.support :=
by induction p; simp! [*]

lemma map_snd_darts {u v : V} (p : G.directed_walk u v) :
  p.darts.map (dart.snd G)= p.support.tail :=
by simpa using congr_arg list.tail (cons_map_snd_darts p)

lemma map_fst_darts_append {u v : V} (p : G.directed_walk u v) :
  p.darts.map (dart.fst G) ++ [v] = p.support :=
by induction p; simp! [*]

lemma map_fst_darts {u v : V} (p : G.directed_walk u v) :
  p.darts.map (dart.fst G) = p.support.init :=
by simpa! using congr_arg list.init (map_fst_darts_append p)
/-
#### Directed Walk Edges Lemmata (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
@[simp] lemma edges_nil {u : V} : (nil : G.directed_walk u u).edges = [] := rfl

@[simp] lemma edges_cons {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).edges = (u, v) :: p.edges := rfl

@[simp] lemma edges_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).edges = p.edges := by { subst_vars, refl }

@[simp] lemma edges_append {u v w : V} (p : G.directed_walk u v) (p' : G.directed_walk v w) :
  (p.append p').edges = p.edges ++ p'.edges :=
by simp [edges]
/-
#### Directed Walk Length of Support, Darts and Edges
-/
@[simp] lemma length_support {u v : V} (p : G.directed_walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma length_darts {u v : V} (p : G.directed_walk u v) : p.darts.length = p.length :=
by induction p; simp *

@[simp] lemma length_edges {u v : V} (p : G.directed_walk u v) : p.edges.length = p.length :=
by simp [edges]
/-
#### Directed Walk Membership
-/
lemma dart_fst_mem_support_of_mem_darts :
  Π {u v : V} (p : G.directed_walk u v) {d : G.dart}, d ∈ p.darts → d.fst ∈ p.support
| u v (cons h p') d hd := 
begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { exact or.inl rfl, },
  { exact or.inr (dart_fst_mem_support_of_mem_darts _ hd), },
end

lemma dart_snd_mem_support_of_mem_darts :
  Π {u v : V} (p : G.directed_walk u v) {d : G.dart}, d ∈ p.darts → d.snd ∈ p.support
| u v (cons h p') d hd := 
begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { sorry, },
  { sorry, },
end

/- Helpfull Lemmata -/
lemma dart_edge_eq_mk_iff : Π {d : G.dart} {p : V × V},
  d.edge G = p ↔ d.to_prod = p :=
begin 
  rintros ⟨p, h⟩,
  simp only [prod.forall],  
  intros p1 p2,
  refl,
end

lemma dart_edge_eq_mk_iff' : Π {d : G.dart} {u v : V},
  d.edge G = (u, v) ↔ d.fst = u ∧ d.snd = v :=
by { rintro ⟨ ⟨a, b⟩, h⟩ u v, rw dart_edge_eq_mk_iff, simp only [prod.mk.inj_iff]}
/- Being able to continue -/

lemma fst_mem_support_of_mem_edges {t u v w : V} (p : G.directed_walk v w) (he : (t, u) ∈ p.edges) :
  t ∈ p.support :=
begin
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he,
  rw dart_edge_eq_mk_iff' at he,
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  exact dart_fst_mem_support_of_mem_darts _ hd, 
end

lemma snd_mem_support_of_mem_edges {t u v w : V} (p : G.directed_walk v w) (he : (t, u) ∈ p.edges) :
  u ∈ p.support :=
begin
  obtain ⟨d , hd, he⟩ := list.mem_map.mp he,
  rw dart_edge_eq_mk_iff' at he,
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  rw ← he_right,
  exact dart_snd_mem_support_of_mem_darts _ hd,
end

lemma darts_nodup_of_support_nodup {u v : V} {p : G.directed_walk u v} (h : p.support.nodup) :
  p.darts.nodup :=
begin
  induction p,
  { simp, },
  { simp only [darts_cons, support_cons, list.nodup_cons] at h ⊢,
    refine ⟨λ h', h.1 (dart_fst_mem_support_of_mem_darts p_p h'), p_ih h.2⟩, }
end

lemma edges_nodup_of_support_nodup {u v : V} {p : G.directed_walk u v} (h : p.support.nodup) :
  p.edges.nodup :=
begin
  induction p,
  { simp, },
  { simp only [edges_cons, support_cons, list.nodup_cons] at h ⊢,
    exact ⟨λ h', h.1 (fst_mem_support_of_mem_edges p_p h'), p_ih h.2⟩, }
end
/-
### Is Directed Trail, Path, Circuit, Cycle
-/
/-- A `directed_trail` is a directed walk with no repeating edges. -/
structure is_directed_trail {u v : V} (p : G.directed_walk u v) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A `directed_path` is a directed walk with no repeating vertices. -/
structure is_directed_path {u v : V} (p : G.directed_walk u v) extends to_directed_trail : is_directed_trail p : Prop :=
(support_nodup : p.support.nodup)

/-- A `directed_circuit` at `u : V` is a nonempty directed trail beginning and ending at `u`. -/
structure is_directed_circuit {u : V} (p : G.directed_walk u u) extends to_directed_trail : is_directed_trail p : Prop :=
(ne_nil : p ≠ nil)

/-- A `directed_cycle` at `u : V` is a directed circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_directed_cycle {u : V} (p : G.directed_walk u u)
  extends to_directed_circuit : is_directed_circuit p : Prop :=
(support_nodup : p.support.tail.nodup)
/-
#### Directed Trail, Path, Circuit, Cycle Definitional Lemmata
-/
lemma is_directed_trail_def {u v : V} (p : G.directed_walk u v) : p.is_directed_trail ↔ p.edges.nodup :=
⟨is_directed_trail.edges_nodup, λ h, ⟨h⟩⟩

@[simp] lemma is_directed_trail_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).is_directed_trail ↔ p.is_directed_trail := by { subst_vars, refl }

lemma is_directed_path.mk' {u v : V} {p : G.directed_walk u v} (h : p.support.nodup) : is_directed_path p :=
⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

lemma is_directed_path_def {u v : V} (p : G.directed_walk u v) : p.is_directed_path ↔ p.support.nodup :=
⟨is_directed_path.support_nodup, is_directed_path.mk'⟩

@[simp] lemma is_directed_path_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).is_directed_path ↔ p.is_directed_path := by { subst_vars, refl }

lemma is_directed_circuit_def {u : V} (p : G.directed_walk u u) :
  p.is_directed_circuit ↔ is_directed_trail p ∧ p ≠ nil :=
iff.intro (λ h, ⟨h.1, h.2⟩) (λ h, ⟨h.1, h.2⟩)

@[simp] lemma is_directed_circuit_copy {u u'} (p : G.directed_walk u u) (hu : u = u') :
  (p.copy hu hu).is_directed_circuit ↔ p.is_directed_circuit := by { subst_vars, refl }

lemma is_directed_cycle_def {u : V} (p : G.directed_walk u u) :
  p.is_directed_cycle ↔ is_directed_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

@[simp] lemma is_directed_cycle_copy {u u'} (p : G.directed_walk u u) (hu : u = u') :
  (p.copy hu hu).is_directed_cycle ↔ p.is_directed_cycle := by { subst_vars, refl }
/-
#### Directed Trail Lemmata (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
@[simp] lemma is_directed_trail.nil {u : V} : (nil : G.directed_walk u u).is_directed_trail :=
⟨by simp [edges]⟩

lemma is_directed_trail.of_cons {u v w : V} {h : G.adj u v} {p : G.directed_walk v w} :
  (cons h p).is_directed_trail → p.is_directed_trail :=
by simp [is_directed_trail_def]

@[simp] lemma cons_is_directed_trail_iff {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).is_directed_trail ↔ p.is_directed_trail ∧ (u, v) ∉ p.edges :=
by simp [is_directed_trail_def, and_comm]

lemma is_directed_trail.of_append_left {u v w : V} {p : G.directed_walk u v} {q : G.directed_walk v w}
  (h : (p.append q).is_directed_trail) : p.is_directed_trail :=
by { rw [is_directed_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.1⟩ }

lemma is_directed_trail.of_append_right {u v w : V} {p : G.directed_walk u v} {q : G.directed_walk v w}
  (h : (p.append q).is_directed_trail) : q.is_directed_trail :=
by { rw [is_directed_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.2.1⟩ }

lemma is_directed_trail.count_edges_le_one [decidable_eq V] {u v : V}
  {p : G.directed_walk u v} (h : p.is_directed_trail) (e : V × V) : p.edges.count e ≤ 1 :=
list.nodup_iff_count_le_one.mp h.edges_nodup e

lemma is_directed_trail.count_edges_eq_one [decidable_eq V] {u v : V}
  {p : G.directed_walk u v} (h : p.is_directed_trail) {e : V × V} (he : e ∈ p.edges) :
  p.edges.count e = 1 :=
list.count_eq_one_of_mem h.edges_nodup he
/-
#### Directed Path Lemmata (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
lemma is_directed_path.nil {u : V} : (nil : G.directed_walk u u).is_directed_path :=
by { fsplit; simp }

lemma is_directed_path.of_cons {u v w : V} {h : G.adj u v} {p : G.directed_walk v w} :
  (cons h p).is_directed_path → p.is_directed_path :=
by simp [is_directed_path_def]

@[simp] lemma cons_is_directed_path_iff {u v w : V} (h : G.adj u v) (p : G.directed_walk v w) :
  (cons h p).is_directed_path ↔ p.is_directed_path ∧ u ∉ p.support :=
by split; simp [is_directed_path_def] { contextual := tt }

@[simp] lemma is_directed_path_iff_eq_nil {u : V} (p : G.directed_walk u u) : p.is_directed_path ↔ p = nil :=
by { cases p; simp [is_directed_path.nil] }

lemma is_directed_path.of_append_left {u v w : V} {p : G.directed_walk u v} {q : G.directed_walk v w} :
  (p.append q).is_directed_path → p.is_directed_path :=
by { simp only [is_directed_path_def, support_append], exact list.nodup.of_append_left }

lemma is_directed_path.of_append_right {u v w : V} {p : G.directed_walk u v} {q : G.directed_walk v w} :
  (p.append q).is_directed_path → q.is_directed_path :=
begin
  simp only [is_directed_path_def],
  simp only [support_append],
  --have h : p.support ++ q.support.tail = (p.support - {v}) ++ q.support := by
  { sorry, }
end
/-
#### Directed Cycle Lemmata
-/
@[simp] lemma is_directed_cycle.not_of_nil {u : V} : ¬ (nil : G.directed_walk u u).is_directed_cycle :=
λ h, h.ne_nil rfl

lemma cons_is_directed_cycle_iff {u v : V} (p : G.directed_walk v u) (h : G.adj u v) :
  (directed_walk.cons h p).is_directed_cycle ↔ p.is_directed_path ∧ ¬ (u, v) ∈ p.edges :=
begin
  simp only [directed_walk.is_directed_cycle_def, directed_walk.is_directed_path_def, directed_walk.is_directed_trail_def, edges_cons, list.nodup_cons,
             support_cons, list.tail_cons],
  have : p.support.nodup → p.edges.nodup := edges_nodup_of_support_nodup,
  tauto,
end
/-
#### Directed Path Instance
-/
instance [decidable_eq V] {u v : V} (p : G.directed_walk u v) : decidable p.is_directed_path :=
by { rw is_directed_path_def, apply_instance }

lemma is_directed_path.length_lt [fintype V] {u v : V} {p : G.directed_walk u v} (hp : p.is_directed_path) :
  p.length < fintype.card V :=
by { rw [nat.lt_iff_add_one_le, ← length_support], exact hp.support_nodup.length_le_card }
/- 
### Decompositions of Directed Walks
-/
section directed_walk_decomp
variables [decidable_eq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def take_until : Π {v w : V} (p : G.directed_walk v w) (u : V) (h : u ∈ p.support), G.directed_walk v u
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by subst u
  else cons r (take_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def drop_until : Π {v w : V} (p : G.directed_walk v w) (u : V) (h : u ∈ p.support), G.directed_walk u w
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by { subst u, exact cons r p }
  else drop_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id

/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
lemma take_spec {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).append (p.drop_until u h) = p :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    refl, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; subst_vars; simp [*], } },
end

lemma mem_support_iff_exists_append {V : Type u} {G : directed_simple_graph V} {u v w : V}
  {p : G.directed_walk u v} :
  w ∈ p.support ↔ ∃ (q : G.directed_walk u w) (r : G.directed_walk w v), p = q.append r :=
begin
  classical,
  split,
  { exact λ h, ⟨_, _, (p.take_spec h).symm⟩ },
  { rintro ⟨q, r, rfl⟩,
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self], },
end

@[simp]
lemma count_support_take_until_eq_one {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support.count u = 1 :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; rw eq_comm at h'; subst_vars; simp! [*, list.count_cons], } },
end

lemma count_edges_take_until_le_one {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) (x : V) :
  (p.take_until u h).edges.count (u, x) ≤ 1 :=
begin
  induction p with u' u' v' w' ha p' ih,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp!, },
    { simp! only,
      split_ifs with h',
      { subst h',
        simp, },
      { rw [edges_cons, list.count_cons],
        split_ifs with h'',
        { obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := h'',
          exact (h' rfl).elim, },
        { apply ih, } } } },
end

@[simp] lemma take_until_copy {u v w v' w'} (p : G.directed_walk v w)
  (hv : v = v') (hw : w = w') (h : u ∈ (p.copy hv hw).support) :
  (p.copy hv hw).take_until u h = (p.take_until u (by { subst_vars, exact h })).copy hv rfl :=
by { subst_vars, refl }

@[simp] lemma drop_until_copy {u v w v' w'} (p : G.directed_walk v w)
  (hv : v = v') (hw : w = w') (h : u ∈ (p.copy hv hw).support) :
  (p.copy hv hw).drop_until u h = (p.drop_until u (by { subst_vars, exact h })).copy rfl hw :=
by { subst_vars, refl }

lemma support_take_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inl hx }

lemma support_drop_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inr hx }

lemma darts_take_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inl hx }

lemma darts_drop_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inr hx }

lemma edges_take_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_take_until_subset h)

lemma edges_drop_until_subset {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_drop_until_subset h)

lemma length_take_until_le {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.take_until u h).length ≤ p.length :=
begin
  have := congr_arg directed_walk.length (p.take_spec h),
  rw [length_append] at this,
  exact nat.le.intro this,
end

lemma length_drop_until_le {u v w : V} (p : G.directed_walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).length ≤ p.length :=
begin
  have := congr_arg directed_walk.length (p.take_spec h),
  rw [length_append, add_comm] at this,
  exact nat.le.intro this,
end

protected
lemma is_directed_trail.take_until {u v w : V} {p : G.directed_walk v w} (hc : p.is_directed_trail) (h : u ∈ p.support) :
  (p.take_until u h).is_directed_trail :=
is_directed_trail.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_directed_trail.drop_until {u v w : V} {p : G.directed_walk v w} (hc : p.is_directed_trail) (h : u ∈ p.support) :
  (p.drop_until u h).is_directed_trail :=
is_directed_trail.of_append_right (by rwa ← take_spec _ h at hc)

protected
lemma is_directed_path.take_until {u v w : V} {p : G.directed_walk v w} (hc : p.is_directed_path) (h : u ∈ p.support) :
  (p.take_until u h).is_directed_path :=
is_directed_path.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_directed_path.drop_until {u v w : V} (p : G.directed_walk v w) (hc : p.is_directed_path) (h : u ∈ p.support) :
  (p.drop_until u h).is_directed_path :=
is_directed_path.of_append_right (by rwa ← take_spec _ h at hc)
/-
### Rotation of a loop Walk
-/
/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.directed_walk v v) (h : u ∈ c.support) : G.directed_walk u u :=
(c.drop_until u h).append (c.take_until u h)

@[simp]
lemma support_rotate {u v : V} (c : G.directed_walk v v) (h : u ∈ c.support) :
  (c.rotate h).support.tail ~r c.support.tail :=
begin
  simp only [rotate, tail_support_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←tail_support_append, take_spec],
end

lemma rotate_darts {u v : V} (c : G.directed_walk v v) (h : u ∈ c.support) :
  (c.rotate h).darts ~r c.darts :=
begin
  simp only [rotate, darts_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←darts_append, take_spec],
end

lemma rotate_edges {u v : V} (c : G.directed_walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges ~r c.edges :=
(rotate_darts c h).map _

protected
lemma is_directed_trail.rotate {u v : V} {c : G.directed_walk v v} (hc : c.is_directed_trail) (h : u ∈ c.support) :
  (c.rotate h).is_directed_trail :=
begin
  rw [is_directed_trail_def, (c.rotate_edges h).perm.nodup_iff],
  exact hc.edges_nodup,
end

protected
lemma is_directed_circuit.rotate {u v : V} {c : G.directed_walk v v} (hc : c.is_directed_circuit) (h : u ∈ c.support) :
  (c.rotate h).is_directed_circuit :=
begin
  refine ⟨hc.to_directed_trail.rotate _, _⟩,
  cases c,
  { exact (hc.ne_nil rfl).elim, },
  { intro hn,
    have hn' := congr_arg length hn,
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn',
    simpa using hn', },
end

protected
lemma is_directed_cycle.rotate {u v : V} {c : G.directed_walk v v} (hc : c.is_directed_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_directed_cycle :=
begin
  refine ⟨hc.to_directed_circuit.rotate _, _⟩,
  rw list.is_rotated.nodup_iff (support_rotate _ _),
  exact hc.support_nodup,
end

end directed_walk_decomp

end directed_walk
/-
### Directed Paths' Type (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
/-- The type for paths between two vertices. -/
abbreviation directed_path (u v : V) := {p : G.directed_walk u v // p.is_directed_path}

namespace directed_path
variables {G G'}

@[simp] protected lemma is_directed_path {u v : V} (p : G.directed_path u v) : (p : G.directed_walk u v).is_directed_path :=
p.property

@[simp] protected lemma is_directed_trail {u v : V} (p : G.directed_path u v) : (p : G.directed_walk u v).is_directed_trail :=
p.property.to_directed_trail

/-- The length-0 path at a vertex. -/
@[refl, simps] protected def nil {u : V} : G.directed_path u u := ⟨directed_walk.nil, directed_walk.is_directed_path.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps] def singleton {u v : V} {g : directed_loopless_simple_graph V} (h : g.adj u v) : g.directed_path u v :=
⟨directed_walk.cons h directed_walk.nil, by {simp only [directed_walk.cons_is_directed_path_iff, directed_walk.is_directed_path_iff_eq_nil, directed_walk.support_nil,
  list.mem_singleton, true_and], exact directed_loopless_simple_graphs.adj.ne h}⟩

lemma mk_mem_edges_singleton {u v : V} {g : directed_loopless_simple_graph V} (h : g.adj u v) :
  (u, v) ∈ (singleton h : g.directed_walk u v).edges := by simp [singleton]

lemma count_support_eq_one [decidable_eq V] {u v w : V} {p : G.directed_path u v}
  (hw : w ∈ (p : G.directed_walk u v).support) : (p : G.directed_walk u v).support.count w = 1 :=
list.count_eq_one_of_mem p.property.support_nodup hw

lemma count_edges_eq_one [decidable_eq V] {u v : V} {p : G.directed_path u v} (e : V × V)
  (hw : e ∈ (p : G.directed_walk u v).edges) : (p : G.directed_walk u v).edges.count e = 1 :=
list.count_eq_one_of_mem p.property.to_directed_trail.edges_nodup hw

@[simp] lemma nodup_support {u v : V} (p : G.directed_path u v) : (p : G.directed_walk u v).support.nodup :=
(directed_walk.is_directed_path_def _).mp p.property

lemma loop_eq {v : V} (p : G.directed_path v v) : p = directed_path.nil :=
begin
  obtain ⟨_|_, this⟩ := p,
  { refl },
  { simpa },
end

lemma not_mem_edges_of_loop {v : V} {e : V × V} {p : G.directed_path v v} :
  ¬ e ∈ (p : G.directed_walk v v).edges :=
by simp [p.loop_eq]

lemma cons_is_cycle {u v : V} (p : G.directed_path v u) (h : G.adj u v)
  (he : ¬ (u, v) ∈ (p : G.directed_walk v u).edges) : (directed_walk.cons h ↑p).is_directed_cycle :=
by simp [directed_walk.is_directed_cycle_def, directed_walk.cons_is_directed_trail_iff, he]

end directed_path
/-
### Bypass of Directed Walk - Walk to Path
-/
namespace directed_walk
variables {G} [decidable_eq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `directed_simple_graph.directed_walk.bypass_is_directed_path`.
This is packaged up in `directed_simple_graph.directed_walk.to_directed_path`. -/
def bypass : Π {u v : V}, G.directed_walk u v → G.directed_walk u v
| u v nil := nil
| u v (cons ha p) :=
  let p' := p.bypass
  in if hs : u ∈ p'.support
     then p'.drop_until u hs
     else cons ha p'

@[simp] lemma bypass_copy {u v u' v'} (p : G.directed_walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).bypass = p.bypass.copy hu hv := by { subst_vars, refl }

lemma bypass_is_directed_path {u v : V} (p : G.directed_walk u v) : p.bypass.is_directed_path :=
begin
  induction p,
  { simp!, },
  { simp only [bypass],
    split_ifs,
    { apply is_directed_path.drop_until,
      assumption, },
    { simp [*, cons_is_directed_path_iff], } },
end

lemma length_bypass_le {u v : V} (p : G.directed_walk u v) : p.bypass.length ≤ p.length :=
begin
  induction p,
  { refl },
  { simp only [bypass],
    split_ifs,
    { transitivity,
      apply length_drop_until_le,
      rw [length_cons],
      exact le_add_right p_ih, },
    { rw [length_cons, length_cons],
      exact add_le_add_right p_ih 1, } },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def to_directed_path {u v : V} (p : G.directed_walk u v) : G.directed_path u v := ⟨p.bypass, p.bypass_is_directed_path⟩

lemma support_bypass_subset {u v : V} (p : G.directed_walk u v) : p.bypass.support ⊆ p.support :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (support_drop_until_subset _ _),
      apply list.subset_cons_of_subset,
      assumption, },
    { rw support_cons,
      apply list.cons_subset_cons,
      assumption, }, },
end

lemma support_to_directed_path_subset {u v : V} (p : G.directed_walk u v) :
  (p.to_directed_path : G.directed_walk u v).support ⊆ p.support :=
support_bypass_subset _

lemma darts_bypass_subset {u v : V} (p : G.directed_walk u v) : p.bypass.darts ⊆ p.darts :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (darts_drop_until_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw darts_cons,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma edges_bypass_subset {u v : V} (p : G.directed_walk u v) : p.bypass.edges ⊆ p.edges :=
list.map_subset _ p.darts_bypass_subset

lemma darts_to_directed_path_subset {u v : V} (p : G.directed_walk u v) :
  (p.to_directed_path : G.directed_walk u v).darts ⊆ p.darts :=
darts_bypass_subset _

lemma edges_to_directed_path_subset {u v : V} (p : G.directed_walk u v) :
  (p.to_directed_path : G.directed_walk u v).edges ⊆ p.edges :=
edges_bypass_subset _

end directed_walk
/-
### Mapping Directed Paths TBC l. 1028 - 1194
-/
/-
### Transferring betweeen Directed Graphs TBC l. 1194 - 1276
-/
/-
### Deleting Edges TBC l.1276 - 1325
-/
/-
### Reachable and Connected (Reverse [cf. simple_graph.connectivity] is not applyable)
-/
/-- Two vertices are *reachable* if there is a walk between them. -/
def reachable (u v : V) : Prop := nonempty (G.directed_walk u v)

variables {G}

lemma reachable_iff_nonempty_univ {u v : V} :
  G.reachable u v ↔ (set.univ : set (G.directed_walk u v)).nonempty :=
set.nonempty_iff_univ_nonempty

protected lemma reachable.elim {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.directed_walk u v → p) : p :=
nonempty.elim h hp

protected lemma reachable.elim_directed_path {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.directed_path u v → p) : p :=
begin
  classical,
  exact h.elim (λ q, hp q.to_directed_path),
end

protected lemma directed_walk.reachable {G : directed_simple_graph V} {u v : V} (p : G.directed_walk u v) :
  G.reachable u v := ⟨p⟩

protected lemma adj.reachable {u v : V} (h : G.adj u v) :
  G.reachable u v := h.to_directed_walk.reachable

@[refl] protected lemma reachable.refl (u : V) : G.reachable u u := by { fsplit, refl }
protected lemma reachable.rfl {u : V} : G.reachable u u := reachable.refl _

@[trans] protected lemma reachable.trans {u v w : V}
  (huv : G.reachable u v) (hvw : G.reachable v w) :
  G.reachable u w :=
huv.elim (λ puv, hvw.elim (λ pvw, ⟨puv.append pvw⟩))

lemma reachable_iff_refl_trans_gen (u v : V) :
  G.reachable u v ↔ relation.refl_trans_gen G.adj u v :=
begin
  split,
  { rintro ⟨h⟩,
    induction h,
    { refl, },
    { exact (relation.refl_trans_gen.single h_h).trans h_ih, }, },
  { intro h,
    induction h with _ _ _ ha hr,
    { refl, },
    { exact reachable.trans hr ⟨directed_walk.cons ha directed_walk.nil⟩, }, },
end

variables (G)

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def preconnected : Prop := ∀ (u v : V), G.reachable u v

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.
There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj, mk_iff]
structure connected : Prop :=
(preconnected : G.preconnected)
[nonempty : nonempty V]

instance : has_coe_to_fun G.connected (λ _, Π (u v : V), G.reachable u v) :=
⟨λ h, h.preconnected⟩

/-- The quotient of `V` by the `directed_simple_graph.reachable` relation gives the connected
components of a graph. -/
def connected_component := quot G.reachable

/-- Gives the connected component containing a particular vertex. -/
def connected_component_mk (v : V) : G.connected_component := quot.mk G.reachable v

@[simps] instance connected_component.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_mk default⟩ 

section connected_component
variables {G}

@[elab_as_eliminator]
protected lemma connected_component.ind {β : G.connected_component → Prop}
  (h : ∀ (v : V), β (G.connected_component_mk v)) (c : G.connected_component) : β c :=
quot.ind h c

@[elab_as_eliminator]
protected lemma connected_component.ind₂ {β : G.connected_component → G.connected_component → Prop}
  (h : ∀ (v w : V), β (G.connected_component_mk v) (G.connected_component_mk w))
  (c d : G.connected_component) : β c d :=
quot.induction_on₂ c d h

protected lemma connected_component.sound {v w : V} :
  G.reachable v w → G.connected_component_mk v = G.connected_component_mk w := quot.sound

/-- The `connected_component` specialization of `quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def connected_component.lift {β : Sort*} (f : V → β)
  (h : ∀ (v w : V) (p : G.directed_walk v w), p.is_directed_path → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim_directed_path (λ hp, h v w hp hp.2))

@[simp] protected lemma connected_component.lift_mk {β : Sort*} {f : V → β}
  {h : ∀ (v w : V) (p : G.directed_walk v w), p.is_directed_path → f v = f w} {v : V} :
  connected_component.lift f h (G.connected_component_mk v) = f v := rfl

protected lemma connected_component.«exists» {p : G.connected_component → Prop} :
  (∃ (c : G.connected_component), p c) ↔ ∃ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).exists

protected lemma connected_component.«forall» {p : G.connected_component → Prop} :
  (∀ (c : G.connected_component), p c) ↔ ∀ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).forall

lemma preconnected.subsingleton_connected_component (h : G.preconnected) :
  subsingleton G.connected_component :=
⟨connected_component.ind₂ (λ v w, connected_component.sound (h v w))⟩

end connected_component
/-
### Directed Walks as Directed Subgraphs TBC l. 1519 - 1590
-/
/-
### Directed Walks of a given Length
-/
section directed_walk_counting

lemma set_walk_self_length_zero_eq (u : V) :
  {p : G.directed_walk u u | p.length = 0} = {directed_walk.nil} :=
by { ext p, simp }

lemma set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
  {p : G.directed_walk u v | p.length = 0} = ∅ :=
begin
  ext p,
  simp only [set.mem_set_of_eq, set.mem_empty_iff_false, iff_false],
  exact λ h', absurd (directed_walk.eq_of_length_eq_zero h') h,
end

lemma set_walk_length_succ_eq (u v : V) (n : ℕ) :
  {p : G.directed_walk u v | p.length = n.succ} =
    ⋃ (w : V) (h : G.adj u w), directed_walk.cons h '' {p' : G.directed_walk w v | p'.length = n} :=
begin
  ext p,
  cases p with _ _ w _ huw pwv,
  { simp [eq_comm], },
  { simp only [nat.succ_eq_add_one, set.mem_set_of_eq, directed_walk.length_cons, add_left_inj,
      set.mem_Union, set.mem_image, exists_prop],
    split,
    { rintro rfl,
      exact ⟨w, huw, pwv, rfl, rfl, heq.rfl⟩, },
    { rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩,
      refl, } },
end

variables (G) [decidable_eq V]

section locally_finite
variables [locally_finite G]

/-- The `finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.directed_walk u v | p.length = n}` a `fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite. -/
def finset_walk_length : Π (n : ℕ) (u v : V), finset (G.directed_walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {directed_walk.nil} }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : G.neighbor_set u),
                 (finset_walk_length n w v).map ⟨λ p, directed_walk.cons w.property p, λ p q, by simp⟩)

lemma coe_finset_walk_length_eq (n : ℕ) (u v : V) :
  (G.finset_walk_length n u v : set (G.directed_walk u v)) = {p : G.directed_walk u v | p.length = n} :=
begin
  induction n with n ih generalizing u v,
  { obtain rfl | huv := eq_or_ne u v;
    simp [finset_walk_length, set_walk_length_zero_eq_of_ne, *], },
  { simp only [finset_walk_length, set_walk_length_succ_eq,
      finset.coe_bUnion, finset.mem_coe, finset.mem_univ, set.Union_true],
    ext p,
    simp only [mem_neighbor_set, finset.coe_map, embedding.coe_fn_mk, set.Union_coe_set,
      set.mem_Union, set.mem_image, finset.mem_coe, set.mem_set_of_eq],
    congr' with w,
    congr' with h,
    congr' with q,
    have := set.ext_iff.mp (ih w v) q,
    simp only [finset.mem_coe, set.mem_set_of_eq] at this,
    rw ← this,
    refl, },
end

variables {G}

lemma walk.mem_finset_walk_length_iff_length_eq {n : ℕ} {u v : V} (p : G.directed_walk u v) :
  p ∈ G.finset_walk_length n u v ↔ p.length = n :=
set.ext_iff.mp (G.coe_finset_walk_length_eq n u v) p

variables (G)

instance fintype_set_walk_length (u v : V) (n : ℕ) : fintype {p : G.directed_walk u v | p.length = n} :=
fintype.of_finset (G.finset_walk_length n u v) $ λ p,
by rw [←finset.mem_coe, coe_finset_walk_length_eq]

lemma set_walk_length_to_finset_eq (n : ℕ) (u v : V) :
  {p : G.directed_walk u v | p.length = n}.to_finset = G.finset_walk_length n u v :=
by { ext p, simp [←coe_finset_walk_length_eq] }

/- See `simple_graph.adj_matrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
lemma card_set_walk_length_eq (u v : V) (n : ℕ) :
  fintype.card {p : G.directed_walk u v | p.length = n} = (G.finset_walk_length n u v).card :=
fintype.card_of_finset (G.finset_walk_length n u v) $ λ p,
  by rw [←finset.mem_coe, coe_finset_walk_length_eq]

instance fintype_set_path_length (u v : V) (n : ℕ) :
  fintype {p : G.directed_walk u v | p.is_directed_path ∧ p.length = n} :=
fintype.of_finset ((G.finset_walk_length n u v).filter directed_walk.is_directed_path) $
  by simp [walk.mem_finset_walk_length_iff_length_eq, and_comm]

end locally_finite

section finite
variables [fintype V] [decidable_rel G.adj]

lemma reachable_iff_exists_finset_walk_length_nonempty (u v : V) :
  G.reachable u v ↔ ∃ (n : fin (fintype.card V)), (G.finset_walk_length n u v).nonempty :=
begin
  split,
  { intro r,
    refine r.elim_directed_path (λ p, _),
    refine ⟨⟨_, p.is_directed_path.length_lt⟩, p, _⟩,
    simp [walk.mem_finset_walk_length_iff_length_eq], },
  { rintro ⟨_, p, _⟩, use p },
end

instance : decidable_rel G.reachable :=
λ u v, decidable_of_iff' _ (reachable_iff_exists_finset_walk_length_nonempty G u v)

--instance : fintype G.connected_component :=
--@quotient.fintype _ _ G.reachable_setoid (infer_instance : decidable_rel G.reachable)

instance : decidable G.preconnected :=
by { unfold preconnected, apply_instance }

instance : decidable G.connected :=
by { rw [connected_iff, ← finset.univ_nonempty_iff], exact and.decidable }

end finite

end directed_walk_counting
/-
### Bridge Edges l. 1722 - 1840
-/
end directed_simple_graph
/-
## Defining missing Object without an analogy to mathlib
-/
/-
### Path System 
-/
namespace directed_simple_graph

variables {V : Type u} {u v w: V} 
variables {n : ℕ} 
variables {α : Type*} [fintype α]
variables (G : directed_simple_graph V)

/- Maybe not needed. -/
@[ext]
structure vertex_subset_n (n : ℕ) (V : Type u) :=
(verts : finset V)
(card : verts.card = n)

lemma A_card_eq_B_card (A B : vertex_subset_n n V): A.verts.card = B.verts.card := by 
{rw A.card, rw B.card}

lemma A_verts_list_length_eq_n (A B : vertex_subset_n n V) : A.verts.to_list.length = n := by 
{simp only [finset.length_to_list], exact A.card}
/- Till here. -/

/- First Approach. -/
structure path_system {α : Type*} [fintype α] (A B : α ↪ V) :=
(B' : α ↪ V)
(range_B' : set.range B' = set.range B)
(path : Π (i : α), G.directed_path (A i) (B' i))
(walk_disj : ∀ (i j : α), i ≠ j → list.disjoint (path i).1.support (path j).1.support)

/- Second Approach. -/
structure path_system2 {α : Type*} [fintype α] (A B : α ↪ V) :=
(σ : equiv.perm α)
(path : Π (i : α), G.directed_path (A i) (B (σ i)))
(walk_disj : ∀ (i j : α), i ≠ j → list.disjoint (path i).1.support (path j).1.support)

variables {G}

/- First Approach. -/
noncomputable def path_system.σ {α : Type*} [fintype α] {A B : α ↪ V} (s : G.path_system A B) : α ≃ α :=
(equiv.of_injective s.B' s.B'.inj').trans
  ((equiv.set.of_eq s.range_B').trans (equiv.of_injective B B.inj').symm)

noncomputable def path_system.sign {α : Type*} [fintype α] {A B : α ↪ V} (s : G.path_system A B) :=
equiv.perm.sign s.σ

/- Second Approach. -/
-- This definition is not actually necessary since one can write `s.σ.sign` just as easily as `s.sign`.
noncomputable def path_system2.sign {α : Type*} [fintype α] {A B : α ↪ V} (s : G.path_system2 A B) :=
s.σ.sign 
/-
### Weights
-/
namespace directed_walk

variables {A B : α ↪ V}

def walk_weight {G : directed_simple_graph V} (weight : G.edge_set → ℝ) : Π {u v : V}, G.directed_walk u v → ℝ
| u v nil := 1
| u v (cons h p) := weight ⟨(u, _), h⟩ * walk_weight p

def path_weight {G : directed_simple_graph V} (weight : G.edge_set → ℝ) (p: G.directed_path u v) : ℝ :=
walk_weight weight (p.1)

def path_system_weight {G : directed_simple_graph V} {A B : α ↪ V} (weight : G.edge_set → ℝ)
(s : G.path_system A B) : ℝ :=
∏ (i : α), path_weight weight (s.path i)
/-
### Path Matrix
-/
end directed_walk

end directed_simple_graph