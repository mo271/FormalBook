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
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.acyclic
import data.list.rotate
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

### Introducing missing Objects
-/
universe u

-- Copying the structure of graph and walk from simple_graph.
@[ext]
structure simple_directed_graph (V : Type u) := (adj : V → V → Prop)

noncomputable instance {V : Type u} [fintype V] : fintype (simple_directed_graph V) :=
by { classical,
exact fintype.of_injective simple_directed_graph.adj simple_directed_graph.ext,}

namespace simple_directed_graph

variables {V : Type u}
variables (G : simple_directed_graph V)

@[derive decidable_eq]
inductive directed_walk : V → V → Type u
| nil {u : V} : directed_walk u u
| cons {u v w: V} (h : G.adj u v) (p : directed_walk v w) : directed_walk u w

attribute [refl] directed_walk.nil

namespace directed_walk
/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.directed_walk u u := directed_walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.directed_walk v w) :
G.directed_walk u w := directed_walk.cons h p

def support : Π {u v : V}, G.directed_walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges: Π {u v : V}, G.directed_walk u v → list (V × V) := 



end directed_walk

end simple_directed_graph