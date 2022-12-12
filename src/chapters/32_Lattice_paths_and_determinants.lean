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
import combinatorics.simple_graph.acyclic
/-!
# Lattice paths and determinants

## TODO

 - missing definitions:
  - directed graphs (trivial to do)
  - Path
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
-/
universe u

-- Copying the structure from simple_graph.
@[ext]
structure simple_directed_graph (V : Type u) := (adj : V → V → Prop)

noncomputable instance {V : Type u} [fintype V] : fintype (simple_directed_graph V) :=
by { classical,
exact fintype.of_injective simple_directed_graph.adj simple_directed_graph.ext,}
