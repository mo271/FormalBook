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
import Mathlib.Tactic
/-
import data.rel
import data.list.defs
import data.matrix.basic
import data.fintype.card

import logic.equiv.defs
import group_theory.perm.sign

import set_theory.zfc.basic

import linear_algebra.matrix.determinant
-/
open BigOperators
/-!
# Lattice paths and determinants

## TODO

  - Lemma
    - proof
  - Theorem
    - proof

  There is a lengthy attempt to at this chapter version of the lean3 version here:
https://github.com/mo271/formal_book/blob/92f57b44cbbc1cd02ca77994efe8d8e6de050a19/src/chapters/32_Lattice_paths_and_determinants.lean
-/

