/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
https://github.com/mo271/FormalBook/blob/92f57b44cbbc1cd02ca77994efe8d8e6de050a19/src/chapters/32_Lattice_paths_and_determinants.lean
-/
