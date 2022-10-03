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
import data.fintype.card
import ring_theory.integral_domain
import data.polynomial.ring_division

open finset
open_locale big_operators nat
/-!
# Every finite division ring is a field

This is a TODO in `ring_theory.integral_domain`.
## TODO
  - statement
    - proof
      - Roots of unity
-/
variables {R : Type*} [ring R] [comm_ring R] [decidable_eq R] [division_ring R]

noncomputable theorem wedderburn (h: fintype R): field R :=
begin
  sorry,
end
