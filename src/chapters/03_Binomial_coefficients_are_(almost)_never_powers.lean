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
open nat
/-!
# Binomial coefficients are (almost) never powers

## TODO
  - (1)
  - (2)
  - (3)
  - (4)


Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/
theorem binomials_coefficients_never_powers (k l m n : ℕ) (h_l : l ≥ 2) (h_ : 4 ≤ k) (h_n : k ≤ n):
  choose n k ≠ m^l :=
begin
  sorry,
end
