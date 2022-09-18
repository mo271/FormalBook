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

Authors: Moritz Firsching, Nikolas Kuhn
-/
import tactic
import data.zmod.basic
import data.finset.card
import data.polynomial.basic
import order.locally_finite


open zmod finset
open polynomial (X)
open_locale polynomial
open_locale big_operators

/-!
# The law of quadratic reciprocity

## Outline
  - Legendre symbol
  - Euler's criterion
  - First proof
    - Lemma of Gauss
    - proof
  - Second proof
    - A.
    - B.
    - First expression -- TO DO
    - Second expression -- TO DO
    - The multiplicative group of a finite field is cyclic
    - proof
-/

namespace book
namespace quadratic_reciprocity




section
/- Throughout this section, `p` is an odd prime. -/
variables (p : ℕ) (h_p : p ≠ 2) [fact (nat.prime p)]


def legendre_sym (a : ℤ) : ℤ :=
  ite ( (a : zmod p) = 0) 0 $
    ite (∃ b : zmod p, a = b ^ 2) 1 (-1)

/--
Fermat's little theorem: If `a` is nonzero modulo the odd prime `p`, then `a ^ (p - 1) = -1`
modulo `p`.
-/
lemma fermat_little (a : ℤ): (a ≠ (0 : zmod p)) → a ^ (p - 1) = (-1 : zmod p) :=
begin
  let units_finset := (finset.univ : finset (zmod p)).erase 0,
  suffices : (units_finset).image (λ x : zmod p, (a : zmod p) * x) = units_finset, by
    sorry,
  sorry,
end

theorem euler_criterion (a : ℤ) :
  a ≠ (0 : zmod p) → (legendre_sym p a : zmod p) = a ^ ((p - 1) / 2) :=
begin
  sorry,
end

lemma product_rule (a b : ℤ) :
  legendre_sym p (a * b) = (legendre_sym p a) * (legendre_sym p b) :=
begin
  sorry,
end

end

/-!
### First proof
For the statement, see `theorem quadratic_reciprocity_1`.
-/

-- Maybe define the function `r i` = "reduce p i" explicitly ?
--TODO : This should probably be broken down a little bit first
lemma lemma_of_Gauss (p : ℕ) [fact (nat.prime p)] (a : ℤ) (h_a : a ≠ (0 : zmod p))
  ( r : ℤ → ℤ ) (h_r : (∀ i, (- (p: ℤ) - 1)/2 ≤ r i ∧ r i ≤ ((p : ℤ) - 1)/2))
  ( H : ∀ i, (r i : ℤ) = (a * i : zmod p) ) :
   legendre_sym p a =
   card ((Icc (1 : ℤ) (((p : ℤ)-1)/2)).image r ∩ (Icc (-((p: ℤ) - 1)/2) (-1))):=
begin
  sorry
end

theorem quadratic_reciprocity_1 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [fact (nat.prime p)] [fact (nat.prime q)] :
  (legendre_sym p q) * (legendre_sym q p) = -1 ^ ((p-1) / 2 * (q - 1) / 2 ) :=
  sorry

/-!
### Second Proof
TODO:
    - A.
    - B.
    - First expression
    - Second expression
    - The multiplicative group of a finite field is cyclic
-/

/- The group of units of a finite field is cyclic, i.e. has a multiplicative generator-/
lemma mult_cyclic (K : Type*) [field K] [fintype K] : ∃ ζ : Kˣ, ∀ α : Kˣ, ∃ k : ℤ, α = ζ ^ k :=
begin
  sorry,
end



lemma fact_A (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2) [fact (nat.prime p)] [fact (nat.prime q)]
  (h_pq : p ≠ q) (K : Type*) [field K] [fintype K] (H : fintype.card K = q ^ (p - 1)) :
  ∀ a b : K, (a + b) ^ q = a ^ q + b ^ q :=
begin
  sorry,
end

/-
For any element `ζ` of multiplicative order `p` in a field `K`, we have a polynomial
decomposition`X^p - 1 = (X - ζ) * (X - ζ ^ 2) * ... * (X - ζ ^ p)`.
-/
lemma fact_B (p : ℕ) [fact (prime p)] (K : Type*) [field K] (ζ : Kˣ) (h_1 : ζ ^ p = 1)
  (h_2 : ζ ≠ 1) :
  X  ^ (p - 1) - (1 : K[X])  = ∏ i in Icc 1 p, (X - (polynomial.C (ζ : K)) ^ i) :=
begin
  sorry,
end

theorem quadratic_reciprocity_2 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [fact (nat.prime p)] [fact (nat.prime q)] :
  (legendre_sym p q) * (legendre_sym q p) = -1 ^ ((p-1) / 2 * (q - 1) / 2 ) :=
begin
  sorry
end


end quadratic_reciprocity
end book

