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
open finset nat
open_locale big_operators
/-!
# Six proofs of the infinity of primes

## TODO
 - Euclid's Proof
 - Seccond Proof
 - Third Proof
 - Fourth Proof
 - Fifth Proof
 - Sixth Proof
 - Appendix: Infinitely many more proofs

### Euclid's Proof

-/
theorem infinity_of_primes₁ (S : finset ℕ) (h: ∀ (q ∈ S), nat.prime q):
  ∃ (p : ℕ), nat.prime p ∧ p ∉ S :=
begin
  let n := 1 + ∏ q in S, q,
  /- This n has a prime divisor;
  we pick the minimal one, the argument works with any prime divisor -/
  let p := n.min_fac,
  use p,
  split,
  { have hn: 0 < ∏ q in S, q :=
    begin
     refine prod_pos _,
     intros q hq,
     exact prime.pos (h q hq),
    end,
    exact nat.min_fac_prime (ne_of_gt(lt_add_of_pos_right 1 hn)), },
  { by_contradiction,
    sorry, },
end

--theorem infinity_of_primes₂
