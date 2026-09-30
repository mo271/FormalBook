/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, OpenClaw
-/
module

public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Slice
import FormalBook.Ch30.EKRAuxiliary
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Combinatorics.Hall.Basic

@[expose] public section
/-!
# Three famous theorems on finite sets

## Katona's cyclic permutation proof of Erdős–Ko–Rado

  - [x] Theorem 1 (Sperner)
  - [x] Theorem 2 (Erdős–Ko–Rado) — Katona's cyclic permutation proof
  - [x] Theorem 3 (Hall's marriage theorem)

## References

* Aigner, M. and Ziegler, G.M., "Proofs from THE BOOK", Chapter 30
* Katona, G.O.H., "A simple proof of the Erdős–Ko–Rado theorem", 1972
-/

namespace chapter30

/-! ## Theorem 1: Sperner's theorem -/

/-- **Sperner's theorem.** -/
theorem sperner {α : Type*} [Fintype α]
    (𝒜 : Finset (Finset α)) (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
  h𝒜.sperner

/-! ## Theorem 2: Erdős–Ko–Rado (Katona's cyclic permutation proof) -/

section ErdosKoRado

/-- **Erdős–Ko–Rado theorem** (Katona's cyclic permutation proof).
If `n ≥ 2k`, then the maximum size of an intersecting k-uniform family
of subsets of `Fin n` is `C(n-1, k-1)`.

The double counting gives `|𝒜| · n · k! · (n-k)! ≤ k · n!`.
Since `C(n-1, k-1) · n · k! · (n-k)! = k · n!`, we get `|𝒜| ≤ C(n-1, k-1)`. -/
theorem erdos_ko_rado {n : ℕ} {𝒜 : Finset (Finset (Fin n))} {k : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hSized : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hk : k ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  -- Trivial case k = 0
  rcases Nat.eq_zero_or_pos k with rfl | h1k
  · convert Nat.zero_le _
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun A hA ↦ h𝒜 hA hA
      (by rw [Finset.disjoint_self_iff_empty, ← Finset.card_eq_zero]; exact hSized hA)
  have hkn : k ≤ n := le_trans hk (Nat.div_le_self n 2)
  have h2k : 2 * k ≤ n := by omega
  -- Use the double counting inequality and factorial identity
  have hdc := double_counting_ineq h2k 𝒜 h𝒜 hSized
  have hid := choose_factorial_identity h1k hkn
  have hpos : 0 < n * k.factorial * (n - k).factorial := by
    apply Nat.mul_pos (Nat.mul_pos (by omega) (Nat.factorial_pos k)) (Nat.factorial_pos (n - k))
  -- |𝒜| * denom ≤ k * n! = C(n-1,k-1) * denom
  rw [← hid] at hdc
  exact Nat.le_of_mul_le_mul_right hdc hpos

end ErdosKoRado

/-! ## Theorem 3: Hall's marriage theorem

The proof follows the book's inductive argument on `|ι|`, with two cases:

**Case 1 (Strict):** If the Hall condition holds *strictly* for every proper nonempty
subset (`|⋃_{i∈S} A_i| ≥ |S| + 1`), pick any representative for an arbitrary element,
remove it from the remaining sets, and apply the induction hypothesis.
(Formalized as `HallMarriageTheorem.hall_hard_inductive_step_A`.)

**Case 2 (Tight):** If some proper nonempty subset `S` satisfies `|⋃_{i∈S} A_i| = |S|`,
solve `S` and `Sᶜ` independently (removing the representatives of `S` from the sets
indexed by `Sᶜ`), then combine.
(Formalized as `HallMarriageTheorem.hall_hard_inductive_step_B`.)

The finite case (`HallMarriageTheorem.hall_hard_inductive`) is then lifted to
arbitrary index types via a compactness argument
(`Finset.all_card_le_biUnion_card_iff_existsInjective`).
-/

/-- **Hall's marriage theorem.** -/
theorem hall_marriage {ι : Type*} {α : Type*} [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t

end chapter30
