import Mathlib.Combinatorics.Enumerative.DoubleCounting

-- https://github.com/leanprover-community/mathlib4/pull/17651

namespace Finset

variable {R α β : Type*} (r : α → β → Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)]

theorem sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
    [AddCommMonoid R] (f : α → β → R) [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, ∑ b ∈ t.bipartiteAbove r a, f a b = ∑ b ∈ t, ∑ a ∈ s.bipartiteBelow r b, f a b := by
  simp_rw [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.sum_filter]
  exact Finset.sum_comm

end Finset
