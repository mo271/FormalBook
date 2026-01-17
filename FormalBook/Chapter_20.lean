/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import FormalBook.Mathlib.EdgeFinset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Real
open RealInnerProductSpace
open BigOperators
open Classical

/-!
# In praise of inequalities

## TODO
  - Theorem I
    - proof
  - Theorem II
    - proof
      - (A)
      - (B)
    - another proof
    - still another proof
  - Theorem 1
    - proof
  - The tangential triangle
  - Theorem 2
    - proof
  - Theorem 3
    - First proof
    - Second proof
-/

section Inequalities

-- Not quite sure what we actually need here, want to have ℝ-vector space with inner product.
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq V]

theorem cauchy_schwarz_inequality (a b : V) : ⟪ a, b ⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have h: ∀ (x : ℝ), ‖x • a + b‖ ^ 2 = x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
    simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
    simp only [inner_add_add_self, inner_smul_right, inner_smul_left, conj_trivial,
        add_left_inj, real_inner_comm]
    intro x
    ring_nf
  by_cases ha : a = 0
  · rw [ha]
    simp
  · by_cases hl : (∃ (l : ℝ),  b = l • a)
    · obtain ⟨l, hb⟩ := hl
      rw [hb]
      simp only [pow_two, ← (real_inner_self_eq_norm_mul_norm _)]
      simp only [inner_smul_right, inner_smul_left, conj_trivial]
      ring_nf
      rfl
    · have : ∀ (x : ℝ), 0 < ‖x • a + b‖ := by
        intro x
        by_contra hx
        simp only [norm_pos_iff, ne_eq, Decidable.not_not] at hx
        absurd hl
        use -x
        rw [← add_zero (-x•a), ← hx]
        simp only [neg_smul, neg_add_cancel_left]
      have : ∀ (x : ℝ), 0 < ‖x • a + b‖ ^ 2 := by
        exact fun x ↦ sq_pos_of_pos (this x)
      have : ∀ (x : ℝ), 0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := by
        convert this
        exact (h _).symm
      have : ∀ (x : ℝ), 0 <  ‖a‖ ^ 2 * (x * x)  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2 := by
        intro x
        calc
          0 <  x ^ 2 * ‖a‖ ^ 2 + 2 * x * ⟪a, b⟫ + ‖b‖ ^ 2 := this x
          _ = ‖a‖ ^ 2 * (x * x)  + 2 * ⟪a, b⟫ * x + ‖b‖ ^ 2  := by ring_nf
      have ha_sq : ‖a‖ ^ 2 ≠ 0 := by aesop
      have := discrim_lt_zero ha_sq this
      unfold discrim at this
      have  : (2 * inner _ a b) ^ 2 < 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by linarith
      linarith



namespace List

noncomputable
def all_positive (a : List ℝ) : Prop
  := ∀ x ∈ a, 0 < x

lemma all_positive_of_map_inv (a : List ℝ) (a_pos : a.all_positive)
  : (a.map Inv.inv).all_positive
  := by
  unfold List.all_positive at a_pos ⊢
  rw [List.forall_mem_map]
  intro x x_in_a
  exact inv_pos.mpr (a_pos x x_in_a)


noncomputable
def all_equal {α} (a : List α) : Prop := a.IsChain (·=·)


lemma all_equal_singleton {α} (x : α)
  : [x].all_equal
  := by simp [all_equal]

lemma all_equal_map {α β} (f : α → β) (xs : List α)
  : xs.all_equal → (xs.map f).all_equal
  := by
  apply List.isChain_map_of_isChain
  intro a b
  exact congr_arg f

lemma all_equal_map_iff {α β} (p : α → Prop) (f : α → β) (inj : Set.InjOn f p)
    (xs : List α) (h : ∀ x ∈ xs, p x)
  : xs.all_equal ↔ (xs.map f).all_equal
  := by
  constructor
  · exact all_equal_map f xs
  · intro map_f_eq
    simp only [all_equal, List.isChain_map] at map_f_eq
    apply List.IsChain.imp_of_mem_imp (p := map_f_eq)
    intro a b a_mem b_mem f_eq
    exact inj (h a a_mem) (h b b_mem) f_eq

lemma isChain_nonempty_eq_iff_eq_replicate {α} {xs : List α} (nonempty : xs ≠ [])
  : IsChain (· = ·) xs ↔ xs = replicate xs.length (xs.head nonempty)
  := by
  have xs_cons := List.cons_head_tail nonempty
  rw [← congr_arg (IsChain (·=·)) xs_cons]
  rw [isChain_cons_eq_iff_eq_replicate]
  rw [List.length_tail, ← List.tail_replicate]
  constructor
  · intro xs_eq_tail
    have := congr_arg (xs.head nonempty :: ·) xs_eq_tail
    simpa [xs_cons, ← List.replicate_succ,
            Nat.sub_add_cancel (List.length_pos_of_ne_nil nonempty)]
  · exact congr_arg List.tail

lemma all_equal_append {α} {xs ys : List α}
  (xs_eq : xs.all_equal) (ys_eq : ys.all_equal) (xy_eq : ∃ x∈xs, ∃ y∈ys, x=y)
  : (xs++ys).all_equal
  := by
  unfold all_equal at xs_eq ys_eq ⊢
  have ⟨x, x_mem, y, y_mem, x_eq_y⟩ := xy_eq
  have xs_nonempty := List.ne_nil_of_mem x_mem
  have ys_nonempty := List.ne_nil_of_mem y_mem
  rw [List.isChain_nonempty_eq_iff_eq_replicate xs_nonempty] at xs_eq
  rw [List.isChain_nonempty_eq_iff_eq_replicate ys_nonempty] at ys_eq
  rw [List.isChain_nonempty_eq_iff_eq_replicate
          (List.append_ne_nil_of_left_ne_nil xs_nonempty ys)]
  rw [xs_eq, List.mem_replicate] at x_mem
  rw [ys_eq, List.mem_replicate] at y_mem
  rw [← y_mem.2, ← x_eq_y, x_mem.2] at ys_eq
  rw [List.length_append, List.replicate_add, List.head_append_left xs_nonempty]
  exact congr_arg₂ List.append xs_eq ys_eq


lemma list1_eq_singleton {α} (xs : List α) (xslen : xs.length = 1)
  : xs = [xs[0]]
  := by
  have len_pos : 0 < xs.length := by linarith
  rw [List.length_pos_iff_exists_cons] at len_pos
  have ⟨h,t,ht_cons⟩ := len_pos
  simp [ht_cons, List.length_cons] at xslen
  simpa [ht_cons]

lemma list2_eq_pair {α} (xs : List α) (xslen : xs.length = 2)
  : xs = [xs[0],xs[1]]
  := by
  have len_pos : 0 < xs.length := by linarith
  rw [List.length_pos_iff_exists_cons] at len_pos
  have ⟨h,t,ht_cons⟩ := len_pos
  simp [ht_cons]
  rw [ht_cons, List.length_cons] at xslen
  exact t.list1_eq_singleton (by linarith : t.length = 1)

end List


noncomputable
def harmonic_mean (a : List ℝ) : ℝ
  := a.length / (a.map (1/·)).sum

noncomputable
def geometric_mean (a : List ℝ) : ℝ := a.prod ^ (1/(a.length:ℝ))

noncomputable
def arithmetic_mean (a : List ℝ) : ℝ := a.sum / a.length

lemma harmonic_mean_eq_inv_arithmetic_mean_inv
  (a : List ℝ) (_hpos : a.all_positive)
  : harmonic_mean a = (arithmetic_mean (a.map Inv.inv))⁻¹
  := by
  unfold harmonic_mean arithmetic_mean
  simp

lemma arithmetic_mean_pos
  (a : List ℝ) (nonempty : a ≠ []) (hpos : a.all_positive)
  : 0 < arithmetic_mean a
  := by
  unfold arithmetic_mean
  have lenpos : 0 < (a.length:ℝ) := by
    simp only [Nat.cast_pos, a.length_pos_of_ne_nil nonempty]
  exact (div_pos_iff_of_pos_right lenpos).mpr (a.sum_pos hpos nonempty)

lemma arithmetic_mean_split (a b : List ℝ) (eq_len : a.length = b.length)
  : arithmetic_mean (a++b) = (arithmetic_mean a + arithmetic_mean b) / 2
  := by
  simp [arithmetic_mean, eq_len]
  ring_nf

lemma geometric_mean_pos (a : List ℝ) (hpos : a.all_positive)
  : 0 < geometric_mean a
  := by
  unfold geometric_mean
  apply Real.rpow_pos_of_pos
  exact a.prod_pos hpos


lemma arithmetic_mean_eq (a : List ℝ) (eq : a.all_equal)
  : ∀ x ∈ a, x = arithmetic_mean a
  := by
  unfold arithmetic_mean
  unfold List.all_equal at eq
  if empty : a = []
  then simp [empty]
  else
    rw [List.isChain_nonempty_eq_iff_eq_replicate empty] at eq
    rw [eq]
    simp [empty]

lemma geometric_mean_eq (a : List ℝ) (a_pos : a.all_positive) (eq : a.all_equal)
  : ∀ x ∈ a, x = geometric_mean a
  := by
  unfold geometric_mean
  unfold List.all_equal at eq
  if empty : a = []
  then simp [empty]
  else
    rw [List.isChain_nonempty_eq_iff_eq_replicate empty] at eq
    rw [eq]
    have len_nezero : ↑a.length ≠ (0 : ℝ) := by simpa
    have head_nonneg := le_of_lt (a_pos (a.head empty) (a.head_mem empty))
    simp [empty, ← rpow_natCast, rpow_rpow_inv head_nonneg len_nezero]

lemma geometric_arithmetic_mean_eq (a : List ℝ) (eq : a.all_equal)
  : let n := a.length
    a.prod = (a.sum / (n : ℝ)) ^ n
  := by
  unfold List.all_equal at eq
  if empty : a = []
  then simp [empty]
  else
    rw [List.isChain_nonempty_eq_iff_eq_replicate empty] at eq
    rw [eq]
    simp [empty]



lemma inv_geometric_mean_eq_geometric_mean_inv
  (a : List ℝ) (hpos : a.all_positive)
  : (geometric_mean a)⁻¹ = geometric_mean (a.map Inv.inv)
  := by
  unfold geometric_mean
  simp [← Real.inv_rpow (le_of_lt (a.prod_pos hpos)), List.prod_inv]

lemma hm_le_gm_of_gm_le_am (n:ℕ) :
  (∀ a : List ℝ, a.all_positive ∧ n = a.length
        → geometric_mean a ≤ arithmetic_mean a
          ∧
          (geometric_mean a = arithmetic_mean a ↔ a.all_equal))
  →
  (∀ a : List ℝ, a.all_positive ∧ n = a.length
        → harmonic_mean a ≤ geometric_mean a
          ∧
          (harmonic_mean a = geometric_mean a ↔ a.all_equal))
  := by
  intro gm_rel_am a ⟨a_pos, a_len⟩
  have a_inv_pos := a.all_positive_of_map_inv a_pos

  have ⟨gm_le_am, gm_eq_am⟩
          := gm_rel_am (a.map Inv.inv) ⟨a_inv_pos, by simp [a_len]⟩

  apply inv_anti₀ (geometric_mean_pos _ a_inv_pos) at gm_le_am
  rw [← inv_inj] at gm_eq_am
  rw [← harmonic_mean_eq_inv_arithmetic_mean_inv a a_pos,
      ← inv_geometric_mean_eq_geometric_mean_inv a a_pos, inv_inv]
          at gm_le_am gm_eq_am

  have inj_f : Set.InjOn (Inv.inv : ℝ → ℝ) (0<·) := by simp
  rw [← (List.all_equal_map_iff (0<·) Inv.inv inj_f a a_pos), eq_comm] at gm_eq_am

  exact ⟨gm_le_am, gm_eq_am⟩

lemma gm_le_am_2 (x y : ℝ)
  : x*y ≤ ((x+y) / 2) ^ 2
    ∧
    (x*y = ((x+y) / 2) ^ 2 → x=y)
  := by
  constructor
  · linarith [sq_nonneg (x-y)]
  · -- grind would solve this, but we want to demonstrate the idea from The Book
    intro gm_eq_am
    rw [← sub_eq_zero, ← sq_eq_zero_iff, sub_sq]
    rw [div_pow] at gm_eq_am
    apply (congr_arg (·*4)) at gm_eq_am
    apply (congr_arg (·-(4*x*y))) at gm_eq_am
    ring_nf at gm_eq_am
    rw [gm_eq_am]
    ring_nf

def flip_parity (n : ℕ) : ℕ
  := if Even n then n-1 else n+1

lemma flip_parity_decrease_even (n:ℕ) (even : Even n) (n3 : 3 ≤ n)
  : flip_parity (n/2) < flip_parity n
  := by
  unfold flip_parity
  simp [if_pos even]
  split
  case isTrue even_half => grind
  case isFalse not_even_half => grind

lemma le_antisymm2 {x y z : ℝ} (xy : x≤y) (yz : y≤z) (xz : x=z)
  : x=y ∧ y=z
  := by
  rw [xz] at xy
  have y_eq_z := le_antisymm yz xy
  rw [← y_eq_z] at xz
  exact ⟨xz, y_eq_z⟩

lemma le_antisymm3 {x y z u : ℝ} (xy : x≤y) (yz : y≤z) (zu : z≤u) (xu : x=u)
  : x=y ∧ y=z ∧ z=u
  := by
  rw [xu] at xy
  have z_eq_u := le_antisymm zu (xy.trans yz)
  have y_eq_z := le_antisymm yz (zu.trans xy)
  rw [← z_eq_u, ← y_eq_z] at xu
  exact ⟨xu, y_eq_z, z_eq_u⟩

lemma gm_le_am_cauchy (a : List ℝ) (nonempty : a ≠ []) (hpos : a.all_positive)
  : let n := a.length
    a.prod ≤ (a.sum / n) ^ n
    ∧
    (a.prod = (a.sum / n) ^ n → a.all_equal)
  := by
  set n := a.length with n_def
  match n with
  | Nat.zero => linarith [a.length_pos_of_ne_nil nonempty]
  | Nat.succ Nat.zero =>
    rw [a.list1_eq_singleton (Eq.symm n_def)]
    simp [List.all_equal_singleton]
  | Nat.succ (Nat.succ Nat.zero) =>
    rw [a.list2_eq_pair (Eq.symm n_def)]
    simp [List.all_equal]
    exact gm_le_am_2 a[0] a[1]
  | Nat.succ (Nat.succ (Nat.succ m3)) =>
    have hn : 0<n := by linarith
    cases n.even_or_odd
    case inr h =>
      have odd := h
      set A := arithmetic_mean a with A_def
      have A_pos := arithmetic_mean_pos a nonempty hpos
      rw [← A_def] at A_pos
      set a1 := a ++ [A] with a1_def
      have a1_pos : a1.all_positive := by
        simp only [a1_def, List.all_positive,
                   List.mem_append, List.mem_singleton]
        rw [forall₂_or_left]
        exact ⟨hpos, λ x x_eq_A => x_eq_A ▸ A_pos⟩
      have a1nonempty : a1 ≠ [] := List.append_ne_nil_of_left_ne_nil nonempty [A]
      have ⟨gm_le_am, gm_eq_am⟩ := gm_le_am_cauchy a1 a1nonempty a1_pos
      simp only [a1_def, List.sum_append, List.prod_append,
                 List.sum_singleton, List.prod_singleton,
                 List.length_append, List.length_singleton] at gm_le_am gm_eq_am
      have nrpos : 0 < (n:ℝ) := by simpa only [Nat.cast_pos]
      have n_ne_0 : (n:ℝ) ≠ 0 := by linarith
      have a_sum_eq_n_arith_mean : a.sum = n*A := by
        simp only [A_def, arithmetic_mean, n, mul_div_cancel₀ a.sum n_ne_0]
      have n1_ne_0 : ↑(n+1) ≠ (0:ℝ) := by simp; linarith
      have am_eq_gm1 : ((a.sum + A) / ↑(n + 1)) ^ (n + 1) = A^n * A :=
        calc
          ((a.sum + A) / ↑(n + 1)) ^ (n + 1)
            = ((n*A + A) / ↑(n + 1)) ^ (n + 1) := by rw [a_sum_eq_n_arith_mean]
          _ = (((n+1)*A) / ↑(n + 1)) ^ (n + 1) := by
                  rw [(by linarith : n*A + A = (n+1)*A)]
          _ = ((↑(n+1)*A) / ↑(n + 1)) ^ (n + 1) := by simp
          _ = A ^ (n + 1) := by simp only [mul_div_cancel_left₀ A n1_ne_0]
          _ = A^n * A := by ring_nf
      have n_def_len : n = a.length := by dsimp
      rw [← n_def_len, am_eq_gm1] at gm_le_am
      apply (le_of_mul_le_mul_right · A_pos) at gm_le_am

      rw [← n_def_len] at gm_eq_am
      have gm_eq_am_of_pred : (a.prod = (a.sum / ↑n) ^ n →
                      a.prod * A = ((a.sum + A) / ↑(n + 1)) ^ (n + 1)) := by
        intro eq
        calc a.prod * A
            = (a.sum / ↑n) ^ n * A := congr_arg (·*A) eq
          _ = A ^ n * A := by simp [A_def, n_def_len, arithmetic_mean]
          _ = A ^ (n+1) := by simp [pow_succ]
          _ = ((a.sum + A) / ↑(n+1)) ^ (n+1) := by
                  simp [a_sum_eq_n_arith_mean]; field_simp
      have gm_eq_am_pred : (a.prod = (a.sum / ↑n) ^ n → a.all_equal) := by
        intro eq
        apply gm_eq_am_of_pred at eq
        apply gm_eq_am at eq
        exact List.IsChain.left_of_append eq
      rw [n_def]
      exact ⟨gm_le_am, gm_eq_am_pred⟩
    case inl h =>
      have even := h
      have even_half := Nat.div_two_mul_two_of_even h
      have n_def_len : n = a.length := by dsimp
      simp only [n_def, ← n_def_len]
      set n2 := n/2 with n2_def
      set al := a.take n2 with al_def
      set ar := a.drop n2 with ar_def
      have a_split : al++ar = a := by simp only [al, ar, List.take_append_drop]
      have hn2 : 1 ≤ n2 := by omega
      have al_pos : al.all_positive
              := λx x_mem ↦ hpos x (List.mem_of_mem_take x_mem)
      have ar_pos : ar.all_positive
              := λx x_mem ↦ hpos x (List.mem_of_mem_drop x_mem)
      have al_len : al.length = n2 := by
        rw [List.length_take, ← n_def_len]
        simp only [inf_eq_left]
        linarith
      have ar_len : ar.length = n2 := by
        rw [List.length_drop, ← n_def_len]
        omega
      have al_nonempty : al ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, al_len]
        linarith
      have ar_nonempty : ar ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, ar_len]
        linarith
      have ⟨gm_le_am_l, gm_eq_am_l⟩ := gm_le_am_cauchy al al_nonempty al_pos
      have ⟨gm_le_am_r, gm_eq_am_r⟩ := gm_le_am_cauchy ar ar_nonempty ar_pos
      have ⟨gm_le_am_pair, gm_eq_am_pair⟩ := gm_le_am_2 (al.sum/n2) (ar.sum/n2)
      rw [al_len] at gm_le_am_l gm_eq_am_l
      rw [ar_len] at gm_le_am_r gm_eq_am_r
      have alprod_nonneg : 0 ≤ al.prod := le_of_lt (List.prod_pos al_pos)
      have arprod_nonneg : 0 ≤ ar.prod := le_of_lt (List.prod_pos ar_pos)
      have even_half_r : ↑n2 * 2 = (n:ℝ) := by
        simp only [← even_half, Nat.cast_mul, Nat.cast_ofNat]
      have n2r_pos : 0 < (n2:ℝ) := by simp; linarith
      have al_am : arithmetic_mean al = al.sum/n2 := by
        simp only [arithmetic_mean, al_len]
      have ar_am : arithmetic_mean ar = ar.sum/n2 := by
        simp only [arithmetic_mean, ar_len]
      have al_am_pos := arithmetic_mean_pos al al_nonempty al_pos
      have ar_am_pos := arithmetic_mean_pos ar ar_nonempty ar_pos
      have mul_sum_pos : 0 < arithmetic_mean al * arithmetic_mean ar :=
              mul_pos al_am_pos ar_am_pos
      have mul_sum_nonneg : 0 ≤ (al.sum/n2) * (ar.sum/n2) :=
              le_of_lt (al_am ▸ ar_am ▸ mul_sum_pos)
      have prod_split : a.prod = al.prod * ar.prod := by
        calc
          a.prod
            = (al++ar).prod := by rw [a_split]
          _ = al.prod * ar.prod := by simp only [List.prod_append]
      have gm_le_am_mul_l_r
        : al.prod * ar.prod ≤ (al.sum/n2)^n2 * (ar.sum/n2)^n2
        := mul_le_mul gm_le_am_l gm_le_am_r
                arprod_nonneg (alprod_nonneg.trans gm_le_am_l)
      have gm_le_am_pair_pow
        : ((al.sum/n2) * (ar.sum/n2))^n2
            ≤ (((al.sum/n2+ar.sum/n2)/2)^2)^n2
        := pow_le_pow_left₀ mul_sum_nonneg gm_le_am_pair n2
      have merge_sum : (((al.sum/n2+ar.sum/n2)/2)^2)^n2 = (a.sum / ↑n) ^ n := by
        calc
          (((al.sum/n2+ar.sum/n2)/2)^2)^n2
          _ = ((a.sum/n)^2)^n2 := by
                have am2 := arithmetic_mean_split al ar (al_len.trans (Eq.symm ar_len))
                simp only [al_am, ar_am] at am2
                simp only [arithmetic_mean, a_split, ← n_def_len] at am2
                rw [← am2]
          _ = (a.sum/n)^(n2*2) := by rw [mul_comm n2 2, pow_mul]
          _ = (a.sum / ↑n) ^ n := by rw [even_half]
      have final_le : a.prod ≤ (a.sum / ↑n) ^ n := by
        calc
          a.prod
          _ = al.prod * ar.prod := prod_split
          _ ≤ (al.sum/n2)^n2 * (ar.sum/n2)^n2 := gm_le_am_mul_l_r
          _ = ((al.sum/n2) * (ar.sum/n2))^n2 := Eq.symm (mul_pow _ _ n2)
          _ ≤ (((al.sum/n2+ar.sum/n2)/2)^2)^n2 := gm_le_am_pair_pow
          _ = (a.sum / ↑n) ^ n := merge_sum
      have final_eq : a.prod = (a.sum / ↑a.length) ^ a.length → a.all_equal := by
        intro eq
        rw [prod_split, ← merge_sum] at eq
        have ⟨gm_eq_am_mul_l_r, _mul_pow_eq, gm_eq_am_pair_pow⟩ :=
                le_antisymm3
                  gm_le_am_mul_l_r
                  (le_of_eq (Eq.symm (mul_pow _ _ n2)))
                  gm_le_am_pair_pow
                  eq
        have ar_am_pow_pos : 0 < (ar.sum / ↑n2) ^ n2
                := ar_am ▸ pow_pos ar_am_pos n2
        rw [mul_eq_mul_iff_eq_and_eq_of_pos gm_le_am_l gm_le_am_r
                (List.prod_pos al_pos) ar_am_pow_pos] at gm_eq_am_mul_l_r
        have al_eq := gm_eq_am_l gm_eq_am_mul_l_r.1
        have ar_eq := gm_eq_am_r gm_eq_am_mul_l_r.2
        rw [pow_left_inj₀ mul_sum_nonneg (sq_nonneg _) (ne_of_gt hn2)]
                at gm_eq_am_pair_pow
        have am_l_eq_r := gm_eq_am_pair gm_eq_am_pair_pow
        rw [← a_split]
        have al_head_mean
                := al_am ▸
                   arithmetic_mean_eq _ al_eq
                        (al.head al_nonempty) (al.head_mem al_nonempty)
        have ar_head_mean
                := ar_am ▸
                   arithmetic_mean_eq _ ar_eq
                        (ar.head ar_nonempty) (ar.head_mem ar_nonempty)
        have eq_chain := al_head_mean.trans (am_l_eq_r.trans (Eq.symm ar_head_mean))
        apply List.all_equal_append al_eq ar_eq
                ⟨al.head al_nonempty, al.head_mem al_nonempty,
                 ar.head ar_nonempty, ar.head_mem ar_nonempty,
                 eq_chain⟩

      exact ⟨final_le, final_eq⟩

termination_by flip_parity a.length
decreasing_by
  · have al_len : min (a.length/2) a.length = a.length/2 := by omega
    simp only [List.length_take, al_len]
    exact flip_parity_decrease_even n even (by linarith : 3 ≤ n)
  · have ar_len : a.length - a.length/2 = a.length/2 := by omega
    simp only [List.length_drop, ar_len]
    exact flip_parity_decrease_even n even (by linarith : 3 ≤ n)
  · have n_def_len : n = a.length := by dsimp
    rw [List.length_append, List.length_singleton, ← n_def_len]
    simp [flip_parity,
            if_neg (Nat.not_even_iff_odd.mpr odd), if_pos (Odd.add_one odd)]

theorem harmonic_geometric_arithmetic₁
    (a : List ℝ) (nonempty : a ≠ []) (hpos : a.all_positive) :
  (harmonic_mean a ≤ geometric_mean a ∧
     (harmonic_mean a = geometric_mean a ↔ a.all_equal))
  ∧
  (geometric_mean a ≤ arithmetic_mean a ∧
     (geometric_mean a = arithmetic_mean a ↔ a.all_equal)) :=
  have gm_le_am
      : ∀ b : List ℝ, b.all_positive ∧ a.length = b.length
                → geometric_mean b ≤ arithmetic_mean b
                  ∧
                  (geometric_mean b = arithmetic_mean b ↔ b.all_equal)
      := by
      intro b ⟨b_pos, a_b_len⟩

      have b_nonempty : b ≠ [] := by
        rwa [← List.length_pos_iff_ne_nil, ← a_b_len, List.length_pos_iff_ne_nil]
      have n_pos : 0 < (b.length:ℝ) := by
        rw [← List.length_pos_iff_ne_nil] at b_nonempty
        exact Nat.cast_pos.mpr b_nonempty
      have recip_n_nonneg : 0 ≤ 1/(b.length : ℝ) := by
        rw [← inv_pos, ← one_div] at n_pos
        exact le_of_lt n_pos

      have b_prod_nonneg : 0 ≤ b.prod := le_of_lt (List.prod_pos b_pos)
      have b_am_nonneg := le_of_lt (arithmetic_mean_pos b b_nonempty b_pos)
      rw [arithmetic_mean] at b_am_nonneg

      have ⟨gm_le_am, gm_eq_am_imp⟩ := gm_le_am_cauchy b b_nonempty b_pos
      have gm_eq_am
              : b.prod = (b.sum / ↑b.length) ^ b.length ↔ b.all_equal
              := Iff.intro (gm_eq_am_imp) (geometric_arithmetic_mean_eq b)

      apply (rpow_le_rpow b_prod_nonneg · recip_n_nonneg) at gm_le_am
      rw [← Real.rpow_natCast,
          ← rpow_mul b_am_nonneg,
          mul_one_div_cancel (ne_of_gt n_pos),
          rpow_one] at gm_le_am

      rw [← Real.rpow_natCast,
          ← Real.rpow_inv_eq b_prod_nonneg b_am_nonneg
                (Ne.symm (ne_of_lt n_pos)),
          inv_eq_one_div
          ] at gm_eq_am

      exact ⟨gm_le_am, gm_eq_am⟩
  ⟨
    hm_le_gm_of_gm_le_am a.length gm_le_am a ⟨hpos, rfl⟩
  ,
    gm_le_am a ⟨hpos, rfl⟩
  ⟩


theorem harmonic_geometric_arithmetic₂ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by sorry


theorem harmonic_geometric_arithmetic₃ (n : ℕ) (hn : 1 ≤ n)
  (a : Finset.Icc 1 n → ℝ) (hpos : ∀ i, 0 < a i) :
  let harmonic := n / (∑ i : Finset.Icc 1 n, 1 / (a i))
  let geometric := (∏ i : Finset.Icc 1 n, a i) ^ ((1 : ℝ) / n)
  let arithmetic := (∑ i : Finset.Icc 1 n, a i) / n
  let all_equal := ∀ i : Finset.Icc 1 n, a i = a ⟨1, Finset.mem_Icc.mpr  ⟨NeZero.one_le, hn⟩⟩
  harmonic ≤ geometric ∧ geometric ≤ arithmetic ∧
  ((harmonic = geometric) ↔ all_equal) ∧
  ((geometric = arithmetic) ↔ all_equal) := by sorry

end Inequalities



section MantelCauchyProof

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

-- TODO: equality #E = (n^2 / 4) iff G = K_{n/2, n/2}
theorem mantel (h: G.CliqueFree 3) : #E ≤ (n^2 / 4) := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have adj_degree_bnd (i j : α) (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Assume the contrary ...
    by_contra hc; simp at hc

    -- ... then by pigeonhole there would exist a vertex k adjacent to both i and j ...
    obtain ⟨k, h⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (by simp) (by simp) hc
    simp at h
    obtain ⟨hik, hjk⟩ := h

    -- ... but then i, j, k would form a triangle, contradicting that G is triangle-free
    exact h {k, j, i} ⟨by aesop (add safe G.adj_symm), by simp [hij.ne', hik.ne', hjk.ne']⟩

  -- We need to define the sum of the degrees of the vertices of an edge ...
  let sum_deg (e : Sym2 α) : ℕ := Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  -- ... and establish a variant of adj_degree_bnd ...
  have adj_degree_bnd' (e : Sym2 α) (he: e ∈ E) : sum_deg e ≤ n := by
    induction e with | _ v w => simp at he; exact adj_degree_bnd v w (by simp [he])

  -- ... and the identity for the sum of the squares of the degrees ...
  have sum_sum_deg_eq_sum_deg_sq : ∑ e ∈ E, sum_deg e = ∑ v ∈ V, d(v)^2 := by
    calc  ∑ e ∈ E, sum_deg e
      _ = ∑ e ∈ E, ∑ v ∈ e, d(v)                  := Finset.sum_congr rfl (λ e he ↦ by induction e with | _ v w => simp at he; simp [sum_deg, he.ne])
      _ = ∑ e ∈ E, ∑ v ∈ {v' ∈ V | v' ∈ e}, d(v)  := Finset.sum_congr rfl (by intro e _; exact congrFun (congrArg Finset.sum (by ext; simp)) _)
      _ = ∑ v ∈ V, ∑ _ ∈ {e ∈ E | v ∈ e}, d(v)    := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
      _ = ∑ v ∈ V, ∑ _ ∈ I(v), d(v)               := Finset.sum_congr rfl (λ v ↦ by simp [G.incidenceFinset_eq_filter v])
      _ = ∑ v ∈ V, d(v)^2                         := by simp [Nat.pow_two]

  -- We now slightly modify the main argument to avoid division by a potentially zero n ...
  have := calc #E * n^2
    _ = (n * (∑ e ∈ E, 1)) * n               := by simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm]
    _ = (∑ _ ∈ E, n) * n                     := by rw [Finset.mul_sum]; simp
    _ ≥ (∑ e ∈ E, sum_deg e) * n             := Nat.mul_le_mul_right n (Finset.sum_le_sum adj_degree_bnd')
    _ = (∑ v ∈ V, d(v)^2) * (∑ v ∈ V, 1^2)   := by simp [sum_sum_deg_eq_sum_deg_sq]
    _ ≥ (∑ v ∈ V, d(v) * 1)^2                := (Finset.sum_mul_sq_le_sq_mul_sq V (λ v ↦ d(v)) 1)
    _ = (2 * #E)^2                           := by simp [G.sum_degrees_eq_twice_card_edges]
    _ = 4 * #E^2                             := by ring

  -- .. and clean up the inequality.
  rw [Nat.pow_two (#E)] at this
  rw [(Nat.mul_assoc 4 (#E) (#E)).symm] at this
  rw [Nat.mul_comm (4 * #E) (#E)] at this

  -- Now we can show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · simp [hE]
  · apply Nat.zero_lt_of_ne_zero at hE
    apply Nat.le_of_mul_le_mul_left this at hE
    rw [Nat.mul_comm] at hE
    exact (Nat.le_div_iff_mul_le (Nat.zero_lt_succ 3)).mpr hE

end MantelCauchyProof
