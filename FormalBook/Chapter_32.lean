/-
Copyright 2026 Egor Morozov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Morozov
-/
import FormalBook.Ch32.WDigraph
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Lattice paths and determinants

## Main results

- `lindstrom_gessel_viennot`: the Lindstrom-Gessel-Viennot lemma
- `binet_cauchy`: Binet-Cauchy determinant formula

## TODO

- Nonnegativity of binomial determinants
-/

universe u v

section LindstromGesselViennot

variable {V : Type u}
variable {R : Type v} [CommRing R]
variable (G : WDigraph V R)

open WDigraph
open Walk

variable {n : ℕ}
abbrev path_collection (A B : Fin n → V) := (i : Fin n) → G.Walk (A i) (B i)

namespace path_collection

variable {A B : Fin n → V} (P : path_collection G A B)
variable {G}

def weight := ∏ (i : Fin n), (P i).weight

def copy {B' : Fin n → V} (h : B = B') : path_collection G A B' := h ▸ P

lemma copy_eq {B' : Fin n → V} (h : B = B') (i : Fin n) :
  P.copy h i = (P i).copy rfl (congrFun h i) := by
  subst h
  rw [copy_rfl_rfl]
  rfl

@[ext]
structure intersection where
  i : Fin n
  j : Fin n
  ki : ℕ
  kj : ℕ
  hne : i ≠ j
  heq : (P i).getVert ki = (P j).getVert kj

def to_prod (I : intersection P) : Fin n ×ₗ ℕ ×ₗ Fin n ×ₗ ℕ :=
  toLex (I.i, toLex (I.ki, toLex (I.j, I.kj)))

lemma to_prod_inj : Function.Injective (to_prod P) := by
  intro X Y h
  simp [to_prod] at h
  ext1 <;> tauto

instance : LinearOrder (intersection P) := LinearOrder.lift'
  (to_prod P) (to_prod_inj P)

instance instWellFoundedLT : WellFoundedLT (intersection P) where
  wf := InvImage.wf (to_prod P) wellFounded_lt

noncomputable section

variable [Nonempty (intersection P)]

def X := (WellFoundedLT.toOrderBot (h := instWellFoundedLT P)).bot

lemma not_lt_X (I : intersection P) : ¬I < X P := by
  simp [X, not_lt_bot]

lemma X_ki_le_length : (X P).ki ≤ (P (X P).i).length := by
  by_contra! h
  let I : P.intersection :=
    { i := (X P).i
      j := (X P).j
      ki := (P (X P).i).length
      kj := (X P).kj
      hne := (X P).hne
      heq := by
        rw [← (X P).heq, getVert_of_ge_length _ (le_refl _),
            getVert_of_ge_length _ (le_of_lt h)] }
  have hI : I < X P := by
    change to_prod P I < to_prod P (X P)
    simpa [to_prod, Prod.Lex.toLex_lt_toLex, I]
  exact not_lt_X _ _ hI

lemma X_kj_le_length : (X P).kj ≤ (P (X P).j).length := by
  by_contra! h
  let I : P.intersection :=
    { i := (X P).i
      j := (X P).j
      ki := (X P).ki
      kj := (P (X P).j).length
      hne := (X P).hne
      heq := by
        rw [(X P).heq, getVert_of_ge_length _ (le_refl _),
            getVert_of_ge_length _ (le_of_lt h)] }
  have hI : I < X P := by
    change to_prod P I < to_prod P (X P)
    simpa [to_prod, Prod.Lex.toLex_lt_toLex, I]
  exact not_lt_X _ _ hI

@[grind →]
lemma X_i_lt_j : (X P).i < (X P).j := by
  by_contra! h
  replace h : (X P).j < (X P).i := lt_of_le_of_ne h (X P).hne.symm
  let I : P.intersection :=
    { i := (X P).j
      j := (X P).i
      ki := (X P).kj
      kj := (X P).ki
      hne := (X P).hne.symm
      heq := (X P).heq.symm }
  have hI : I < X P := by
    change to_prod P I < to_prod P (X P)
    simp_all [to_prod, Prod.Lex.toLex_lt_toLex, I]
  exact not_lt_X _ _ hI

lemma X_i_ne_j : (X P).i ≠ (X P).j := ne_of_lt (X_i_lt_j P)

def swap : path_collection G A (B ∘ Equiv.swap (X P).i (X P).j) := fun l =>
  if hi : l = (X P).i then
    ((P l).take (X P).ki).append
      (((P (X P).j).drop (X P).kj).copy (hi ▸ (X P).heq.symm) (by simp [hi]))
  else if hj : l = (X P).j then
    ((P l).take (X P).kj).append
      (((P (X P).i).drop (X P).ki).copy (hj ▸ (X P).heq) (by simp [hj]))
  else (P l).copy rfl (by simp [Equiv.swap_apply_of_ne_of_ne hi hj])

lemma swap_i : swap P (X P).i =
  ((P (X P).i).take (X P).ki).append
  (((P (X P).j).drop (X P).kj).copy (X P).heq.symm (by simp)) := by
  rw [swap, dite_eq_left rfl]

lemma swap_j : swap P (X P).j =
  ((P (X P).j).take (X P).kj).append
  (((P (X P).i).drop (X P).ki).copy (X P).heq (by simp)) := by
  rw [swap, dite_eq_right ((X P).hne.symm), dite_eq_left rfl]

lemma swap_ne (l : Fin n) (hi : l ≠ (X P).i) (hj : l ≠ (X P).j) :
  swap P l = (P l).copy rfl (by simp [Equiv.swap_apply_of_ne_of_ne hi hj]) :=
  by rw [swap, dite_eq_right hi, dite_eq_right hj]

lemma swap_weight : P.swap.weight = P.weight := by
  rw [weight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (X P).i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr
      ⟨(X_i_ne_j P).symm, Finset.mem_univ _⟩), ← mul_assoc]
  have aux (a b c d : R) : a * b * (c * d) = a * d * (c * b) := by ring
  rw [swap_i, weight_append, swap_j, weight_append, aux]
  simp only [copy_weight, ← weight_append, append_take_drop_eq]
  rw [Finset.prod_congr (g := fun i ↦ (P i).weight) rfl]
  · rw [weight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (X P).i),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr
        ⟨(X_i_ne_j P).symm, Finset.mem_univ _⟩), ← mul_assoc]
  · intro l _
    rw [swap_ne P l, copy_weight] <;> grind

def Y : intersection (swap P) :=
  { i := (X P).i
    j := (X P).j
    ki := (X P).ki
    kj := (X P).kj
    hne := (X P).hne
    heq := by simp [swap, (X P).hne.symm, getVert_append,
                    X_ki_le_length P, X_kj_le_length P, (X P).heq] }

instance instNonemptySwap : Nonempty (intersection (swap P)) :=
  Nonempty.intro (Y P)

lemma X_swap_le_Y : to_prod _ (X (swap P)) ≤ to_prod _ (Y P) := by
  change (X (swap P)) ≤ (Y P)
  simp only [X]
  --it is not clear why simp only [X, bot_le] does not work
  let instOrderBot : OrderBot P.swap.intersection :=
    (WellFoundedLT.toOrderBot (h := instWellFoundedLT _))
  exact @bot_le _ _ _ (Y P)

def Z_i : Fin n :=
  if (X (swap P)).i = (X P).i ∧ (X (swap P)).ki > (X P).ki then (X P).j else
  if (X (swap P)).i = (X P).j ∧ (X (swap P)).ki > (X P).kj then (X P).i else
  (X (swap P)).i

def Z_j : Fin n :=
  if (X (swap P)).j = (X P).i ∧ (X (swap P)).kj > (X P).ki then (X P).j else
  if (X (swap P)).j = (X P).j ∧ (X (swap P)).kj > (X P).kj then (X P).i else
  (X (swap P)).j

def Z_ki : ℕ :=
  if (X (swap P)).i = (X P).i ∧ (X (swap P)).ki > (X P).ki then 
  (X P).kj + ((X (swap P)).ki - (X P).ki) else
  if (X (swap P)).i = (X P).j ∧ (X (swap P)).ki > (X P).kj then
  (X P).ki + ((X (swap P)).ki - (X P).kj) else
  (X (swap P)).ki

def Z_kj : ℕ :=
  if (X (swap P)).j = (X P).i ∧ (X (swap P)).kj > (X P).ki then 
  (X P).kj + ((X (swap P)).kj - (X P).ki) else
  if (X (swap P)).j = (X P).j ∧ (X (swap P)).kj > (X P).kj then
  (X P).ki + ((X (swap P)).kj - (X P).kj) else
  (X (swap P)).kj

lemma Z_i_getVert : (P (Z_i P)).getVert (Z_ki P) =
  (swap P (X (swap P)).i).getVert
  (X (swap P)).ki := by
  rw [swap]
  split_ifs with hi hj <;> rw [Z_i, Z_ki]
  case neg => grind [getVert_copy]
  all_goals rw [getVert_append, take_length, getVert_copy, drop_getVert,
    take_getVert]
  · grind [X_ki_le_length, (X P).hne]
  · grind [X_kj_le_length, (X P).hne]

lemma Z_j_getVert : (P (Z_j P)).getVert (Z_kj P) =
  (swap P (X (swap P)).j).getVert
  (X (swap P)).kj := by
  rw [swap]
  split_ifs with hi hj <;> rw [Z_j, Z_kj]
  case neg => grind [getVert_copy]
  all_goals rw [getVert_append, take_length, getVert_copy, drop_getVert,
    take_getVert]
  · grind [X_ki_le_length, (X P).hne]
  · grind [X_kj_le_length, (X P).hne]

lemma Z_getVert : (P (Z_i P)).getVert (Z_ki P) =
  (P (Z_j P)).getVert (Z_kj P) := by
  rw [Z_i_getVert, Z_j_getVert, (X (swap P)).heq]

def Z (hne : Z_i P ≠ Z_j P) : intersection P :=
  { i := Z_i P
    j := Z_j P
    ki := Z_ki P
    kj := Z_kj P
    hne := hne
    heq := Z_getVert P }

lemma not_Z_le_X (hne : Z_i P ≠ Z_j P) : ¬to_prod P (Z P hne) < to_prod P (X P)
  := by
  change ¬Z P hne < X P
  simp [X, not_lt_bot]

lemma swap_i_eq : (X (swap P)).i = (X P).i := by
  apply eq_of_le_of_ge
  · change (X (swap P)).i ≤ (Y P).i
    have := X_swap_le_Y P
    simp only [to_prod, Prod.Lex.toLex_le_toLex] at this
    grind
  · by_contra! h
    have hZi : Z_i P = (X (swap P)).i := by
      unfold Z_i
      grind [X_i_lt_j]
    have hne : Z_i P ≠ Z_j P := by
      unfold Z_j
      grind [X_i_lt_j]
    apply not_Z_le_X P hne
    simp [to_prod, Prod.Lex.toLex_lt_toLex, Z, hZi, h]

variable [PathFinite G]

lemma swap_ki_eq : (X (swap P)).ki = (X P).ki := by
  apply eq_of_le_of_ge
  · change (X (swap P)).ki ≤ (Y P).ki
    have := X_swap_le_Y P
    simp only [to_prod, Prod.Lex.toLex_le_toLex, swap_i_eq, Y] at *
    grind
  · by_contra! h
    have hZi : Z_i P = (X P).i := by
      rw [Z_i, swap_i_eq]
      grind
    have hZki : Z_ki P = (X (swap P)).ki := by
      rw [Z_ki, swap_i_eq]
      grind
    by_cases! hj : (X (swap P)).j = (X P).j ∧ (X (swap P)).kj > (X P).kj
    · have hZj : Z_j P = (X P).i := by
        rw [Z_j]
        grind
      have : Z_kj P = (X P).ki + ((X (swap P)).kj - (X P).kj) := by
        rw [Z_kj]
        grind
      refine acyclic_of_path_finite (P (Z_i P)) (Z_ki P) (Z_kj P) ?_ ?_ ?_
      · omega
      · rw [hZki, hZi]
        left
        exact lt_of_lt_of_le h (X_ki_le_length P)
      · conv_rhs => rw [Eq.trans hZi hZj.symm]
        exact Z_getVert P
    · have hne : Z_i P ≠ Z_j P := by
        unfold Z_i Z_j
        grind
      apply not_Z_le_X P hne
      simp [to_prod, Prod.Lex.toLex_lt_toLex, Z, hZi, hZki, h]

lemma Z_i_eq : Z_i P = (X P).i := by
  unfold Z_i
  rw [swap_i_eq, swap_ki_eq]
  grind

lemma Z_ki_eq : Z_ki P = (X P).ki := by
  unfold Z_ki
  rw [swap_i_eq, swap_ki_eq]
  grind

lemma swap_j_eq : (X (swap P)).j = (X P).j := by
  apply eq_of_le_of_ge
  · change (X (swap P)).j ≤ (Y P).j
    have := X_swap_le_Y P
    simp only [to_prod, Prod.Lex.toLex_le_toLex, swap_i_eq, swap_ki_eq, Y] at *
    grind
  · by_contra! h
    have aux : (X P).i ≠ (X (swap P)).j := by
      conv_lhs => rw [← swap_i_eq]
      exact X_i_ne_j (swap P)
    have hZj : Z_j P = (X (swap P)).j := by
      unfold Z_j
      grind
    have hne : Z_i P ≠ Z_j P := by
      rw [Z_i_eq, hZj]
      exact aux
    apply not_Z_le_X P hne
    simp [to_prod, Prod.Lex.toLex_lt_toLex, Z, Z_i_eq, Z_ki_eq, hZj, h]

lemma swap_kj_eq : (X (swap P)).kj = (X P).kj := by
  apply eq_of_le_of_ge
  · change (X (swap P)).kj ≤ (Y P).kj
    have := X_swap_le_Y P
    simp only [to_prod, Prod.Lex.toLex_le_toLex, swap_i_eq, swap_ki_eq,
      swap_j_eq, Y] at *
    grind
  · by_contra! h
    have hZj : Z_j P = (X P).j := by
      rw [Z_j, swap_j_eq]
      grind
    have hZkj : Z_kj P = (X (swap P)).kj := by
      rw [Z_kj, swap_j_eq]
      grind
    have hne : Z_i P ≠ Z_j P := by
      rw [Z_i_eq, hZj]
      exact (X P).hne
    apply not_Z_le_X P hne
    simp [to_prod, Prod.Lex.toLex_lt_toLex, Z, Z_i_eq, Z_ki_eq, hZj, hZkj, h]

lemma swap_B_eq : B = (B ∘ ⇑(Equiv.swap (X P).i (X P).j)) ∘
  ⇑(Equiv.swap (X (swap P)).i (X (swap P)).j) := by
  rw [swap_i_eq, swap_j_eq]
  exact (Equiv.comp_symm_eq _ _ _).mp rfl

lemma swap_i_take_aux : (P (X P).i).getVert (X P).ki =
  (swap P (X (swap P)).i).getVert (X (swap P)).ki := by
  rw [swap_i_eq, swap_ki_eq, swap_i, getVert_append, ite_eq_left,
      take_getVert, min_self]
  rw [take_length, min_eq_left (X_ki_le_length P)]

lemma swap_i_take : (swap P (X (swap P)).i).take (X (swap P)).ki =
  ((P (X P).i).take (X P).ki).copy
    (congrArg _ (swap_i_eq P).symm) (swap_i_take_aux P) := by
  rw! [swap_i_eq, swap_ki_eq, swap_i, take_append_of_le_length,
       take_of_le_length ((P (X P).i).take (X P).ki), copy_copy]
  · rfl
  all_goals rw [take_length, min_eq_left (X_ki_le_length P)]

lemma swap_j_take_aux : (P (X P).j).getVert (X P).kj =
  (swap P (X (swap P)).j).getVert (X (swap P)).kj := by
  rw [swap_j_eq, swap_kj_eq, swap_j, getVert_append, ite_eq_left,
      take_getVert, min_self]
  rw [take_length, min_eq_left (X_kj_le_length P)]

lemma swap_j_take : (swap P (X (swap P)).j).take (X (swap P)).kj =
  ((P (X P).j).take (X P).kj).copy
    (congrArg _ (swap_j_eq P).symm) (swap_j_take_aux P) := by
  rw! [swap_j_eq, swap_kj_eq, swap_j, take_append_of_le_length,
       take_of_le_length ((P (X P).j).take (X P).kj), copy_copy]
  · rfl
  all_goals rw [take_length, min_eq_left (X_kj_le_length P)]

lemma swap_i_drop_aux : (P (X P).j).getVert (X P).kj =
  (swap P (X (swap P)).i).getVert (X (swap P)).ki := by
  rw! [swap_i_eq, swap_ki_eq, swap_i, getVert_append, ite_eq_left,
       take_getVert, min_self, (X P).heq]
  · rfl
  all_goals rw [take_length, min_eq_left (X_ki_le_length P)]

lemma swap_i_drop : (swap P (X (swap P)).i).drop (X (swap P)).ki =
  ((P (X P).j).drop (X P).kj).copy (swap_i_drop_aux P)
  (by simp [swap_i_eq]) := by
  rw! [swap_i_eq, swap_ki_eq, swap_i, drop_append_of_ge_length, take_length,
       min_eq_left (X_ki_le_length P), Nat.sub_self, drop_zero,
       copy_copy, copy_copy]
  · rfl
  all_goals rw [take_length, min_eq_left (X_ki_le_length P)]

lemma swap_j_drop_aux : (P (X P).i).getVert (X P).ki =
  (swap P (X (swap P)).j).getVert (X (swap P)).kj := by
  rw! [swap_j_eq, swap_kj_eq, swap_j, getVert_append, ite_eq_left,
       take_getVert, min_self, (X P).heq]
  · rfl
  all_goals rw [take_length, min_eq_left (X_kj_le_length P)]

lemma swap_j_drop : (swap P (X (swap P)).j).drop (X (swap P)).kj =
  ((P (X P).i).drop (X P).ki).copy (swap_j_drop_aux P)
  (by simp [swap_j_eq]) := by
  rw! [swap_j_eq, swap_kj_eq, swap_j, drop_append_of_ge_length, take_length,
       min_eq_left (X_kj_le_length P), Nat.sub_self, drop_zero,
       copy_copy, copy_copy]
  · rfl
  all_goals rw [take_length, min_eq_left (X_kj_le_length P)]

lemma swap_swap : swap (swap P) = P.copy (swap_B_eq P) := by
  ext l
  rw [swap]
  split_ifs with hi hj
  · subst hi
    rw [swap_i_take, swap_j_drop, copy_copy, append_copy_copy,
        append_take_drop_eq, path_collection.copy_eq]
    rw! [swap_i_eq]
    rfl
  · subst hj
    rw [swap_j_take, swap_i_drop, copy_copy, append_copy_copy,
        append_take_drop_eq, path_collection.copy_eq]
    rw! [swap_j_eq]
    rfl
  · rw [swap_i_eq] at hi
    rw [swap_j_eq] at hj
    rw [swap_ne P l hi hj, copy_copy, path_collection.copy_eq]

end
end path_collection

open path_collection

abbrev path_system (A B : Fin n → V) :=
  (σ : Equiv.Perm (Fin n)) × path_collection G A (B ∘ σ)

namespace path_system

variable (A B : Fin n → V) (P : path_system G A B)

abbrev NonemptyIntersection := Nonempty P.2.intersection
abbrev VertexDisjoint := ∀ (i j : Fin n), i ≠ j → ¬Intersecting (P.2 i) (P.2 j)

lemma vertex_disjoint_iff_nonempty_intersection : ∀ (P : path_system G A B),
  ¬VertexDisjoint G A B P ↔ NonemptyIntersection G A B P := by
  intro P
  unfold VertexDisjoint
  push Not
  constructor <;> intro h
  · rcases h with ⟨i, j, hne, hdis⟩
    rw [Intersecting] at hdis
    rcases hdis with ⟨ki, kj, heq⟩
    exact Nonempty.intro
      { i := i 
        j := j 
        ki := ki
        kj := kj 
        hne := hne
        heq := heq }
  · exact ⟨(X P.2).i, (X P.2).j, (X P.2).hne, (X P.2).ki, (X P.2).kj,
      (X P.2).heq⟩

def sign : ℤˣ := Equiv.Perm.sign P.1
def weight : R := P.2.weight

noncomputable section

variable (P : Subtype (NonemptyIntersection G A B))

instance : NonemptyIntersection G A B P := P.prop

def swap : Subtype (NonemptyIntersection G A B) :=
  ⟨⟨P.val.1 * (Equiv.swap P.val.2.X.i P.val.2.X.j), P.val.2.swap⟩, by 
    simp only [NonemptyIntersection, Equiv.Perm.coe_mul]
    exact Nonempty.intro (path_collection.Y P.val.2)⟩

lemma swap_sign : (swap G A B P).val.sign = -P.val.sign := by
  simp [sign, swap, P.val.2.X_i_ne_j]

lemma swap_weight : (swap G A B P).val.weight = P.val.weight := by
  simp [weight, swap, path_collection.swap_weight]

lemma swap_inv [PathFinite G] : Function.Involutive (swap G A B) := by
  rw [Function.Involutive.eq_1]
  intro P
  rw [swap]; ext l
  · simp [swap, swap_i_eq, swap_j_eq]
  · simp [swap, swap_swap, copy]

end
end path_system

open path_system

variable [PathFinite G]

noncomputable def path_matrix (A B : Fin n → V) :=
    Matrix.of (fun i j => ∑ (p : G.Walk (A i) (B j)), p.weight)

lemma det_path_matrix_eq_sum (A B : Fin n → V) :
  (path_matrix G A B).det = ∑ (P : path_system G A B), P.sign • P.weight := by
  rw [← Matrix.det_transpose, Matrix.det_apply, path_matrix, Matrix.transpose]
  simp_rw [Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
           sign, path_system.weight, Fintype.sum_sigma, Finset.smul_sum]
  rfl

open Classical in
lemma sum_not_path_disjoint_eq_zero (A B : Fin n → V) :
  ∑ (P : path_system G A B) with ¬VertexDisjoint G A B P,
    P.sign • P.weight = 0 := by
  rw [Finset.filter_congr (q := NonemptyIntersection G A B)]
  · let g (P : path_system G A B) (h : P ∈ Finset.filter
      (NonemptyIntersection G A B) Finset.univ) : path_system G A B :=
    (path_system.swap G A B ⟨P, by simp_all⟩).val
    refine Finset.sum_involution g ?_ ?_ ?_ ?_ <;> intro P h <;> subst g <;>
    let := (Finset.mem_filter.mp h).2
    · simp [swap_sign, path_system.swap_weight]
    · intro _
      have : P.1 * Equiv.swap P.2.X.i P.2.X.j ≠ P.1 := by
        simp [path_collection.X_i_ne_j]
      grind [path_system.swap, Sigma.ext]
    · simp [NonemptyIntersection, path_system.swap, instNonemptySwap P.2]
    · simp [swap_inv G A B ⟨P, _⟩]
  · intro P _
    exact vertex_disjoint_iff_nonempty_intersection G A B P

open Classical in
theorem lindstrom_gessel_viennot (A B : Fin n → V) :
  (path_matrix G A B).det = ∑ (P : path_system G A B) with
    VertexDisjoint G A B P, P.sign • P.weight := by
  rw [det_path_matrix_eq_sum,
      ← Finset.sum_filter_add_sum_filter_not _ (VertexDisjoint G A B) _,
      sum_not_path_disjoint_eq_zero, add_zero]

end LindstromGesselViennot

section BinetCauchy

lemma eq_zero_or_eq_one_or_ge_two (n : ℕ) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  grind

lemma fin_inj_image_card {α : Type*} [LinearOrder α] {k : ℕ} {f : Fin k → α}
  (h : Function.Injective f) : (Finset.univ.image f).card = k := by
  rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]

variable {R : Type v} [CommRing R]
variable (r s : ℕ)
variable (P : Matrix (Fin r) (Fin s) R) (Q : Matrix (Fin s) (Fin r) R)

abbrev V := (Fin r) ⊕ (Fin s) ⊕ (Fin r)

abbrev A : Fin r → V r s := Sum3.in₀
abbrev B : Fin s → V r s := Sum3.in₁
abbrev C : Fin r → V r s := Sum3.in₂

def G : WDigraph (V r s) R :=
  { weight := fun i j => match i, j with
    | Sum3.in₀ i, Sum3.in₁ j => some (P i j)
    | Sum3.in₁ i, Sum3.in₂ j => some (Q i j)
    | _, _ => none }

lemma G_adj_AB (i : Fin r) (j : Fin s) : (G r s P Q).Adj (A r s i) (B r s j) :=
  by rfl

@[simp]
lemma G_weight_AB (i : Fin r) (j : Fin s) : (G r s P Q).weight (A r s i) (B r s
  j) = P i j := by rfl

lemma G_adj_BC (i : Fin s) (j : Fin r) : (G r s P Q).Adj (B r s i) (C r s j) :=
  by rfl

@[simp]
lemma G_weight_BC (i : Fin s) (j : Fin r) : (G r s P Q).weight (B r s i) (C r s
  j) = Q i j := by rfl

lemma G_walk_CC_aux (i : Fin r) (j : Fin r)
  (p : (G r s P Q).Walk (Sum.inr (Sum.inr i)) (C r s j)) : i = j := by
  cases p with
  | nil => rfl
  | @cons _ x _ hx px =>
    rcases x with _ | _ | _ <;> simp [G, WDigraph.Adj] at hx

lemma G_walk_CC (i : Fin r) (j : Fin r)
  (p : (G r s P Q).Walk (Sum.inr (Sum.inr i)) (C r s j)) :
  p = (WDigraph.Walk.nil (u := C r s j)).copy
  (G_walk_CC_aux r s P Q i j p ▸ (Eq.refl _)) (Eq.refl _) := by
  cases p with
  | nil => rfl
  | @cons _ x _ hx px =>
    rcases x with _ | _ | _ <;> simp [G, WDigraph.Adj] at hx

def f (i j : Fin r) (k : Fin s) :
  (G r s P Q).Walk (A r s i) (C r s j) :=
  WDigraph.Walk.cons (G_adj_AB r s P Q i k)
    (WDigraph.Walk.cons (G_adj_BC r s P Q k j) WDigraph.Walk.nil)

lemma f_bij (i : Fin r) (j : Fin r) :
  Function.Bijective (f r s P Q i j) := by
  constructor
  · intro _ _ h
    simp [f, B] at h
    grind
  · intro p
    cases p with | @cons _ x _ hx px
    rcases x with _ | x | _
    · simp [WDigraph.Adj, G] at hx
    · use x
      simp only [f, B]
      cases px with | @cons _ y _ hy py
      rcases y with _ | _ | y
      · simp [WDigraph.Adj, G] at hy
      · simp [WDigraph.Adj, G] at hy
      · simp [G_walk_CC r s P Q y j py, C, G_walk_CC_aux r s P Q y j py]
    · simp [WDigraph.Adj, G] at hx

open Classical in
lemma f_bijInv (i j : Fin r) (p : (G r s P Q).Walk (A r s i) (C r s j)) :
  B r s (Fintype.bijInv (f_bij r s P Q i j) p) = p.getVert 1 := by
  rcases Function.Bijective.surjective (f_bij r s P Q i j) p with ⟨k, hk⟩
  rw [← hk, Fintype.leftInverse_bijInv]
  simp [f]

open path_system

def preF (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) × Equiv.Perm (Fin r)) :
  path_system (G r s P Q) (A r s) (C r s) :=
  ⟨p.2.2 * p.2.1, fun i => f r s P Q i ((p.2.2 * p.2.1) i) ((p.1 ∘ p.2.1) i)⟩

lemma preF_length
  (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) × Equiv.Perm (Fin r)) (i : Fin r) :
  ((preF r s P Q p).2 i).length = 2 := by
  simp [preF, f]

@[simp]
lemma preF_zero (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) × Equiv.Perm (Fin r))
  (i : Fin r) : ((preF r s P Q p).2 i).getVert 0 = A r s i := by
  simp [preF]

@[simp]
lemma preF_one (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) × Equiv.Perm (Fin r))
  (i : Fin r) : ((preF r s P Q p).2 i).getVert 1 = B r s ((p.1 ∘ p.2.1) i) := by
  simp [preF, f]

lemma preF_two (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) × Equiv.Perm (Fin r))
  (i : Fin r) {k : ℕ} (hk : k ≥ 2) :
  ((preF r s P Q p).2 i).getVert k = C r s ((p.2.2 * p.2.1) i) := by
  have h : ((preF r s P Q p).2 i).length ≤ k := by
    simp only [preF_length r s P Q p i, hk]
  rw [WDigraph.Walk.getVert_of_ge_length _ h]
  simp [preF]

lemma preF_vertex_disjoint (p : (Fin r ↪o Fin s) × Equiv.Perm (Fin r) ×
  Equiv.Perm (Fin r)) : VertexDisjoint (G r s P Q) (A r s) (C r s)
  (preF r s P Q p) := by
  intro i j h'
  rw [WDigraph.Walk.Intersecting]
  push Not
  intro ki kj
  rcases eq_zero_or_eq_one_or_ge_two ki with rfl | rfl | hi <;>
  rcases eq_zero_or_eq_one_or_ge_two kj with rfl | rfl | hj <;>
  simp only [Function.comp_apply, preF_one, WDigraph.Walk.getVert_zero, ne_eq]
  any_goals rw [preF_two r s P Q p i hi]
  any_goals rw [preF_two r s P Q p j hj]
  all_goals simp [A, B, C] <;> grind [RelEmbedding.injective p.1,
    Equiv.injective p.2.1, Equiv.injective p.2.2]

def F := Subtype.coind (preF r s P Q) (preF_vertex_disjoint r s P Q)

open Classical in
lemma F_bij : Function.Bijective (F r s P Q) := by
  constructor
  · apply Subtype.coind_injective
    intro p q h
    simp only [preF, Sigma.mk.injEq] at h
    rcases h with ⟨h1, h2⟩
    rw [h1] at h2
    have h3 : p.1 ∘ p.2.1 = q.1 ∘ q.2.1 := by
      funext i
      exact Function.Bijective.injective (f_bij r s P Q i _)
        (congrFun (eq_of_heq h2) i)
    have h4 : Finset.univ.image p.1 = Finset.univ.image q.1 := by
      calc
        _ = Finset.univ.image (p.1 ∘ p.2.1) := by
          rw [← Finset.image_image, Finset.image_univ_equiv]
        _ = Finset.univ.image (q.1 ∘ q.2.1) := by rw [h3]
        _ = Finset.univ.image q.1 := by
          rw [← Finset.image_image, Finset.image_univ_equiv]
    have h5 : p.1 = q.1 := by
      calc
        _ = (Finset.univ.image p.1).orderEmbOfFin
          (fin_inj_image_card (RelEmbedding.injective p.1)) := by
          rw [← Finset.orderEmbOfFin_unique'
            (fin_inj_image_card (RelEmbedding.injective p.1))
            (f := p.1) (by simp)]
        _ = (Finset.univ.image q.1).orderEmbOfFin
          (fin_inj_image_card (RelEmbedding.injective q.1)) := by
          rw! [h4]; rfl
        _ = q.1 := by
          rw [← Finset.orderEmbOfFin_unique'
          (fin_inj_image_card (RelEmbedding.injective q.1))
            (f := q.1) (by simp)]
    rw [h5] at h3
    replace h3 := DFunLike.coe_fn_eq.mp (Function.Injective.comp_left
      (RelEmbedding.injective q.1) h3)
    rw [h3] at h1
    replace h1 := (mul_left_inj q.2.1).mp h1
    grind
  · rintro ⟨q, hq⟩
    let e := fun i => Fintype.bijInv (f_bij r s P Q i (q.1 i)) (q.2 i)
    have he : Function.Injective e := by
      intro i j h
      simp only [e] at h
      contrapose! hq
      rw [VertexDisjoint]; push Not
      use i, j
      refine ⟨hq, ?_⟩
      rw [WDigraph.Walk.Intersecting]
      use 1, 1
      rw [← f_bijInv, ← f_bijInv, h]
    let p1 := Finset.orderEmbOfFin _ (fin_inj_image_card he)
    let p21 : Equiv.Perm (Fin r) := {
      toFun := fun i => (Finset.orderIsoOfFin _ (fin_inj_image_card he)).symm
        ⟨e i, by simp⟩
      invFun := fun i => Function.Injective.invOfMemRange he
        ⟨(Finset.orderIsoOfFin _ (fin_inj_image_card he) i), by
          apply mem_image_univ_iff_mem_range.mp; simp⟩
      left_inv := by simp [Function.LeftInverse]
      right_inv := by
        rw [Function.RightInverse, Function.LeftInverse]
        intro i
        rcases Finset.mem_image.mp (((Finset.image e Finset.univ).orderIsoOfFin
          (fin_inj_image_card he)) i).prop with ⟨j, _, hj⟩
        rw! [← hj, Function.Injective.right_inv_of_invOfMemRange, hj]
        simp [-Finset.coe_orderIsoOfFin_apply] }
    use ⟨p1, p21, q.1 * p21.symm⟩
    simp only [F, Subtype.coind, preF, Equiv.Perm.coe_mul, Subtype.mk.injEq]
    apply Sigma.ext
    · simp [pull_end]
      grind
    · simp only [Equiv.Perm.coe_mul, Function.comp_assoc]
      rw [Equiv.symm_comp_self, Function.comp_id, heq_eq_eq]
      ext i
      simp [← Finset.coe_orderIsoOfFin_apply, Equiv.coe_fn_mk, p1, p21, e,
        Function.RightInverse.eq (Fintype.rightInverse_bijInv (f_bij r s P Q i
        (q.1 i)))]

lemma F_weight (Z : Fin r ↪o Fin s) (σ τ : Equiv.Perm (Fin r)) :
  (F r s P Q (Z, σ, τ)).val.weight =
  (∏ (j : Fin r), (Q (Z j) (τ j))) * ∏ (i : Fin r), (P i (Z (σ i))) := by
  simp [F, Subtype.coind, preF, f, weight, path_collection.weight,
    Finset.prod_mul_distrib, Fintype.prod_equiv σ
      (fun x ↦ Q (Z (σ x)) (τ (σ x)))
      (fun x ↦ Q (Z x) (τ x)) (congrFun rfl)]

lemma F_sign (Z : Fin r ↪o Fin s) (σ τ : Equiv.Perm (Fin r)) :
  (F r s P Q (Z, σ, τ)).val.sign = τ.sign * σ.sign := by
  simp [F, preF, f, sign]

lemma G_walk_C {i : Fin r} {v : V r s} (p : (G r s P Q).Walk (C r s i) v) :
  p.length = 0 := by
  cases p with
  | nil => simp
  | cons e _ => simp [G, WDigraph.Adj] at e

lemma G_walk_B {i : Fin s} {v : V r s} (p : (G r s P Q).Walk (B r s i) v) :
  p.length ≤ 1 := by
  cases p with
  | nil => simp
  | @cons _ w _ e q =>
    match w with
      | Sum.inr (Sum.inr _) => simp [G_walk_C]
      | Sum.inr (Sum.inl _) => simp [G, WDigraph.Adj] at e
      | Sum.inl _ => simp [G, WDigraph.Adj] at e

lemma G_walk_A {i : Fin r} {v : V r s} (p : (G r s P Q).Walk (A r s i) v) :
  p.length ≤ 2 := by
  cases p with
  | nil => simp
  | @cons _ w _ e q =>
    match w with
      | Sum.inr (Sum.inr _) => simp [G, WDigraph.Adj] at e
      | Sum.inr (Sum.inl _) => simp [G_walk_B]
      | Sum.inl _ => simp [G, WDigraph.Adj] at e

instance : WDigraph.Walk.PathFinite (G r s P Q) := by
  apply WDigraph.Walk.path_finite_of_bounded_length (k := 3)
  intro u
  match u with
    | Sum.inr (Sum.inr _) => simp [G_walk_C]
    | Sum.inr (Sum.inl _) => grind [G_walk_B]
    | Sum.inl _ => grind [G_walk_A]

lemma path_matrix_G_eq_PQ : path_matrix (G r s P Q) (A r s) (C r s) =
  P * Q := by
  ext i j
  rw [path_matrix, Matrix.mul_apply]; dsimp
  rw [← Function.Bijective.sum_comp (f_bij r s P Q i j)]
  congr; funext
  rw! [f, WDigraph.Walk.weight, WDigraph.Walk.weight, G_weight_AB, G_weight_BC]
  simp [mul_comm]
  rfl

open Classical in
theorem binet_cauchy : Matrix.det (P * Q) =
  ∑ (Z : Fin r ↪o Fin s), (Matrix.det (P.submatrix id Z)) *
  (Matrix.det (Q.submatrix Z id)) := by
  rw [← path_matrix_G_eq_PQ, lindstrom_gessel_viennot,
    ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ,
    ← Function.Bijective.sum_comp (F_bij r s P Q), Fintype.sum_prod_type]
  congr; funext Z
  rw [Fintype.sum_prod_type, ← Matrix.det_transpose]
  nth_rw 2 [← Matrix.det_transpose]
  simp only [Matrix.det_apply, Matrix.submatrix, id_eq, Matrix.transpose, 
    Matrix.of_apply, Fintype.sum_mul_sum]
  congr; funext σ
  congr; funext τ
  rw [F_weight, F_sign, mul_smul_mul_comm, mul_comm]

end BinetCauchy

