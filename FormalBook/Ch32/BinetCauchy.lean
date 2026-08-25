import LindstromGesselViennot.WDigraph
import LindstromGesselViennot.Main

set_option linter.style.header false
/-!
# Binet-Cauchy formula

In this file we state and prove Binet-Cauchy formula for the determinant of
product of two rectangular matrices.

## Main results

- `binet_cauchy`: Binet-Cauchy formula.
-/

lemma eq_zero_or_eq_one_or_ge_two (n : ℕ) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  grind

lemma fin_inj_image_card {α : Type*} [LinearOrder α] {k : ℕ} {f : Fin k → α}
  (h : Function.Injective f) : (Finset.univ.image f).card = k := by
  rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]

universe u

variable {R : Type u} [CommRing R]
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

