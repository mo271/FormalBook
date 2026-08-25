import Mathlib

/-!
# Brouwer Fixed Point Theorem via Covering Spaces

Auxiliary machinery for Chapter 28: the no-retraction theorem and
Brouwer's fixed-point theorem in 2D via covering space arguments.
-/

noncomputable section BrouwerProof

open Metric Set unitInterval Topology Complex Real

private abbrev acBase : AddCircle (1 : ℝ) := QuotientAddGroup.mk 0

private def acLoop : Path acBase acBase where
  toFun t := QuotientAddGroup.mk (t : ℝ)
  continuous_toFun := continuous_quotient_mk'.comp continuous_subtype_val
  source' := rfl
  target' := by
    show QuotientAddGroup.mk (1 : ℝ) = QuotientAddGroup.mk 0
    rw [QuotientAddGroup.eq]; simp

private def acCov : IsCoveringMap (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

private theorem acLoop_lift_eq :
    (⟨fun t => (t : ℝ), continuous_subtype_val⟩ : C(I, ℝ)) =
    acCov.liftPath acLoop.toContinuousMap 0 rfl := by
  rw [acCov.eq_liftPath_iff' rfl]
  exact ⟨by ext; simp [acLoop], by simp⟩

private theorem not_sc_addCircle : ¬ SimplyConnectedSpace (AddCircle (1 : ℝ)) := by
  intro hsc
  have hom := SimplyConnectedSpace.paths_homotopic acLoop (Path.refl acBase)
  have key := acCov.liftPath_apply_one_eq_of_homotopicRel hom 0 rfl rfl
  have h1 : (acCov.liftPath acLoop.toContinuousMap 0 rfl) 1 = (1 : ℝ) := by
    rw [← acLoop_lift_eq]; simp
  have h2 : (acCov.liftPath (Path.refl acBase).toContinuousMap 0 rfl) 1 = (0 : ℝ) := by
    have : (ContinuousMap.const I (0 : ℝ)) =
        acCov.liftPath (Path.refl acBase).toContinuousMap 0 rfl := by
      rw [acCov.eq_liftPath_iff' rfl]
      exact ⟨by ext; simp only [ContinuousMap.const_zero, ContinuousMap.coe_zero,
        Function.comp_apply, Pi.zero_apply, QuotientAddGroup.mk_zero, Path.coe_toContinuousMap,
        Path.refl_apply], by simp only [ContinuousMap.const_zero, ContinuousMap.zero_apply]⟩
    rw [← this]; simp
  rw [h1, h2] at key; exact one_ne_zero key

private theorem sc_of_retract {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace A] [SimplyConnectedSpace X]
    (i : C(A, X)) (r : C(X, A)) (hri : ∀ a, r (i a) = a) :
    SimplyConnectedSpace A := by
  rw [simply_connected_iff_paths_homotopic']
  have hX := (simply_connected_iff_paths_homotopic' (Y := X)).mp inferInstance
  refine ⟨⟨⟨r (Classical.arbitrary X)⟩, fun a b => ?_⟩, fun p₁ p₂ => ?_⟩
  · obtain ⟨p⟩ := hX.1.joined (i a) (i b)
    exact ⟨(p.map r.continuous).cast (hri a).symm (hri b).symm⟩
  · let q₁ := p₁.map i.continuous
    let q₂ := p₂.map i.continuous
    obtain ⟨H⟩ := hX.2 q₁ q₂
    have hH := H.map r
    have h₀ : q₁.map r.continuous = p₁.cast (hri _) (hri _) := by
      ext t; show r (i (p₁ t)) = p₁ t; exact hri (p₁ t)
    have h₁ : q₂.map r.continuous = p₂.cast (hri _) (hri _) := by
      ext t; show r (i (p₂ t)) = p₂ t; exact hri (p₂ t)
    rw [h₀, h₁] at hH
    exact ⟨hH⟩

private theorem sc_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [hsc : SimplyConnectedSpace X] : SimplyConnectedSpace Y :=
  sc_of_retract ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ (fun y => e.apply_symm_apply y)

private theorem not_sc_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : ¬ SimplyConnectedSpace X) : ¬ SimplyConnectedSpace Y := by
  intro hY
  apply h
  let _ : SimplyConnectedSpace Y := hY
  exact sc_of_homeomorph e.symm

private noncomputable def circleSphereHomeomorph : Circle ≃ₜ sphere (0 : ℂ) 1 where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private theorem not_sc_sphere : ¬ SimplyConnectedSpace (sphere (0 : ℂ) 1) := by
  have h1 := not_sc_addCircle
  have h2 : ¬ SimplyConnectedSpace Circle :=
    not_sc_of_homeomorph (AddCircle.homeomorphCircle one_ne_zero) h1
  exact not_sc_of_homeomorph circleSphereHomeomorph h2

private instance : ContractibleSpace (closedBall (0 : ℂ) 1) :=
  Convex.contractibleSpace (convex_closedBall (0:ℂ) 1)
    ⟨(0 : ℂ), mem_closedBall_self one_pos.le⟩

private instance : SimplyConnectedSpace (closedBall (0 : ℂ) 1) :=
  SimplyConnectedSpace.ofContractible _

private theorem no_retraction_complex :
    ¬ ∃ (r : C(closedBall (0 : ℂ) 1, sphere (0 : ℂ) 1)),
      ∀ (x : sphere (0 : ℂ) 1), r ⟨x.1, sphere_subset_closedBall x.2⟩ = x := by
  rintro ⟨r, hr⟩
  exact not_sc_sphere (sc_of_retract
    ⟨fun x => ⟨x.1, sphere_subset_closedBall x.2⟩, continuous_inclusion sphere_subset_closedBall⟩
    r hr)

private def nsq (z : ℂ) : ℝ := ‖z‖ ^ 2

private lemma nsq_eq (z : ℂ) : nsq z = Complex.normSq z :=
  (Complex.normSq_eq_norm_sq z).symm

private def rA (f : ℂ → ℂ) (x : ℂ) : ℝ := nsq (x - f x)
private def rB (f : ℂ → ℂ) (x : ℂ) : ℝ := @inner ℝ ℂ _ (f x) (x - f x)
private def rC (f : ℂ → ℂ) (x : ℂ) : ℝ := nsq (f x) - 1
private def rDisc (f : ℂ → ℂ) (x : ℂ) : ℝ := rB f x ^ 2 - rA f x * rC f x
private def rS (f : ℂ → ℂ) (x : ℂ) : ℝ := (-rB f x + Real.sqrt (rDisc f x)) / rA f x
private def rR (f : ℂ → ℂ) (x : ℂ) : ℂ := f x + (rS f x : ℂ) * (x - f x)

private lemma rA_pos {f : ℂ → ℂ} {x : ℂ}
    (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) (hx : ‖x‖ ≤ 1) : 0 < rA f x := by
  simp only [rA, nsq]; exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hfp x hx).symm)) 2

private lemma rC_nonpos {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hx : ‖x‖ ≤ 1) : rC f x ≤ 0 := by
  simp only [rC, nsq]
  have h := hfB x hx
  have h_sq : ‖f x‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← one_mul (1 : ℝ)]
    exact mul_self_le_mul_self (norm_nonneg _) h
  linarith [h_sq]

private lemma rDisc_nonneg {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) : 0 ≤ rDisc f x := by
  simp only [rDisc]
  nlinarith [sq_nonneg (rB f x), (rA_pos hfp hx).le, rC_nonpos hfB hx]

private lemma quad_at_one (f : ℂ → ℂ) (x : ℂ) :
    rA f x + 2 * rB f x + rC f x = nsq x - 1 := by
  simp only [rA, rB, rC, nsq]
  have h : ‖f x + (x - f x)‖ ^ 2 = ‖x‖ ^ 2 := by congr 1; abel_nf
  rw [norm_add_sq_real] at h
  linarith

private lemma rS_root {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) :
    rA f x * rS f x ^ 2 + 2 * rB f x * rS f x + rC f x = 0 := by
  have hA := rA_pos hfp hx
  have hΔ := rDisc_nonneg hfB hfp hx
  set B := rB f x; set C := rC f x; set A := rA f x
  set sqΔ := Real.sqrt (rDisc f x)
  have hΔeq : sqΔ ^ 2 = B ^ 2 - A * C := by
    simp only [sqΔ, rDisc]; exact Real.sq_sqrt hΔ
  have hS : rS f x = (-B + sqΔ) / A := rfl
  rw [hS]
  field_simp
  nlinarith [sq_nonneg sqΔ, hΔeq, sq_nonneg B, hA.le]

private lemma rR_norm_sq_expand (f : ℂ → ℂ) (x : ℂ) :
    nsq (rR f x) = rA f x * rS f x ^ 2 + 2 * rB f x * rS f x + rC f x + 1 := by
  simp only [rR, rA, rB, rC, nsq]
  set s := rS f x
  set a := f x
  set b := x - f x
  have hsm : (↑s : ℂ) • b = (s : ℝ) • b := Complex.coe_smul s b
  rw [show (↑s : ℂ) * b = (↑s : ℂ) • b from (smul_eq_mul ..).symm]
  rw [hsm, norm_add_sq_real a ((s : ℝ) • b), real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma rR_on_sphere {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) : ‖rR f x‖ = 1 := by
  have h : nsq (rR f x) = 1 := by rw [rR_norm_sq_expand, rS_root hfB hfp hx]; ring
  simp only [nsq] at h
  have hnn := norm_nonneg (rR f x)
  nlinarith [sq_abs ‖rR f x‖]

private lemma rS_eq_one {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) (hx1 : ‖x‖ = 1) : rS f x = 1 := by
  have hA := rA_pos hfp hx
  have hC := rC_nonpos hfB hx
  have hquad : rA f x + 2 * rB f x + rC f x = 0 := by
    rw [quad_at_one]; simp [nsq, hx1]
  have hBval : rB f x = -(rA f x + rC f x) / 2 := by linarith
  have hDiscEq : rDisc f x = ((rA f x - rC f x) / 2) ^ 2 := by
    simp only [rDisc, hBval]; ring
  have hAC : 0 ≤ (rA f x - rC f x) / 2 := by linarith
  simp only [rS, hBval, hDiscEq, Real.sqrt_sq hAC]
  field_simp; ring

private lemma rR_eq_on_sphere {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) (hx1 : ‖x‖ = 1) : rR f x = x := by
  have h1 := rS_eq_one hfB hfp hx hx1
  simp only [rR, h1]; push_cast; ring

private lemma rR_continuousOn {f : ℂ → ℂ}
    (hfc : Continuous f) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) :
    ContinuousOn (rR f) (closedBall 0 1) := by
  have hfco : ContinuousOn f (closedBall 0 1) := hfc.continuousOn
  have hA_cont : ContinuousOn (rA f) (closedBall 0 1) :=
    (continuous_norm.comp_continuousOn (continuousOn_id.sub hfco)).pow 2
  have hB_cont : ContinuousOn (rB f) (closedBall (0 : ℂ) 1) := by
    unfold rB
    have hfco' : ContinuousOn (fun x => (f x, x - f x)) (closedBall 0 1) :=
      fun x hx => ContinuousWithinAt.prodMk (hfco x hx) ((continuousOn_id.sub hfco) x hx)
    exact continuous_inner.comp_continuousOn hfco'
  have hC_cont : ContinuousOn (rC f) (closedBall 0 1) :=
    ((continuous_norm.comp_continuousOn hfco).pow 2).sub continuousOn_const
  have hDisc_cont : ContinuousOn (rDisc f) (closedBall 0 1) := by
    unfold rDisc
    exact (hB_cont.pow 2).sub (hA_cont.mul hC_cont)
  have hSqrt_cont : ContinuousOn (fun x => Real.sqrt (rDisc f x)) (closedBall 0 1) :=
    continuous_sqrt.comp_continuousOn hDisc_cont
  have hA_ne : ∀ x ∈ closedBall (0 : ℂ) 1, rA f x ≠ 0 := fun x hx =>
    ne_of_gt (rA_pos hfp (mem_closedBall_zero_iff.mp hx))
  have hS_cont : ContinuousOn (rS f) (closedBall 0 1) := by
    unfold rS
    exact (hB_cont.neg.add hSqrt_cont).div hA_cont hA_ne
  unfold rR
  exact hfco.add ((continuous_ofReal.comp_continuousOn hS_cont).mul (continuousOn_id.sub hfco))

private theorem retraction_from_fp_free {f : ℂ → ℂ}
    (hfc : Continuous f) (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1)
    (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) :
    ∃ (r : C(closedBall (0 : ℂ) 1, sphere (0 : ℂ) 1)),
      ∀ (x : sphere (0 : ℂ) 1), r ⟨x.1, sphere_subset_closedBall x.2⟩ = x := by
  refine ⟨⟨fun x => ⟨rR f x.1, mem_sphere_zero_iff_norm.mpr
    (rR_on_sphere hfB hfp (mem_closedBall_zero_iff.mp x.2))⟩,
    (rR_continuousOn hfc hfp).comp_continuous continuous_subtype_val (fun x => x.2) |>.subtype_mk _⟩,
    fun x => ?_⟩
  ext; exact congr_arg Subtype.val (by
    simp only [ContinuousMap.coe_mk]
    congr 1; exact rR_eq_on_sphere hfB hfp
      (mem_closedBall_zero_iff.mp (sphere_subset_closedBall x.2))
      (mem_sphere_zero_iff_norm.mp x.2))

private theorem brouwer_complex
    (f : ℂ → ℂ) (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  by_contra h; push_neg at h
  have hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x := fun x hx hfx => (h x hx hfx).elim
  exact no_retraction_complex (retraction_from_fp_free hf hB hfp)

theorem brouwer_fixed_point_2d_from_complex
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  set e := Complex.orthonormalBasisOneI.repr with he
  set g : ℂ → ℂ := fun z => e.symm (f (e z)) with hg
  have hgc : Continuous g := e.symm.continuous.comp (hf.comp e.continuous)
  have hgB : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1 := fun x hx => by
    simp only [hg]; rw [LinearIsometryEquiv.norm_map]
    exact hB _ (by rwa [LinearIsometryEquiv.norm_map])
  obtain ⟨z, hz1, hz2⟩ := brouwer_complex g hgc hgB
  exact ⟨e z, by rwa [LinearIsometryEquiv.norm_map], by
    have := congr_arg e hz2; simp [hg] at this; exact this⟩

end BrouwerProof

