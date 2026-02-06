/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.BourbakiWitt

/-!
# The chromatic number of Kneser graphs

## TODO
  - The Borsuk-Ulam theorem (sketched in the book, is probably a whole different task)
  - Gale's Theorem (only stated in the book and never used to prove the main statement)
-/

noncomputable section

/-- The Borsuk-Ulam theorem in dimension `d` states that for any continuous map from the `d`-sphere
  to `\mathbb{R}^d`, there exists a pair of antipodal points with the same image. -/
theorem borsuk_ulam (d : ℕ) :
  ∀ f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d),
  ContinuousOn f (Metric.sphere 0 1) →
  ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, f x = f (-x) := by
  sorry -- This will probably be in Mathlib at some point. We assume it to be true for now.

/-- Given a collection of sets `U_i`, there exists a point `x` on the sphere such that the distance
  from `x` to `U_i` is the same as the distance from `-x` to `U_i` for all `i < d`. -/
theorem borsuk_ulam_distances {d : ℕ}
    (U : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin (d + 1)))) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, ∀ i : Fin d,
    Metric.infDist x (U (Fin.castSucc i)) = Metric.infDist (-x) (U (Fin.castSucc i)) := by
  have h_borsuk := borsuk_ulam d
  specialize h_borsuk (fun x => (WithLp.equiv 2 _).symm
  (fun (i : Fin d) => Metric.infDist x (U i.castSucc))) ?_
  · rw[WithLp.equiv_symm_apply]; fun_prop (disch := solve_by_elim);
  · simp only [WithLp.equiv_symm_apply, WithLp.toLp.injEq] at h_borsuk
    exact ⟨h_borsuk.choose, h_borsuk.choose_spec.1, fun i => congr_fun h_borsuk.choose_spec.2 i⟩

/-- If an open set `U` intersected with a symmetric closed set `S` (like a sphere) contains no
  antipodal points, then the closure of that intersection also contains no antipodal points.
  Since we need to apply this to the sphere, which is in particular closed, we may take the closure
  in the ambient space `E`, which is more convenient to formalize.
  Since the open sets of `S` are obtained by intersecting open sets of `E` with `S`, this is indeed
  what is required. -/
lemma closure_inter_sphere_disjoint_neg_of_open_inter_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (U : Set E) (h_open : IsOpen U) (S : Set E)
    (hS_symm : ∀ x ∈ S, -x ∈ S) (h_disjoint : Disjoint (U ∩ S) {x | -x ∈ U ∩ S}) :
    Disjoint (closure (U ∩ S)) {x | -x ∈ U ∩ S} := by
  rw [ Set.disjoint_left ] at *;
  intro x hx h_neg_x_closure;
  obtain ⟨xn, hxn⟩ : ∃ xn : ℕ → E, (∀ n, xn n ∈ U ∩ S) ∧
    Filter.Tendsto xn Filter.atTop (nhds x) := by
    rwa [ mem_closure_iff_seq_limit ] at hx;
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, -xn n ∈ U := by
    have h_neg_xn_in_U : Filter.Tendsto (fun n => -xn n) Filter.atTop (nhds (-x)) := by
      exact hxn.2.neg;
    exact Filter.eventually_atTop.mp ( h_neg_xn_in_U ( h_open.mem_nhds h_neg_x_closure.1 ) );
  exact h_disjoint ( hxn.1 N ) ⟨ hN N le_rfl, hS_symm _ ( hxn.1 N |>.2 ) ⟩

/-- If the `d`-sphere `S^d` is covered by `d+1` sets, i.e.,
  `S^d = U_1 \cup \dots \cup U_d \cup U_{d+1}`, such that each of the first `d` sets
  `U_1, \dots, U_d` is either open or closed, then one of the `d+1` sets contains a pair of
  antipodal points `x^*, -x^*`. Here, we rather take the `U_i` to be open/closed sets of `R^{d+1}`
  whose intersection with `S^d` determines the corresponding open set in the cover. -/
lemma lusternik_schnirelmann {d : ℕ}
    (U : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin (d + 1))))
    (h_cover : (⋃ i, U i) ⊇ Metric.sphere 0 1)
    (h_open_closed : ∀ i : Fin (d + 1), i ≠ Fin.last d → IsOpen (U i) ∨ IsClosed (U i)) :
    ∃ i, ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, x ∈ U i ∧ -x ∈ U i := by
      obtain ⟨x, hx⟩ : ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
        ∀ i : Fin d,
        Metric.infDist x (U (Fin.castSucc i) ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
        = Metric.infDist (-x) (U (Fin.castSucc i) ∩ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
        convert borsuk_ulam_distances _ using 1;
        convert rfl;
        rotate_right;
        use fun i => U i ∩ Metric.sphere 0 1;
        · rfl;
        · bound;
      obtain ⟨k, hk⟩ : ∃ k : Fin (d + 1),
        x ∈ U k ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
        exact Exists.elim ( Set.mem_iUnion.mp ( h_cover hx.1 ) ) fun i hi => ⟨ i, hi, hx.1 ⟩;
      by_cases hk_last : k = Fin.last d;
      · obtain ⟨l, hl⟩ : ∃ l : Fin (d + 1),
          -x ∈ U l ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
          simp_all +decide [Set.subset_def];
        by_cases hl_last : l = Fin.last d;
        · exact ⟨ k, x, hx.1, hk.1 |> fun h => by aesop, by aesop ⟩;
        · have h_dist_zero : Metric.infDist x
            (U l ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) = 0 := by
            have h_dist_zero : Metric.infDist (-x)
              (U l ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) = 0 := by
              exact Metric.infDist_zero_of_mem hl;
            cases l using Fin.lastCases <;> aesop;
          have h_closure : x ∈ closure
            (U l ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
            rw [ Metric.mem_closure_iff_infDist_zero ] ; aesop;
            exact ⟨ -x, hl ⟩;
          cases h_open_closed l hl_last <;> simp_all +decide
          · have := closure_inter_sphere_disjoint_neg_of_open_inter_sphere ( U l ) ‹_›
              (Metric.sphere 0 1) (by aesop);
              simp_all +decide [Set.disjoint_left];
            exact not_forall_not.mp fun h => this
              (by intro a a_1 a_2; subst hk_last;
                  simp_all only [not_exists, not_and, not_false_eq_true, implies_true])
              h_closure hl hx.1 |> False.elim;
          · exact ⟨l, x, hx.1,
              by
                rw [closure_eq_iff_isClosed.mpr ( IsClosed.inter ‹_› ( Metric.isClosed_sphere ))]
                  at h_closure;
                aesop⟩;
      · have h_dist_zero :
          Metric.infDist (-x) (U k ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) = 0 := by
          have h_dist_zero :
            Metric.infDist x (U k ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) = 0 := by
            exact Metric.infDist_zero_of_mem hk;
          cases k using Fin.lastCases <;> aesop;
        have h_neg_x_closure :
          -x ∈ closure (U k ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
          rw [ Metric.mem_closure_iff_infDist_zero ] ; aesop;
          exact ⟨ x, hk ⟩;
        cases h_open_closed k hk_last <;> simp_all +decide only [ne_eq, mem_sphere_iff_norm,
          sub_zero, Set.mem_inter_iff, and_true];
        · have := closure_inter_sphere_disjoint_neg_of_open_inter_sphere ( U k ) ‹_›
            (Metric.sphere 0 1 ) ( by aesop ) ; simp_all +decide only [Set.mem_inter_iff,
              mem_sphere_iff_norm, sub_zero, norm_neg, Set.disjoint_left, Set.mem_setOf_eq,
              and_true, and_imp, not_and] ;
          contrapose! this
          simp_all only [not_false_eq_true, implies_true, true_and]
          obtain ⟨left, right⟩ := hx
          apply Exists.intro
          · apply And.intro
            · exact h_neg_x_closure
            · simp_all only [neg_neg, norm_neg, and_self];
        · obtain ⟨left, right⟩ := hx
          apply Exists.intro
          · apply Exists.intro
            · apply And.intro
              on_goal 2 => apply And.intro
              on_goal 2 => { exact hk
              }
              · simp_all only
              · apply h_neg_x_closure
                simp_all only [Set.mem_setOf_eq, Set.inter_subset_left, and_self]


/-- A Kneser graph for natural numbers `n`, `k` is a graph with vertices being `k`-subsets of
  `{1,..,n}` and edges between disjoint sets. -/
def KneserGraph (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} :=
  SimpleGraph.fromRel (fun v w => Disjoint v.val w.val)

/-- If `n < 2k`, the Kneser graph has no edges. -/
lemma KneserGraph_no_edges_of_lt_two_mul (n k : ℕ) (h : n < 2 * k) :
    (KneserGraph n k).edgeSet = ∅ := by
      ext ⟨s, hs⟩;
      simp +zetaDelta at *;
      by_contra h_contra
      obtain ⟨A, B, hA, hB, h_disjoint⟩ :
        ∃ A B : Finset (Fin n), A.card = k ∧ B.card = k ∧ Disjoint A B := by
        unfold KneserGraph at h_contra; aesop;
      have := Finset.card_le_univ ( A ∪ B ) ; simp_all +decide [Finset.disjoint_iff_inter_eq_empty]
      grind

/-- The chromatic number of the Kneser graph `K(2k+d, k)` is at most `d+2`. -/
lemma KneserGraph_chromaticNumber_le (n k d : ℕ) (hk : 1 ≤ k) (h : n = 2 * k + d) :
    (KneserGraph n k).chromaticNumber ≤ d + 2 := by
      refine' mod_cast SimpleGraph.Colorable.chromaticNumber_le _;
      have h_coloring : ∃ (color : Finset (Fin n) → Fin (d + 2)),
        ∀ (A B : Finset (Fin n)), A.card = k → B.card = k → Disjoint A B → color A ≠ color B := by
        use fun A => if hA : ∃ x ∈ A, x.val < d + 1 then
          ⟨ hA.choose.val, by linarith [ Fin.is_lt hA.choose, hA.choose_spec.2 ] ⟩ else
          ⟨ d + 1, by linarith ⟩;
        field_simp;
        intro A B hA hB hAB; split_ifs <;> simp_all +decide [ Fin.ext_iff, Finset.disjoint_left ] ;
        · exact fun h => hAB ( ‹∃ x ∈ A, ( x : ℕ ) < d + 1›.choose_spec.1 )
            (by convert ‹∃ x ∈ B, ( x : ℕ ) < d + 1›.choose_spec.1 using 1; exact Fin.ext h);
        · exact ne_of_lt ( ‹∃ x ∈ A, ( x : ℕ ) < d + 1›.choose_spec.2 );
        · linarith [ ‹∃ x ∈ B, ( x : ℕ ) < d + 1›.choose_spec.2 ];
        · have h_union_card : (A ∪ B).card = 2 * k := by
            rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr hAB ), hA, hB, two_mul ];
          have h_union_subset : A ∪ B ⊆ Finset.univ.filter (fun x : Fin n => x.val ≥ d + 1) := by
            intro x hx; aesop;
          have := Finset.card_le_card h_union_subset; simp_all +decide ;
          rw [ show Finset.filter (fun x : Fin n => d + 1 ≤ ( x : ℕ ))
            Finset.univ = Finset.Ici ⟨d + 1, by linarith⟩ by ext; aesop ] at this; simp_all +decide;
          omega;
      obtain ⟨ color, hcolor ⟩ := h_coloring;
      use fun v => color v.val;
      unfold KneserGraph; aesop;

/-- A set of points `S` in `R^d` is in general position if every subset of size at most `d` is
  linearly independent. -/
def GeneralPosition {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ s ⊆ S, s.card ≤ d → LinearIndependent ℝ (fun x : s => (x : EuclideanSpace ℝ (Fin d)))

/-- The moment curve is an explicit construction to obtain points in general position. -/
def momentCurve (d : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 _).symm (fun (i : Fin d) => t ^ (i : ℕ))

/-- Points on the moment curve are in general position. In particular, there exist a set of points
  in general position. We do this to construct the points explicitly for the proof. -/
lemma momentCurve_general_position {d : ℕ} {s : Finset ℝ} (hs : s.card ≤ d) :
    LinearIndependent ℝ (fun x : s => momentCurve d x) := by
      have h_vandermonde_inv : ∀ (c : Fin s.card → ℝ),
        (∀ j : Fin d, ∑ i : Fin s.card, c i * (s.orderEmbOfFin rfl i) ^ j.val = 0) → c = 0 := by
        intro c hc
        have h_vandermonde_inv : Matrix.mulVec
          (Matrix.of (fun j i : Fin s.card => (s.orderEmbOfFin rfl i) ^ j.val)) c = 0 := by
          ext j; simp_all +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
          exact hc ⟨ j, by linarith [ Fin.is_lt j ] ⟩;
        have h_vandermonde_inv : Matrix.det
          (Matrix.of (fun j i : Fin s.card => (s.orderEmbOfFin rfl i) ^ j.val)) ≠ 0 := by
          erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
          exact Finset.prod_ne_zero_iff.mpr fun i hi =>
            Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| by
            simpa [Fin.ext_iff] using ne_of_gt <| Finset.mem_Ioi.mp hj;
        exact Matrix.eq_zero_of_mulVec_eq_zero h_vandermonde_inv ‹_›;
      rw [ Fintype.linearIndependent_iff ];
      intro g hg i;
      convert congr_fun
        (h_vandermonde_inv ( fun i => g ⟨ s.orderEmbOfFin rfl i, by simp +decide⟩) ?_)
        (Fin.mk ( s.orderIsoOfFin rfl |>.symm i) (by simp only [Fin.is_lt])) using 1;
      · exact Eq.symm ( by simp +decide [ Finset.orderEmbOfFin ] );
      · intro j;
        convert congr_fun (congrArg (WithLp.equiv 2 _) hg) j using 1
        simp only [WithLp.equiv_apply, WithLp.ofLp_sum, WithLp.ofLp_smul]
        rw [ Finset.sum_apply, Finset.sum_eq_multiset_sum ];
        refine' Finset.sum_bij ( fun x _ => ⟨ s.orderEmbOfFin rfl x, by simp +decide ⟩ )
          _ _ _ _ <;> simp +decide;
        · intro x hx
          have := Finset.mem_image.mp
            (show x ∈ Finset.image (fun i : Fin s.card => s.orderEmbOfFin rfl i)
            Finset.univ from by simpa [ Finset.mem_image ] using hx) ; aesop;
        · exact fun i => Or.inl rfl

/-- The set of points `x` such that the open hemisphere defined by `x` contains some set `A` from
  `V`. In order not to deal with the sphere as a subtype, we extend this definition to the whole
  space using inner products. We will obtain the set we want by only considering sets of points
  on the sphere and then intersecting the obtained set with the sphere.
  In our case, `V` will be an element of the chosen cover of `k`-subsets of `2k + d₀`
  points in general position on the sphere `S^{d₀ + 1}`. -/
def open_set_for_subsets {d : ℕ} (V : Set (Finset (EuclideanSpace ℝ (Fin d)))) :
  Set (EuclideanSpace ℝ (Fin d)) :=
  { x | ∃ A ∈ V, ∀ y ∈ A, inner (𝕜 := ℝ) x y > 0 }

/-- The set of points `x` such that the open hemisphere defined by `x` contains some set `A` from
  `V` is open. -/
lemma is_open_open_set_for_subsets {d : ℕ} (V : Set (Finset (EuclideanSpace ℝ (Fin d)))) :
    IsOpen (open_set_for_subsets V) := by
      convert isOpen_biUnion fun A hA => ?_;
      rotate_left;
      exact Finset ( EuclideanSpace ℝ ( Fin d ) );
      exact V
      exact fun A => { x : EuclideanSpace ℝ ( Fin d ) | ∀ y ∈ A, 0 < inner ℝ x y };
      · simp +decide only [Set.setOf_forall];
        exact isOpen_biInter_finset fun x hx =>
          isOpen_lt continuous_const <| continuous_id.inner continuous_const;
      · exact Set.ext fun x =>
          ⟨fun hx => by rcases hx with ⟨A, hA, hA'⟩ ; simp; exact ⟨A, hA, hA'⟩,
          fun hx => by rcases Set.mem_iUnion₂.1 hx with ⟨A, hA, hA'⟩ ; exact ⟨ A, hA, hA' ⟩⟩

/-- If `P` is a set of `2k+d` points in general position in `R^{d+2}`, and `C` is the set of points
  `x` such that no `k`-subset of `P` lies in the open hemisphere of `x`, then `C` contains no
  antipodal points. -/
lemma no_antipodal_in_C {k d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin (d + 2))))
    (hP_card : P.card = 2 * k + d) (hP_gp : GeneralPosition P)
    (C : Set (EuclideanSpace ℝ (Fin (d + 2))))
    (hC : C = { x | ∀ A ⊆ P, A.card = k → ∃ y ∈ A, inner (𝕜 := ℝ) x y ≤ 0 }) :
    ∀ x ∈ Metric.sphere 0 1, x ∈ C → -x ∈ C → False := by
      intros x hx_mem hx_C hx_neg_C
      have h_card_Hx : (Finset.filter (fun y => inner ℝ x y > 0) P).card < k := by
        contrapose! hx_C;
        obtain ⟨ A, hA₁, hA₂ ⟩ := Finset.exists_subset_card_eq hx_C;
        exact fun hx =>
          by
            obtain ⟨ y, hy₁, hy₂ ⟩ := hC.subset hx A
              (Finset.Subset.trans hA₁ (Finset.filter_subset _ _ )) hA₂
            linarith [Finset.mem_filter.mp ( hA₁ hy₁ )]
      have h_card_Hnegx : (Finset.filter (fun y => inner ℝ (-x) y > 0) P).card < k := by
        contrapose! hx_neg_C;
        obtain ⟨ A, hA₁, hA₂ ⟩ := Finset.exists_subset_card_eq hx_neg_C;
        grind
      have h_card_Z : (Finset.filter (fun y => inner ℝ x y = 0) P).card ≥ d + 2 := by
        have h_card_Z : (Finset.filter (fun y => inner ℝ x y > 0) P).card +
          (Finset.filter (fun y => inner ℝ x y < 0) P).card +
          (Finset.filter (fun y => inner ℝ x y = 0) P).card = P.card := by
          rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
          rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ]
          rw [ Finset.card_eq_sum_ones ]
          congr
          ext y
          rcases lt_trichotomy ( inner ℝ x y ) 0 with h | h | h <;> split_ifs <;> linarith;
        simp_all +decide;
        linarith;
      have h_hyperplane : ∃ (s : Subspace ℝ (EuclideanSpace ℝ (Fin (d + 2)))),
        s ≠ ⊤ ∧ ∀ y ∈ Finset.filter (fun y => inner ℝ x y = 0) P, y ∈ s := by
        refine' ⟨LinearMap.ker ( innerₛₗ ℝ x ), _, _⟩ <;> simp_all +decide [Submodule.eq_top_iff'];
        exact ⟨ x, by rw [ real_inner_self_eq_norm_sq ] ; norm_num [ hx_mem ] ⟩;
      obtain ⟨ s, hs_ne_top, hs ⟩ := h_hyperplane;
      have h_dim_s : Module.finrank ℝ s ≤ d + 1 := by
        exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( le_trans ( Submodule.finrank_le _ )
          ( by norm_num ) ) fun con => hs_ne_top <| Submodule.eq_top_of_finrank_eq <| by aesop );
      have h_linear_dep : ∀ (T : Finset (EuclideanSpace ℝ (Fin (d + 2)))),
        T ⊆ Finset.filter (fun y => inner ℝ x y = 0) P → T.card > d + 1 →
        ¬LinearIndependent ℝ (fun y : T => (y : EuclideanSpace ℝ (Fin (d + 2)))) := by
        intros T hT_sub hT_card hT_lin_ind
        have hT_dim : Module.finrank ℝ (Submodule.span ℝ (T : Set (EuclideanSpace ℝ (Fin (d + 2)))))
          ≤ d + 1 := by
          exact le_trans
            (Submodule.finrank_mono <| Submodule.span_le.mpr <| fun y hy => hs y <| hT_sub hy)
            h_dim_s;
        have hT_dim : Module.finrank ℝ (Submodule.span ℝ (T : Set (EuclideanSpace ℝ (Fin (d + 2)))))
          = T.card := by
          exact finrank_span_finset_eq_card hT_lin_ind;
        linarith;
      contrapose! h_linear_dep;
      obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq h_card_Z;
      exact ⟨ T, hT.1, by linarith, hP_gp T ( Finset.Subset.trans hT.1 ( Finset.filter_subset _ _ ))
        (by linarith) ⟩

/- If `x` and `-x` are both in the open set defined by `V`, then `V` contains two disjoint sets. -/
lemma antipodal_in_open_set_implies_disjoint_sets {d : ℕ}
    (V : Set (Finset (EuclideanSpace ℝ (Fin d)))) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ open_set_for_subsets V) (hnegx : -x ∈ open_set_for_subsets V) :
    ∃ A B, A ∈ V ∧ B ∈ V ∧ Disjoint A B := by
      obtain ⟨ A, hA, hA' ⟩ := hx;
      obtain ⟨ B, hB, hB' ⟩ := hnegx;
      exact ⟨ A, B, hA, hB, Finset.disjoint_left.mpr fun y hy hy' =>
        by have := hA' y hy; have := hB' y hy'; norm_num at *; linarith ⟩

/-- Given a finite set of points `P` of `R^d` in general position, `C` is the set of points
  such that for any `k`-set of `P` we can always find an element `y` such that `x` is not on the
  open hemisphere centered at `y`. In particular, here `C` contains all the points outside the
  sphere as well. -/
def kneser_C {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
  Set (EuclideanSpace ℝ (Fin d)) :=
  { x | ∀ A ⊆ P, A.card = k → ∃ y ∈ A, inner (𝕜 := ℝ) x y ≤ 0 }

/-- The union of the open sets `O_i` and the set `C` covers the entire space. -/
lemma kneser_cover_eq_univ {d k n : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d)))
    (V : Fin n → Set (Finset (EuclideanSpace ℝ (Fin d))))
    (h_partition : (⋃ i, V i) = { A | A ⊆ P ∧ A.card = k }) :
    (⋃ i, open_set_for_subsets (V i)) ∪ kneser_C P k = Set.univ := by
      ext x
      simp [open_set_for_subsets, kneser_C];
      by_cases h : ∃ i : Fin n, ∃ A ∈ V i, ∀ y ∈ A, 0 < ( inner ( 𝕜 := ℝ ) x y ) <;>
        simp_all +decide [ Set.ext_iff ];
      exact Or.inr fun A hA₁ hA₂ =>
        by
            obtain ⟨ i, hi ⟩ := h_partition A |>.2 ⟨ hA₁, hA₂ ⟩
            obtain ⟨ y, hy₁, hy₂ ⟩ := h i A hi
            exact ⟨ y, hy₁, hy₂ ⟩

/-- The set `C` defined for the Kneser graph proof is closed. -/
lemma is_closed_kneser_C {d k : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) :
    IsClosed (kneser_C P k) := by
      set V := { A : Finset (EuclideanSpace ℝ (Fin d)) | A ⊆ P ∧ A.card = k } with hV;
      have hC_eq : kneser_C P k =
        ⋂ A ∈ V, ⋃ y ∈ A, { x : EuclideanSpace ℝ (Fin d) | inner (𝕜 := ℝ) x y ≤ 0 } :=
          by ext; aesop;
      refine' hC_eq ▸ isClosed_biInter fun A hA => _;
      exact Set.Finite.isClosed_biUnion ( Finset.finite_toSet A )
        fun y hy => isClosed_le ( continuous_id.inner continuous_const ) continuous_const

/-- Given a partition of the `k`-subsets of a set of points in general position into `d+1` classes,
  one class contains two disjoint sets. this actually holds on the entire space `R^{d+2}`.-/
theorem kneser_geometric_lemma {k d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin (d + 2))))
    (hP_card : P.card = 2 * k + d)
    (hP_gp : GeneralPosition P)
    (V : Fin (d + 1) → Set (Finset (EuclideanSpace ℝ (Fin (d + 2)))))
    (h_partition : (⋃ i, V i) = { A | A ⊆ P ∧ A.card = k }) :
    ∃ i, ∃ A B, A ∈ V i ∧ B ∈ V i ∧ Disjoint A B := by
      have h_cover : (⋃ i, open_set_for_subsets (V i)) ∪ kneser_C P k ⊇ Metric.sphere 0 1 := by
        exact Set.subset_univ _ |> Set.Subset.trans <| kneser_cover_eq_univ P V h_partition |>
          fun h => h.symm ▸ Set.Subset.refl _;
      obtain ⟨j, x, hx⟩ : ∃ j : Fin (d + 2), ∃ x : EuclideanSpace ℝ (Fin (d + 2)),
        x ∈ Metric.sphere 0 1 ∧ x ∈ (if h : j.val < d + 1 then
        open_set_for_subsets (V ⟨j.val, h⟩) else kneser_C P k) ∧
        -x ∈ (if h : j.val < d + 1 then open_set_for_subsets (V ⟨j.val, h⟩) else kneser_C P k) := by
        have h_lusternik_schnirelmann : ∀ (U : Fin (d + 2) → Set (EuclideanSpace ℝ (Fin (d + 2)))),
          (⋃ i, U i) ⊇ Metric.sphere 0 1 → (∀ i : Fin (d + 2), i ≠ Fin.last (d + 1) →
          IsOpen (U i)) → ∃ i : Fin (d + 2), ∃ x : EuclideanSpace ℝ (Fin (d + 2)),
          x ∈ Metric.sphere 0 1 ∧ x ∈ U i ∧ -x ∈ U i := by
          intros U hU hU_open
          apply lusternik_schnirelmann U hU (fun i hi => Or.inl (hU_open i hi));
        specialize h_lusternik_schnirelmann (fun i => if h : i.val < d + 1
          then open_set_for_subsets (V ⟨i.val, h⟩) else kneser_C P k);
        refine' h_lusternik_schnirelmann _ _;
        · intro x hx; specialize h_cover hx; simp_all +decide [ Fin.exists_iff ] ;
          rcases h_cover with ( ⟨ i, hi, hx ⟩ | hx ) <;> [ exact
            ⟨ i, Nat.lt_succ_of_lt hi, by simpa [ hi ] using hx ⟩ ;
            exact ⟨ d + 1, Nat.lt_succ_self _, by simpa [ Nat.lt_succ_iff ] using hx ⟩ ];
        · intro i hi; split_ifs <;> simp_all +decide [ Fin.ext_iff ] ;
          · apply_rules [ is_open_open_set_for_subsets ]
          · exact False.elim <| hi <| le_antisymm ( Fin.is_le _ ) ‹_›;
      split_ifs at hx <;> simp_all +decide [ open_set_for_subsets ];
      · obtain ⟨ A, hA₁, hA₂ ⟩ := hx.2.1
        obtain ⟨ B, hB₁, hB₂ ⟩ := hx.2.2
        use ⟨ j, by linarith ⟩, A, hA₁, B, hB₁; rw [ Finset.disjoint_left ]
        intro y hy₁ hy₂
        have := hA₂ y hy₁
        have := hB₂ y hy₂
        linarith;
      · have := no_antipodal_in_C P hP_card hP_gp ( kneser_C P k ) rfl x ( by aesop ) hx.2.1 hx.2.2
        aesop

/-- The geometric Kneser graph on a set of points `P` with parameter `k` has vertices as
  `k`-subsets of `P` and edges between disjoint sets. -/
def GeometricKneserGraph {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    SimpleGraph {s : Finset (EuclideanSpace ℝ (Fin d)) // s ⊆ P ∧ s.card = k} :=
  SimpleGraph.fromRel (fun v w => Disjoint v.val w.val)

/-- The vertices of the geometric Kneser graph on `P` are in bijection with the vertices of the
  standard Kneser graph `K(|P|, k)`. -/
def isoGeometricKneserGraphVertices {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    {s : Finset (EuclideanSpace ℝ (Fin d)) // s ⊆ P ∧ s.card = k} ≃
    {s : Finset (Fin P.card) // s.card = k} :=
  let α := {x // x ∈ P}
  let h_card : Fintype.card α = P.card := Fintype.card_coe P
  let e : α ≃ Fin P.card := (Fintype.equivFin α).trans (Equiv.cast (congr_arg Fin h_card))
  { toFun := fun ⟨s, hs⟩ => ⟨s.attach.map ⟨fun x => e ⟨x.1, hs.1 x.2⟩, by
      exact e.injective.comp fun x y hxy => by aesop;⟩, by
      simp +decide [ ← hs.2, Finset.card_map ]⟩
    invFun := fun ⟨t, ht⟩ => ⟨t.map ⟨fun y => (e.symm y).1, by
      exact fun x y hxy => e.symm.injective <| Subtype.ext hxy⟩, by
      simp +decide [ Finset.subset_iff, Finset.card_map, ht ]⟩
    left_inv := fun ⟨s, hs⟩ => (by
    ext x; simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists, ↓existsAndEq, Equiv.symm_apply_apply, exists_prop, exists_eq_right])
    right_inv := fun ⟨t, ht⟩ => (by
    ext; simp +decide [ Finset.mem_map];
    constructor;
    · rintro ⟨ a, ⟨ b, hb, rfl ⟩, rfl ⟩ ; aesop;
    · intro h;
      use e.symm ‹_›;
      subst ht
      simp_all only [Equiv.symm_trans_apply, Subtype.coe_eta, Equiv.trans_apply,
        Equiv.apply_symm_apply, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
        exists_const, α, e]) }

/-- The geometric Kneser graph on `P` is isomorphic to the standard Kneser graph `K(|P|, k)`. -/
def isoGeometricKneserGraph {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    GeometricKneserGraph P k ≃g KneserGraph P.card k :=
  { toEquiv := isoGeometricKneserGraphVertices P k
    map_rel_iff' := fun {v w} => by
      simp [GeometricKneserGraph, KneserGraph]
      unfold isoGeometricKneserGraphVertices; simp +decide [ Finset.disjoint_left ] ;
      intro hvw; constructor <;> intro h <;> contrapose! h <;> aesop; }

/- The chromatic number of the geometric Kneser graph on `P` is strictly greater than `d+1`. -/
theorem chromatic_number_geometric_kneser_gt {k d : ℕ} (hk : 1 ≤ k)
    (P : Finset (EuclideanSpace ℝ (Fin (d + 2))))
    (hP_card : P.card = 2 * k + d)
    (hP_gp : GeneralPosition P) :
    (GeometricKneserGraph P k).chromaticNumber > d + 1 := by
      by_contra h_contra;
      obtain ⟨coloring, hcoloring⟩ : ∃ coloring :
        {s : Finset (EuclideanSpace ℝ (Fin (d + 2))) // s ⊆ P ∧ s.card = k} → Fin (d + 1),
        ∀ v w : {s : Finset (EuclideanSpace ℝ (Fin (d + 2))) // s ⊆ P ∧ s.card = k}, v ≠ w →
        Disjoint v.val w.val → coloring v ≠ coloring w := by
        have h_colorable : (GeometricKneserGraph P k).Colorable (d + 1) := by
          simp +zetaDelta at *;
          exact SimpleGraph.chromaticNumber_le_iff_colorable.mp h_contra;
        obtain ⟨ coloring, hcoloring ⟩ := h_colorable;
        exact ⟨ coloring,
          fun v w hvw hdisj => fun h => hvw <|
            by have := @hcoloring v w; simp_all +decide [ GeometricKneserGraph ] ⟩;
      set V : Fin (d + 1) → Set (Finset (EuclideanSpace ℝ (Fin (d + 2)))) :=
        fun i => {A | ∃ v : {s : Finset (EuclideanSpace ℝ (Fin (d + 2))) // s ⊆ P ∧ s.card = k},
          coloring v = i ∧ v.val = A};
      obtain ⟨i, A, B, hA, hB, h_disjoint⟩ : ∃ i : Fin (d + 1),
        ∃ A B : Finset (EuclideanSpace ℝ (Fin (d + 2))), A ∈ V i ∧ B ∈ V i ∧ Disjoint A B := by
        have := kneser_geometric_lemma P hP_card hP_gp V ?_;
        · exact this;
        · ext A; aesop;
      obtain ⟨ v, hv₁, hv₂ ⟩ := hA;
      obtain ⟨ w, hw₁, hw₂ ⟩ := hB;
      specialize hcoloring v w;
      simp_all +decide [ Finset.disjoint_left ] ;
      exact absurd ( Finset.eq_empty_of_forall_notMem h_disjoint ) ( by aesop )

/-- Isomorphic graphs have the same chromatic number. -/
lemma SimpleGraph.Iso.chromaticNumber_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber := by
      refine' le_antisymm _ _;
      · have h_coloring : ∀ (n : ℕ), H.Colorable n → G.Colorable n := by
          rintro n ⟨ f, hf ⟩;
          use fun v => f (e v);
          exact fun { a b } hab => hf ( e.map_adj_iff.mpr hab );
        exact chromaticNumber_le_of_forall_imp h_coloring;
      · have h_colorable : ∀ k, G.Colorable k → H.Colorable k := by
          intro k hk;
          obtain ⟨ c, hc ⟩ := hk;
          use fun w => c (e.symm w);
          exact fun { a b } hab => hc ( e.symm.map_adj_iff.mpr hab );
        exact chromaticNumber_le_of_forall_imp h_colorable

/-- The set of `n` points on the moment curve in `R^d`. -/
def momentCurvePoints (n d : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) :=
  (Finset.univ : Finset (Fin n)).image (fun (i : Fin n) => momentCurve d (i : ℝ))

/-- The set of points on the moment curve has size `n`, provided `d \geq 2`. -/
lemma momentCurvePoints_card (n d : ℕ) (hd : 2 ≤ d) : (momentCurvePoints n d).card = n := by
  convert Finset.card_image_of_injective _ _;
  · norm_num;
  · unfold momentCurve
    intro i j h
    simp only [WithLp.equiv_symm_apply, WithLp.toLp.injEq] at h
    have := congrFun h ⟨ 1, by linarith ⟩
    simp_all only [pow_one, Nat.cast_inj]
    ext : 1
    simp_all only

/-- The points on the moment curve are in general position. -/
lemma momentCurvePoints_generalPosition (n d : ℕ) :
    GeneralPosition (momentCurvePoints n (d + 2)) := by
      intro s hs hcard
      have h_sub :
        ∃ I : Finset ℝ, s = I.image (fun t => momentCurve (d + 2) t) ∧ I.card = s.card := by
        have h_sub : ∃ I : Finset ℝ, s = I.image (fun t => momentCurve (d + 2) t) := by
          use Finset.image (fun x => x) (Finset.filter (fun x => momentCurve (d + 2) x ∈ s)
            (Finset.image (fun i : Fin n => (i : ℝ)) (Finset.univ : Finset (Fin n))));
          ext x; simp [Finset.mem_image];
          constructor <;> intro hx;
          · have := hs hx; unfold momentCurvePoints at this; aesop;
          · grind;
        obtain ⟨ I, rfl ⟩ := h_sub;
        rw [ Finset.card_image_of_injective ];
        · use I;
        · intro t t' h_eq;
          simpa using congr_fun ( WithLp.equiv 2 _ |>.symm.injective h_eq ) ⟨ 1, by linarith ⟩ ;
      obtain ⟨I, hI⟩ := h_sub
      have h_lin_ind : LinearIndependent ℝ (fun t : I => momentCurve (d + 2) t) := by
        convert momentCurve_general_position _;
        linarith;
      rw [ linearIndependent_iff' ] at *;
      intro s_1 g hg i hi
      specialize h_lin_ind (Finset.filter
        (fun x => momentCurve ( d + 2 ) x.1 ∈ s_1.image ( fun x : { x // x ∈ s } => x.val ))
        (Finset.univ : Finset { x // x ∈ I }))
        (fun x => g ⟨ momentCurve ( d + 2 ) x.1, by aesop ⟩ )
      simp_all +decide [ Finset.sum_filter ] ;
      contrapose! h_lin_ind;
      refine' ⟨ _, _ ⟩;
      · convert hg using 1;
        rw [ ← Finset.sum_filter ];
        refine' Finset.sum_bij ( fun x hx => ⟨ momentCurve ( d + 2 ) x, by aesop ⟩ ) _ _ _ _ <;>
          simp +decide [ Finset.mem_filter ];
        · intro a ha x hx hq hx' y hy z hz hq' hy' h
          simp_all +decide;
          simp_all +decide [ momentCurve ];
          replace h := congr_arg ( fun f => f 1 ) h ; aesop;
        · intro a ha ha'
          rw [ hI.1 ] at ha
          rw [ Finset.mem_image ] at ha
          obtain ⟨ t, ht, rfl ⟩ := ha
          use t
          aesop
      · grind

/-- The chromatic number of the Kneser graph `K(2k+d, k)` is exactly `d+2`. -/
theorem KneserGraph_chromaticNumber_eq (n k d : ℕ) (hk : 1 ≤ k) (h : n = 2 * k + d) :
    (KneserGraph n k).chromaticNumber = d + 2 := by
      obtain ⟨P, hP_card, hP_gp⟩ :
        ∃ P : Finset (EuclideanSpace ℝ (Fin (d + 2))), P.card = n ∧ GeneralPosition P := by
        use Finset.image ( fun i : Fin n => momentCurve ( d + 2 ) i ) Finset.univ;
        rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · convert momentCurvePoints_generalPosition n ( d ) using 1;
        · simp +decide [ Fin.ext_iff, momentCurve ];
          intro i j h; have := congr_fun h 1; aesop;
      have h_chromatic_ge : (GeometricKneserGraph P k).chromaticNumber > d + 1 := by
        convert chromatic_number_geometric_kneser_gt hk P ( by linarith ) hP_gp using 1;
      have h_iso :
        (KneserGraph n k).chromaticNumber = (GeometricKneserGraph P k).chromaticNumber := by
        have h_iso : (GeometricKneserGraph P k) ≃g (KneserGraph n k) := by
          convert isoGeometricKneserGraph P k;
          · exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm hP_card))) n);
          · linarith;
          · exact hP_card.symm;
        exact Eq.symm (SimpleGraph.Iso.chromaticNumber_eq h_iso);
      have h_chromatic_le : (KneserGraph n k).chromaticNumber ≤ d + 2 := by
        convert KneserGraph_chromaticNumber_le n k d hk h using 1;
      refine' le_antisymm h_chromatic_le _;
      refine' h_iso ▸ le_of_not_gt fun h => _;
      contrapose! h_chromatic_ge;
      exact Order.le_of_lt_add_one h
