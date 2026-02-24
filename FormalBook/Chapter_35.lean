/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Pi.Interval
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic

/-!
# The finite Kakeya problem

-/


noncomputable section

/-- Auxiliary lemma containing the bulk of the proof of the following: every nonzero polynomial
  `p(x) \in F[x_1, \dots, x_n]` of degree `d` has at most `dq^{n-1}` roots in `F^n`, where `q` is
  the cardinality of the field.-/
lemma lemma_35_1_aux {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
  (IH : ∀ (p : MvPolynomial (Fin n) F) (_ : p ≠ 0),
    Fintype.card {x : Fin n → F // MvPolynomial.eval x p = 0} ≤
    p.totalDegree * (Fintype.card F) ^ (n - 1))
  (p : MvPolynomial (Fin (n + 1)) F) (hp : p ≠ 0) :
  Fintype.card {x : Fin (n + 1) → F // MvPolynomial.eval x p = 0} ≤
  p.totalDegree * (Fintype.card F) ^ n := by
  set P : MvPolynomial (Fin (n + 1)) F := p;
  set d := (Polynomial.natDegree ((MvPolynomial.finSuccEquiv F n) P))
  set g := (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) P) d) with hg_def
  have hg_nonzero : g ≠ 0 := by
    aesop;
  -- We count roots $x \in F^{n+1}$ of $p$. Write $x = (a, b)$ where $a \in F^n, b \in F$.
  have h_count : Fintype.card { x : Fin (n + 1) → F // (MvPolynomial.eval x) P = 0 } ≤
    Fintype.card { a : Fin n → F | (MvPolynomial.eval a) g = 0 } * Fintype.card F +
    Fintype.card { a : Fin n → F | (MvPolynomial.eval a) g ≠ 0 } * d := by
    /- For each $a \in F^n$, the number of $b \in F$ such that $P(a, b) = 0$ is at most $d$ if
      $g(a) \neq 0$, and at most $|F|$ if $g(a) = 0$.-/
    have h_count : ∀ a : Fin n → F, Fintype.card
      { b : F | (MvPolynomial.eval (Fin.cons b a)) P = 0 } ≤ if (MvPolynomial.eval a) g = 0
      then Fintype.card F else d := by
      intro a
      by_cases ha : (MvPolynomial.eval a) g = 0;
      · simp [ha];
        exact Fintype.card_subtype_le _;
      · have h_poly_b : ∃ q : Polynomial F, q ≠ 0 ∧ q.natDegree ≤ d ∧
          ∀ b : F, (MvPolynomial.eval (Fin.cons b a)) P = q.eval b := by
          refine' ⟨ Polynomial.map ( MvPolynomial.eval a ) ( MvPolynomial.finSuccEquiv F n P ), _,
            _, _ ⟩;
          · contrapose! ha; simp_all +decide [ Polynomial.ext_iff ] ;
          · exact Polynomial.natDegree_map_le ..;
          · simp +decide [ MvPolynomial.finSuccEquiv ];
            intro b;
            induction P using MvPolynomial.induction_on
            simp +decide only [MvPolynomial.eval_C, MvPolynomial.algHom_C,
              MvPolynomial.algebraMap_eq, Polynomial.eval_map] ;
            · simp +decide only [MvPolynomial.optionEquivLeft, AlgEquiv.ofAlgHom_apply,
              MvPolynomial.algHom_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq,
              Polynomial.eval₂_C, MvPolynomial.eval_C];
            · expose_names
              simp +decide only [map_add, Polynomial.eval_map, Polynomial.map_add,
              Polynomial.eval_add, *];

            · rename_i k hk;
              refine' Fin.cases _ _ k <;> simp +decide only [MvPolynomial.eval_X, Fin.cons_succ,
                map_mul, MvPolynomial.rename_X, finSuccEquiv_succ, Polynomial.map_mul,
                Polynomial.eval_mul];
              · simp +decide [ MvPolynomial.optionEquivLeft ];
                simp_all only [ne_eq, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero,
                  EmbeddingLike.map_eq_zero_iff, not_false_eq_true, g, d]
                simp_all only [P]
                apply Or.inl
                rfl
              · simp +decide only [MvPolynomial.optionEquivLeft, AlgEquiv.ofAlgHom_apply,
                  MvPolynomial.aeval_X, Option.elim_some, Polynomial.map_C, MvPolynomial.eval_X,
                  Polynomial.eval_C, mul_eq_mul_right_iff];
                intro i
                simp_all only [ne_eq, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero,
                  EmbeddingLike.map_eq_zero_iff, not_false_eq_true, g, d]
                simp_all only [P]
                apply Or.inl
                rfl
        obtain ⟨ q, hq_ne_zero, hq_deg, hq_eval ⟩ := h_poly_b;
        simp +decide only [hq_eval, Set.coe_setOf, ha, ↓reduceIte, ge_iff_le] ;
        rw [ Fintype.card_subtype ] ;
        exact le_trans ( Finset.card_le_card ( show q.roots.toFinset ⊇ Finset.filter
          ( fun b => Polynomial.eval b q = 0 ) Finset.univ from fun x hx => by aesop ) )
          ( le_trans ( Multiset.toFinset_card_le _ ) <| le_trans ( Polynomial.card_roots' _ )
          hq_deg ) ;
    have h_count : Fintype.card { x : Fin (n + 1) → F // (MvPolynomial.eval x) p = 0 } =
      ∑ a : Fin n → F, Fintype.card { b : F | (MvPolynomial.eval (Fin.cons b a)) p = 0 } := by
      simp +decide only [Fintype.card_subtype, Finset.card_filter];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x ∘ Fin.succ, x 0 ) ) _ _ _ _ <;> simp +decide;
      · exact fun a₁ a₂ h₁ h₂ => funext fun i =>
          by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
      · exact fun a b => ⟨ Fin.cons b a, rfl, rfl ⟩;
      · exact fun a => by congr; ext i; induction i using Fin.inductionOn <;> simp +decide [ * ] ;
    refine' h_count.symm ▸ le_trans ( Finset.sum_le_sum fun a _ => ‹∀ a : Fin n → F,
      Fintype.card { b : F | ( MvPolynomial.eval ( Fin.cons b a ) ) p = 0 } ≤
      if ( MvPolynomial.eval a ) g = 0 then Fintype.card F else d› a ) _;
    simp +decide only [Finset.sum_ite, Finset.sum_const, smul_eq_mul, Set.coe_setOf, ne_eq,
      Fintype.card_subtype_compl, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin];
    simp +decide only [Finset.filter_not, Finset.card_sdiff, Finset.card_univ, Fintype.card_pi,
      Finset.prod_const, Fintype.card_fin, Finset.inter_univ, Fintype.card_subtype, le_refl];
  rcases n <;> simp_all +decide only [ne_eq, zero_tsub, pow_zero, mul_one, Nat.reduceAdd,
    Set.coe_setOf, Fintype.card_subtype_compl, Fintype.card_unique, ge_iff_le];
  · refine' le_trans h_count _;
    by_cases h : ( MvPolynomial.eval 0 ) g = 0 <;> simp_all +decide [ Fintype.card_subtype ];
    · simp_all +decide only [MvPolynomial.eval_eq', Finset.univ_eq_empty, Finset.prod_empty,
        mul_one, Finset.filter_singleton, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.prod_singleton, ↓reduceIte, Finset.card_singleton, one_mul, tsub_self, zero_mul,
        add_zero];
      contrapose! hg_nonzero;
      ext x; simp_all +decide only [Fin.isValue, MvPolynomial.coeff_zero] ;
      convert h using 1;
      rw [ Finset.sum_eq_single x ] <;> simp +contextual [ Finsupp.ext_iff ];
    · simp_all +decide [ Finset.filter_singleton ];
      split_ifs ;
      simp_all +decide only [default, Finset.card_singleton, one_mul, tsub_self, zero_mul, add_zero,
        ↓reduceIte];
      · contradiction;
      · simp only [Finset.card_empty, zero_mul, tsub_zero, one_mul, zero_add ]
        unfold d
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact MvPolynomial.degreeOf_le_totalDegree p 0
  · refine le_trans h_count ?_;
    refine' le_trans _ ( Nat.mul_le_mul_right _
      (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p d hg_nonzero) );
    rw [ add_mul ];
    refine' add_le_add _ _;
    · convert Nat.mul_le_mul_right ( Fintype.card F ) ( IH g hg_nonzero ) using 1
      rw [add_tsub_cancel_right, hg_def, pow_add, pow_one, mul_assoc]
    · rw [ mul_comm ] ;
      gcongr ;
      apply le_trans (Nat.sub_le _ _) ?_
      simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, le_refl]

/-- Every nonzero polynomial `p(x) \in F[x_1, \dots, x_n]` of degree `d` has at most `dq^{n-1}`
  roots in `F^n`, where `q` is the cardinality of the field.
  A version of this is already in Mathlib as `Mathlib.Algebra.MyPolynomial.SchwartzZippel`. -/
theorem lemma_35_1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
  {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) :
    Fintype.card {x : Fin n → F // MvPolynomial.eval x p = 0} ≤
    p.totalDegree * (Fintype.card F) ^ (n - 1) := by
  have h_ind : ∀ n : ℕ, ∀ p : MvPolynomial (Fin n) F, p ≠ 0 →
    Fintype.card { x : Fin n → F // (MvPolynomial.eval x p) = 0 } ≤
    p.totalDegree * (Fintype.card F) ^ (n - 1) := by
    intro n
    induction n;
    case zero =>
      intro p hp
      have h_const : ∃ c : F, p = MvPolynomial.C c := by
        use p.coeff 0;
        ext i;
        rw [ MvPolynomial.coeff_C ];
        simp only [Eq.symm (Subsingleton.eq_zero i), ↓reduceIte];
      simp_all only [ne_eq, zero_tsub, pow_zero, mul_one, ge_iff_le]
      obtain ⟨w, h⟩ := h_const
      subst h
      simp_all only [map_eq_zero, MvPolynomial.eval_C, Fintype.card_eq_zero,
        MvPolynomial.totalDegree_C, le_refl];
    case succ n ih => convert lemma_35_1_aux ih using 1;
  exact h_ind n p hp

/-- The set of exponents `s \in \mathbb{N}^n` such that `\sum s_i \le d`. -/
def exponents_le {n : ℕ} (d : ℕ) : Set (Fin n →₀ ℕ) := {s | s.sum (fun _ k => k) ≤ d}

/-- The set of exponents with sum at most `d` is finite. -/
lemma exponents_le_finite (n d : ℕ) : (exponents_le (n := n) d).Finite := by
  have h_finite : Set.Finite {s : Fin n → ℕ | ∀ i, s i ≤ d} := by
    exact Set.finite_iff_bddAbove.mpr ⟨ fun _ => d, fun s hs => hs ⟩;
  refine' Set.Finite.subset ( h_finite.preimage _ ) _;
  exact fun s => s;
  · exact fun x hx y hy hxy => Finsupp.ext fun i => by simpa using congr_fun hxy i;
  · intro s hs i; have := hs.out; simp_all +decide [ Finsupp.sum_fintype ] ;
    exact le_trans ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( s a ) )
      ( Finset.mem_univ i ) ) this

/-- The set of exponents with sum at most `d` is finite. -/
noncomputable instance (n d : ℕ) : Fintype (exponents_le (n := n) d) :=
  (exponents_le_finite n d).fintype

/-- The number of `n`-tuples of non-negative integers with sum at most `d` is `\binom{n+d}{n}`.
  TODO: this is not strictly the argument in the book. -/
lemma card_exponents_le (n d : ℕ) :
  Fintype.card (exponents_le (n := n) d) = (n + d).choose n := by
  rw [ Fintype.card_of_subtype ];
  have h_card : Finset.card (Finset.filter (fun y : Fin n → ℕ => ∑ i, y i ≤ d)
    (Finset.Iic (fun _ => d))) = (d + n).choose n := by
    induction' n with n ih generalizing d;
    · aesop;
    · have h_split : Finset.filter (fun y : Fin (n + 1) → ℕ => ∑ i, y i ≤ d)
        (Finset.Iic (fun _ => d)) = Finset.biUnion (Finset.range (d + 1))
        (fun k => Finset.image (fun y : Fin n → ℕ => Fin.cons k y)
        (Finset.filter (fun y : Fin n → ℕ => ∑ i, y i ≤ d - k) (Finset.Iic (fun _ => d - k)))) := by
        ext y; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor;
        · intro hy;
          refine' ⟨ y 0, _, Fin.tail y, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_succ ];
          · linarith [ hy.2, show ∑ i, y ( Fin.succ i ) ≥ 0 by exact Nat.zero_le _ ];
          · constructor
            · exact fun i => Nat.le_sub_of_add_le <|
                by
                  linarith! [ hy.1 i.succ, Finset.single_le_sum
                    ( fun a _ => Nat.zero_le ( y ( Fin.succ a ) ) ) ( Finset.mem_univ i ) ]
            · exact Nat.le_sub_of_add_le <|
                by
                  linarith! [ hy.1 0, Finset.sum_nonneg fun a ( _ : a ∈ Finset.univ ) =>
                    Nat.zero_le ( y ( Fin.succ a ) ) ];
        · rintro ⟨ a, ha, b, hb, rfl ⟩ ; simp_all +decide [ Fin.sum_univ_succ ];
          constructor
          · exact fun i => by cases i using Fin.inductionOn <;>
              [ exact Nat.le_of_lt_succ ha; exact le_trans ( hb.1 _ ) ( Nat.sub_le _ _ ) ]
          · linarith [ Nat.sub_add_cancel ( by linarith : a ≤ d ) ];
      rw [ h_split, Finset.card_biUnion ];
      · rw [ Finset.sum_congr rfl fun x hx => Finset.card_image_of_injective _ <| fun a b h =>
          by simpa [ Fin.ext_iff ] using h ];
        rw [ Finset.sum_congr rfl fun x hx => ih _ ];
        exact Nat.recOn d ( by simp +arith +decide ) fun d ih =>
          by simp +arith +decide [ Nat.choose, Finset.sum_range_succ' ] at * ; linarith;
      · intro k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; contrapose! hkl; aesop;
  swap;
  exact Finset.image ( fun y : Fin n → ℕ => ∑ i, Finsupp.single i ( y i ) )
    ( Finset.filter ( fun y : Fin n → ℕ => ∑ i, y i ≤ d ) ( Finset.Iic ( fun _ => d ) ) );
  · rw [ Finset.card_image_of_injective, h_card, add_comm ];
    intro y₁ y₂ h;
    ext i;
    replace h := congr_arg ( fun f => f i ) h;
    simp_all +decide [ Finsupp.single_apply, Finset.sum_apply' ] ;
  · simp +zetaDelta at *;
    intro x; constructor <;> intro hx;
    · rcases hx with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
      convert ha₂ using 1;
      simp +decide [ ← Finsupp.sum_finset_sum_index, exponents_le ];
    · refine' ⟨ fun i => x i, ⟨ _, _ ⟩, _ ⟩;
      · intro i; have := hx.out; simp_all +decide [ Finsupp.sum_fintype ];
        exact le_trans
          ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( x a ) ) ( Finset.mem_univ i ) ) this;
      · convert hx using 1;
        simp +decide [ Finsupp.sum_fintype, exponents_le ];
      · ext i; simp +decide;

/-- The subspace of polynomials of degree at most `d` is the span of the monomials of degree at
  most `d`. -/
lemma restrictTotalDegree_eq_span {F : Type*} [Field F] (n d : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) F d =
    Submodule.span F ((MvPolynomial.basisMonomials (Fin n) F) '' (exponents_le d)) := by
  refine' le_antisymm _ _;
  · intro p hp;
    rw [ show p = ∑ s ∈ p.support,
      p.coeff s • ( MvPolynomial.monomial s 1 : MvPolynomial ( Fin n ) F ) from ?_ ];
    · refine' Submodule.sum_mem _ fun s hs => _;
      exact Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ s, by aesop ⟩ );
    · simp +decide [ MvPolynomial.smul_monomial ];
  · rw [ Submodule.span_le ];
    rintro _ ⟨ s, hs, rfl ⟩;
    simp +decide [ MvPolynomial.mem_restrictTotalDegree, hs.out ]

/-- The dimension of the space of polynomials of degree at most `d` is `\binom{n+d}{n}`. -/
lemma dim_restrictTotalDegree (F : Type*) [Field F] (n d : ℕ) :
    Module.finrank F (MvPolynomial.restrictTotalDegree (Fin n) F d) = (n + d).choose n := by
  have : Fintype ↑(⇑(MvPolynomial.basisMonomials (Fin n) F) '' exponents_le d) := by
    apply Fintype.ofFinite ↑(⇑(MvPolynomial.basisMonomials (Fin n) F) '' exponents_le d)
  rw [ restrictTotalDegree_eq_span n d, finrank_span_set_eq_card ];
  · rw [ Set.toFinset_card ];
    rw [ Set.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
    exact card_exponents_le n d;
  · exact ( MvPolynomial.basisMonomials ( Fin n ) F ).linearIndependent.linearIndepOn_id.mono
      ( Set.image_subset_iff.mpr fun x hx => by aesop )

/-- For every set `E \subseteq F^n` of size `|E| < \binom{n+d}{n}`, there is a nonzero polynomial
  `p(x) \in F[x_1, \dots, x_n]` of degree at most `d` that vanishes on `E`. -/
theorem lemma_35_2 {F : Type*} [Field F] [Fintype F] {n d : ℕ} {E : Set (Fin n → F)}
    (hE : (@Set.toFinset _ E (Fintype.ofFinite ↑E)).card < (n + d).choose n) :
    ∃ p : MvPolynomial (Fin n) F, p ∈ MvPolynomial.restrictTotalDegree (Fin n) F d ∧ p ≠ 0 ∧
    ∀ x ∈ E, MvPolynomial.eval x p = 0 := by
  set V := MvPolynomial.restrictTotalDegree (Fin n) F d;
  let _ := (Fintype.ofFinite ↑E)
  -- Consider the evaluation map $L : V \to F^E$ defined by $L(p) = (p(a))_{a \in E}$.
  set L : V →ₗ[F] (E → F) := { toFun := fun p => fun x => MvPolynomial.eval x p.1, map_add' := by
                                aesop, map_smul' := by
                                aesop };

  have h_kernel_nontrivial : ∃ p : V, p ≠ 0 ∧ L p = 0 := by
    have h_kernel_nontrivial : LinearMap.ker L ≠ ⊥ := by
      contrapose! hE;
      have := LinearMap.finrank_range_of_inj
        ( show Function.Injective L from LinearMap.ker_eq_bot.mp hE );
      exact dim_restrictTotalDegree F n d ▸ this ▸ le_trans ( Submodule.finrank_le _ )
        ( by simp +decide [ Set.toFinset_card ]; );
    simp_all +decide [ Submodule.ne_bot_iff ];
    tauto;
  obtain ⟨ p, hp ⟩ := h_kernel_nontrivial;
  exact ⟨ p, p.2, by simpa using hp.1, fun x hx => by simpa using congr_fun ( hp.2 ) ⟨ x, hx ⟩ ⟩

/-- A set `K \subseteq F^n` is a Kakeya set if it contains a line in every direction. -/
def IsKakeyaSet (F : Type*) [Field F] {n : ℕ} (K : Set (Fin n → F)) : Prop :=
  ∀ v : Fin n → F, v ≠ 0 → ∃ w : Fin n → F, ∀ t : F, w + t • v ∈ K

/-- Given a direction `v` and a starting vector `w` in `F^n`, the polynomial `p` in `F[t]` defined
  by `p(t) = p(w + tv)`. -/
def linePoly {F : Type*} [CommSemiring F] {n : ℕ} (w v : Fin n → F) (p : MvPolynomial (Fin n) F) :
  Polynomial F :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X) p

/-- Evaluating the restriction of a polynomial to a line at a parameter `t` is the same as
  evaluating the polynomial at the point on the line corresponding to `t`. -/
lemma eval_linePoly {F : Type*} [CommSemiring F] {n : ℕ} (w v : Fin n → F)
  (p : MvPolynomial (Fin n) F) (t : F) :
    (linePoly w v p).eval t = MvPolynomial.eval (w + t • v) p := by
  rw [ linePoly ];
  simp +decide [ MvPolynomial.eval₂_eq', MvPolynomial.eval_eq' ];
  simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_prod ];
  ac_rfl

/-- The coefficient of `t^d` in `p(w+tv)` is equal to the evaluation of the homogeneous component
  of degree `d` of `p` at `v`, provided `p` has total degree at most `d`. -/
lemma coeff_linePoly_eq_homogeneousComponent_eval {F : Type*} [CommSemiring F] {n : ℕ}
    (w v : Fin n → F) (p : MvPolynomial (Fin n) F) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (linePoly w v p).coeff d = MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
  unfold linePoly MvPolynomial.homogeneousComponent;
  simp +decide [ MvPolynomial.eval₂_eq'];
  rw [ MvPolynomial.eval_eq' ];
  rw [ Finset.sum_subset ( show p.support ⊇
      ( MvPolynomial.weightedHomogeneousComponent 1 d p |> MvPolynomial.support ) from ?_ ) ];
  · refine' Finset.sum_congr rfl fun x hx => _;
    by_cases h : Finsupp.sum x ( fun i k => k ) = d <;>
      simp_all +decide [ MvPolynomial.coeff_weightedHomogeneousComponent ];
    · simp +decide [ ← h, Finsupp.weight ];
      simp +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
      rw [ Finset.prod_congr rfl fun i _ => by rw [ add_comm, add_pow ] ];
      simp +decide [mul_pow ];
      rw [ Finset.prod_sum ];
      rw [ Polynomial.finset_sum_coeff, Finset.sum_eq_single ( fun i _ => x i ) ] <;>
        simp +decide [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum ]
      · simp +decide [ Polynomial.coeff_mul, Polynomial.coeff_X_pow ];
        rw [ Finset.sum_eq_single ( 0, ∑ i, x i ) ] <;> simp +decide;
        · simp +decide [ Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod ];
        · aesop;
      · intro b hb hb';
        rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
        refine' lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) _;
        refine' lt_of_le_of_lt ( add_le_add ( Polynomial.natDegree_mul_le .. )
          ( Polynomial.natDegree_prod_le _ _ ) ) _;
        refine' lt_of_le_of_lt ( add_le_add_three ( Polynomial.natDegree_mul_le .. )
          ( Polynomial.natDegree_prod_le _ _ )
          ( Finset.sum_le_sum fun i _ => Polynomial.natDegree_C _ |> le_of_eq ) ) _;
        simp +decide;
        refine' lt_of_le_of_lt ( add_le_add_three ( Polynomial.natDegree_prod_le _ _ )
          ( Polynomial.natDegree_X_pow_le _ )
          ( Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le .. ) ) _;
        refine' lt_of_le_of_lt ( add_le_add_three ( Finset.sum_le_sum fun i _ =>
          Polynomial.natDegree_pow_le .. ) ( Finset.sum_le_sum fun i _ => le_rfl )
          ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( Nat.sub_le _ _ )
            ( Nat.zero_le _ ) ) ) _;
        simp +decide [ Polynomial.natDegree_C ];
        refine' Finset.sum_lt_sum _ _;
        · exact fun i _ => Nat.le_of_lt_succ ( hb i );
        · grind;
    · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
      · simp_all +decide [ Finsupp.weight ];
        simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
      · refine' lt_of_le_of_lt ( Polynomial.natDegree_prod_le _ _ ) _;
        refine' lt_of_le_of_lt _ ( lt_of_le_of_ne ( show x.sum ( fun i k => k ) ≤ d from _ ) h );
        · refine' le_trans ( Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le ) _;
          simp +decide [ Finsupp.sum_fintype ];
          exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( Nat.zero_le _ )
            ( by by_cases hi : v i = 0 <;> simp +decide [ hi ] );
        · exact le_trans ( Finset.le_sup ( f := fun s => s.sum fun i k => k )
            ( Finsupp.mem_support_iff.mpr hx ) ) hd;
  · aesop;
  · intro m hm;
    contrapose! hm;
    simp_all +decide [ MvPolynomial.coeff_weightedHomogeneousComponent ] ;

/-- The degree of the restriction of a polynomial to a line is at most the total degree of the
  polynomial. -/
lemma natDegree_linePoly_le {F : Type*} [CommSemiring F] {n : ℕ} (w v : Fin n → F)
    (p : MvPolynomial (Fin n) F) :
    (linePoly w v p).natDegree ≤ p.totalDegree := by
  refine' le_trans ( Polynomial.natDegree_sum_le _ _ |> le_trans <| Finset.sup_le _ ) _;
  exact p.totalDegree;
  · intro a ha;
    refine' le_trans ( Polynomial.natDegree_C_mul_le _ _ ) _;
    refine' le_trans ( Polynomial.natDegree_prod_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun i _ => _ ) _;
    exact fun i => a i;
    · refine' le_trans ( Polynomial.natDegree_pow_le ) _;
      by_cases hi : v i = 0 <;> simp +decide [ hi ];
    · exact Finset.le_sup ( f := fun s => s.sum fun x e => e ) ha;
  · rfl

/-- If a polynomial `p` has degree less than `|F|` and vanishes on a line `w + tv`, then the
  homogeneous component of `p` of degree `\deg p` vanishes at the direction vector `v`. -/
lemma eval_homogeneousComponent_eq_zero_of_forall_eval_line_eq_zero
    {F : Type*} [Field F] [Fintype F] {n : ℕ} (p : MvPolynomial (Fin n) F)
    (h_deg : p.totalDegree < Fintype.card F)
    (w v : Fin n → F)
    (h_zero : ∀ t : F, MvPolynomial.eval (w + t • v) p = 0) :
    MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) = 0 := by
  have hP_zero : ∀ t : F, (linePoly w v p).eval t = 0 := by
    exact fun t => by simpa [ eval_linePoly ] using h_zero t;
  have hP_zero_poly : (linePoly w v p).natDegree < Fintype.card F := by
    exact lt_of_le_of_lt ( natDegree_linePoly_le _ _ _ ) h_deg;
  have hP_zero_poly : (linePoly w v p) = 0 := by
    exact
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (linePoly w v p) Finset.univ
        (fun i a => hP_zero i) hP_zero_poly
  have := coeff_linePoly_eq_homogeneousComponent_eval w v p p.totalDegree le_rfl; aesop;

/-- If `n > 0` and `K` is a Kakeya set, and `p` is a polynomial of degree `< |F|` vanishing on `K`,
  then the top homogeneous component of `p` vanishes everywhere. -/
lemma eval_homogeneousComponent_eq_zero_of_vanishes_on_Kakeya
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : n > 0)
    {K : Set (Fin n → F)} (hK : IsKakeyaSet F K)
    (p : MvPolynomial (Fin n) F) (hp_deg : p.totalDegree < Fintype.card F)
    (h_vanish : ∀ x ∈ K, MvPolynomial.eval x p = 0) :
    ∀ v, MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) = 0 := by
  cases eq_or_ne ( MvPolynomial.totalDegree p ) 0;
  case inl hd =>
    obtain ⟨c, hc⟩ : ∃ c : F, p = MvPolynomial.C c := by
      use p.coeff 0;
      exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd;
    obtain ⟨ v, hv ⟩ := hK ( fun _ => 1 ) ( fun h => by simpa using congr_fun h ⟨ 0, hn ⟩ ) ; aesop;
  case inr hd =>
    intro v
    by_cases hv : v = 0;
    · simp +decide [ hv, MvPolynomial.homogeneousComponent_apply ];
      simp +contextual [ MvPolynomial.constantCoeff_monomial ];
      exact fun _ => Ne.symm hd;
    · obtain ⟨ w, hw ⟩ := hK v hv;
      exact  eval_homogeneousComponent_eq_zero_of_forall_eval_line_eq_zero p hp_deg w v
        (fun t => h_vanish (w + t • v) (hw t))

/-- If `K` is a Kakeya set in `F^n`, then `|K| \ge \binom{|F|+n-1}{n}`. For the alternative
  statement `|K| \ge \frac{|F|^n}{n!}`, see `theorem_35_3'`.  -/
theorem theorem_35_3 {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]
    {K : Set (Fin n → F)} (hK : IsKakeyaSet F K) :
    (Fintype.card F + n - 1).choose n ≤ (@Set.toFinset _ K (Fintype.ofFinite ↑K)).card := by
      revert hK;
      contrapose!;
      intro hK_card hK_kakeya
      obtain ⟨p, hp_deg, hp_nonzero, hp_vanish⟩ :
        ∃ p : MvPolynomial (Fin n) F, p.totalDegree < Fintype.card F ∧ p ≠ 0 ∧
        ∀ x ∈ K, MvPolynomial.eval x p = 0 := by
        convert lemma_35_2 ( hE := ?_ ) using 1;
        rotate_left;
        (expose_names; exact inst_1);
        exact Fintype.card F - 1;
        exact K;
        · rwa [ add_comm, Nat.add_sub_assoc
            ( Nat.one_le_iff_ne_zero.mpr ( Fintype.card_ne_zero ) ) ] at hK_card;
        · ext; simp [MvPolynomial.mem_restrictTotalDegree];
          exact fun _ _ => ⟨ fun h => Nat.le_sub_one_of_lt h,
            fun h => lt_of_le_of_lt h ( Nat.pred_lt ( ne_bot_of_gt ( Fintype.card_pos ) ) ) ⟩;
      have h_homogeneous_nonzero : MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 := by
        simp_all +decide [ MvPolynomial.ext_iff ];
        simp_all +decide [ MvPolynomial.coeff_homogeneousComponent ];
        have h_homogeneous_nonzero : ∃ x ∈ p.support, x.degree = p.totalDegree := by
          have h_homogeneous_nonzero : ∃ x ∈ p.support, ∀ y ∈ p.support, y.degree ≤ x.degree := by
            apply_rules [ Finset.exists_max_image ];
            exact ⟨ hp_nonzero.choose, MvPolynomial.mem_support_iff.mpr hp_nonzero.choose_spec ⟩;
          obtain ⟨ x, hx₁, hx₂ ⟩ := h_homogeneous_nonzero;
          refine' ⟨ x, hx₁, le_antisymm _ _ ⟩;
          · exact Finset.le_sup ( f := fun s => s.degree ) hx₁;
          · exact Finset.sup_le fun y hy => hx₂ y hy;
        aesop;
      have h_homogeneous_vanish : ∀ v : Fin n → F, MvPolynomial.eval v
        (MvPolynomial.homogeneousComponent p.totalDegree p) = 0 := by
        apply_rules [ eval_homogeneousComponent_eq_zero_of_vanishes_on_Kakeya];
        exact NeZero.pos n;
      have h_homogeneous_deg : (MvPolynomial.homogeneousComponent p.totalDegree p).totalDegree =
        p.totalDegree := by
        refine' le_antisymm _ _;
        · simp +decide [ MvPolynomial.totalDegree ];
          simp +decide [ MvPolynomial.coeff_homogeneousComponent ];
          exact fun s hs hs' => Finset.le_sup ( f := fun s => s.sum fun x e => e )
            ( Finsupp.mem_support_iff.mpr hs' );
        · obtain ⟨s, hs⟩ : ∃ s : Fin n →₀ ℕ, s ∈ p.support ∧ s.sum (fun _ k => k) =
            p.totalDegree := by
            have h_max_deg : ∃ s ∈ p.support, ∀ t ∈ p.support, t.sum (fun _ k => k) ≤
              s.sum (fun _ k => k) := by
              apply_rules [ Finset.exists_max_image ];
              exact Finset.nonempty_of_ne_empty ( by aesop );
            exact ⟨ h_max_deg.choose, h_max_deg.choose_spec.1,
              le_antisymm ( Finset.le_sup ( f := fun s => s.sum fun _ k => k )
              h_max_deg.choose_spec.1 ) ( Finset.sup_le fun t ht => h_max_deg.choose_spec.2 t ht )⟩;
          refine' le_trans _ ( Finset.le_sup <| show s ∈ ( MvPolynomial.homogeneousComponent
            p.totalDegree p |> MvPolynomial.support ) from _ );
          · rw [ hs.2 ];
          · simp_all +decide [ MvPolynomial.coeff_homogeneousComponent ];
            convert hs.2 using 1;
      have := lemma_35_1 h_homogeneous_nonzero;
      rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
      exact this.not_gt ( mul_lt_mul_of_pos_right hp_deg ( pow_pos ( Fintype.card_pos ) _ ) )

/-- The second inequality in the statement of the finite Kakeya problem, phrased for general
  natural numbers `n ≠ 0` and `k`. -/
lemma le_binom_sum (k n : ℕ) [NeZero n] : k^n ≤ (k + n - 1).choose n * Nat.factorial n := by
  have h_binom : Nat.choose (k + n - 1) n * Nat.factorial n =
    ∏ i ∈ Finset.range n, (k + n - 1 - i) := by
    rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ Nat.descFactorial_eq_prod_range ];
  exact h_binom ▸ le_trans ( by norm_num ) ( Finset.prod_le_prod' fun i hi =>
    show k + n - 1 - i ≥ k from Nat.le_sub_of_add_le
    ( by
      linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel
        ( show 1 ≤ k + n from by linarith [ NeZero.pos n ] ) ] ) )

/-- If `K` is a Kakeya set in `F^n`, then  `|K| \ge \frac{|F|^n}{n!}`.  -/
theorem theorem_35_3' {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]
    {K : Set (Fin n → F)} (hK : IsKakeyaSet F K) :
    (Fintype.card F)^n ≤ (@Set.toFinset _ K (Fintype.ofFinite ↑K)).card * Nat.factorial n :=
      (le_binom_sum (Fintype.card F) n).trans ( Nat.mul_le_mul_right _ ( theorem_35_3 hK ) )
