import Mathlib

/-!
# Sperner's Lemma and Brouwer Fixed Point Theorem via Sperner

Auxiliary machinery for Chapter 28: Sperner's lemma (combinatorial),
the Sperner-to-Brouwer bridge via subdivision of the standard 2-simplex.
-/


namespace chapter28

/-- An abstract simplicial 2-complex: a collection of triangles (3-element subsets). -/
structure Triangulation (m : ℕ) where
  /-- The collection of triangles (3-element subsets of vertices). -/
  triangles : Finset (Finset (Fin m))
  triangle_card : ∀ t ∈ triangles, t.card = 3

/-- A triangle is rainbow (tricolored) under coloring `c` if its vertices receive
    all three colors {0, 1, 2}. -/
def isRainbow {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Prop :=
  t.image c = {0, 1, 2}

instance {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Decidable (isRainbow c t) :=
  inferInstanceAs (Decidable (t.image c = {0, 1, 2}))

/-- Auxiliary parity lemma: if `f` maps each element of a finset to `{0, 1, 2}`,
    and the sum `∑ f` is odd, then the number of elements with `f = 1` is odd.
    This is the combinatorial core of Sperner's lemma (the double-counting/parity argument). -/
private theorem odd_card_filter_eq_one {α : Type*} {S : Finset α} {f : α → ℕ}
    (hf : ∀ s ∈ S, f s = 0 ∨ f s = 1 ∨ f s = 2)
    (hsum : Odd (∑ s ∈ S, f s)) :
    Odd (S.filter (fun s => f s = 1)).card := by
  -- Show: ∑ f = #{f=1} + 2 * #{f=2}, so #{f=1} has same parity as ∑ f.
  set S₁ := S.filter (fun s => f s = 1)
  set S₂ := S.filter (fun s => f s = 2)
  suffices hkey : ∑ s ∈ S, f s = S₁.card + 2 * S₂.card by
    rw [hkey] at hsum; obtain ⟨k, hk⟩ := hsum; rw [Nat.odd_iff]; omega
  -- Decompose: f s = 𝟙_{f=1}(s) + 2·𝟙_{f=2}(s)
  have hind : ∀ s ∈ S, f s = (if f s = 1 then 1 else 0) + 2 * (if f s = 2 then 1 else 0) := by
    intro s hs; rcases hf s hs with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl hind, Finset.sum_add_distrib]
  simp only [Finset.sum_boole]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp; rfl

/-- **Sperner's Lemma** (combinatorial, odd-count version).

    Given a triangulation with a 3-coloring and a "12-edge count" function `count12`
    that assigns to each triangle the number of edges connecting a vertex of color 1
    to a vertex of color 2, if:
    1. Rainbow triangles are exactly those with an odd 12-edge count (`count12 = 1`),
    2. Each triangle has 0, 1, or 2 such edges,
    3. The total sum of 12-edge counts is odd (from the Sperner boundary condition
       and the double-counting argument: each interior 12-edge is shared by exactly
       two triangles, so contributes evenly, while boundary 12-edges contribute once),
    then the number of rainbow triangles is odd. -/
theorem sperner_lemma {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    Odd (T.triangles.filter (isRainbow c)).card := by
  have hfilt : T.triangles.filter (isRainbow c) =
      T.triangles.filter (fun t => count12 t = 1) := by
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hr⟩; exact ⟨ht, (h_rainbow_iff t ht).mp hr⟩
    · rintro ⟨ht, h1⟩; exact ⟨ht, (h_rainbow_iff t ht).mpr h1⟩
  rw [hfilt]
  exact odd_card_filter_eq_one h_range h_odd_sum

/-- Corollary: at least one rainbow triangle exists. -/
theorem sperner_lemma_exists {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    ∃ t ∈ T.triangles, isRainbow c t := by
  have hodd := sperner_lemma T c count12 h_rainbow_iff h_range h_odd_sum
  rw [Nat.odd_iff] at hodd
  have hne : (T.triangles.filter (isRainbow c)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hodd
  exact let ⟨t, ht⟩ := hne; ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-! ## Sperner → Brouwer bridge: infrastructure and proof outline

The book proof (pp.204–205) deduces Brouwer's fixed-point theorem from Sperner's lemma
via the standard 2-simplex Δ² = conv{e₁,e₂,e₃}.  We set up the key definitions and
state the lemmas needed to connect the combinatorial `sperner_lemma` above to the
analytic fixed-point conclusion.

### Proof outline (Proofs from THE BOOK, Chapter 28)

1. **Standard 2-simplex.** Δ² = {(x₁,x₂,x₃) ∈ ℝ³ | xᵢ ≥ 0, x₁+x₂+x₃ = 1}.
2. **Regular triangulation.** Subdivide Δ² into k² small triangles with vertices
   of the form (a/k, b/k, c/k), a+b+c = k.
3. **Sperner coloring.** For a continuous f : Δ² → Δ², color vertex v with
   the smallest i such that f(v)ᵢ < vᵢ.  This is well-defined because
   ∑ f(v)ᵢ = 1 = ∑ vᵢ so f(v) ≠ v implies some coordinate decreases.
4. **Boundary condition.** If v lies on the face opposite eⱼ (i.e. vⱼ = 0),
   then color(v) ≠ j.  This gives a proper Sperner coloring.
5. **Rainbow triangles.** By `sperner_lemma`, each T_k has a rainbow triangle.
6. **Compactness.** Extract a convergent subsequence of rainbow triangle vertices.
7. **Fixed point.** At the limit, f(v)ᵢ ≤ vᵢ for all i, and ∑ = 1 forces equality.
-/

/-- A point in the standard 2-simplex: nonnegative coordinates summing to 1. -/
def stdSimplex2 : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The Sperner coloring for a continuous self-map of Δ².  Given v ∈ Δ² and
    f : Δ² → Δ², color(v) = min {i | f(v)ᵢ < vᵢ}.  Well-defined when f(v) ≠ v
    and ∑ f(v)ᵢ = ∑ vᵢ = 1. When f(v) = v, we default to 0. -/
noncomputable def spernerColor (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : Fin 3 :=
  if h : ∃ i : Fin 3, f v i < v i then h.choose else 0

/-! ### Brouwer's fixed-point theorem on the standard 2-simplex via Sperner's lemma

The book proof (pp. 204–205) deduces Brouwer from Sperner via:
1. For each k, subdivide Δ² into small triangles, apply Sperner coloring, get a rainbow triangle
2. Extract convergent subsequence (compactness of Δ²)
3. At the limit, f(x*) = x*

**Gap 1 (Geometric Sperner):** Constructing the regular k-subdivision as an instance of
`Triangulation` and verifying the boundary parity condition is a major formalization effort.
We axiomatize the infrastructure lemmas (triangulation construction, boundary parity,
vertex extraction) below; `sperner_coloring_rainbow_triangles` is proved modulo these.

**Gaps 2–3 (Compactness + Limit):** Fully proved below.
-/

/-- The standard 2-simplex equals Mathlib's `stdSimplex`. -/
private theorem stdSimplex2_eq : stdSimplex2 = stdSimplex ℝ (Fin 3) := by
  ext x; simp only [stdSimplex2, stdSimplex, Set.mem_setOf_eq]

/-- The standard 2-simplex is compact. -/
private theorem stdSimplex2_isCompact : IsCompact stdSimplex2 := by
  rw [stdSimplex2_eq]; exact isCompact_stdSimplex ℝ (Fin 3)

/-- The Sperner coloring is well-defined: if v ∈ Δ² and f(v) ≠ v with f(v) ∈ Δ²,
    then some coordinate strictly decreases. -/
private theorem spernerColor_exists {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ} (hv : v ∈ stdSimplex2) (hfv : f v ∈ stdSimplex2)
    (hne : f v ≠ v) : ∃ i : Fin 3, f v i < v i := by
  by_contra h; push_neg at h
  have hsum_v := hv.2; have hsum_fv := hfv.2
  have : ∀ i, f v i = v i := by
    intro i
    have hle_sum : ∑ j, v j ≤ ∑ j, f v j := Finset.sum_le_sum (fun j _ => h j)
    rw [hsum_v, hsum_fv] at hle_sum
    have hge : f v i ≤ v i := by
      by_contra hlt; push_neg at hlt
      have : ∑ j, v j < ∑ j, f v j :=
        Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ _, hlt⟩
      linarith
    exact le_antisymm hge (h i)
  exact hne (funext this)

/-- The Sperner coloring satisfies the boundary condition: if vⱼ = 0 and v ∈ Δ²
    and f(v) ∈ Δ², then color(v) ≠ j (since f(v)ⱼ ≥ 0 = vⱼ). -/
private theorem spernerColor_boundary {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ} (hv : v ∈ stdSimplex2) (hfv : f v ∈ stdSimplex2) {j : Fin 3} (hvj : v j = 0)
    (hne : f v ≠ v) : spernerColor f v ≠ j := by
  have hex := spernerColor_exists hv hfv hne
  intro heq
  unfold spernerColor at heq; rw [dif_pos hex] at heq
  have hchoose := hex.choose_spec
  rw [heq] at hchoose
  rw [hvj] at hchoose; linarith [hfv.1 j]

/-! ### Regular k-subdivision of Δ² and geometric Sperner infrastructure

We encode the regular k-subdivision of the standard 2-simplex and connect it
to `sperner_lemma_exists`. The subdivision has vertices (a/k, b/k, c/k) with
a + b + c = k, and small triangles of two types ("up" and "down").

The key steps are:
1. Define the vertex set and its encoding as `Fin m`
2. Define the triangulation
3. Define the 12-edge count and verify boundary parity
4. Extract geometric consequences from the combinatorial rainbow triangle
-/

/-- Number of vertices in the k-th regular subdivision: (k+1)(k+2)/2. -/
private def subdivVertCount (k : ℕ) : ℕ := (k + 1) * (k + 2) / 2

/-- A vertex of the k-th regular subdivision is a triple (a,b,c) with a+b+c = k. -/
private def SubdivVert (k : ℕ) : Type :=
  { abc : Fin 3 → ℕ // ∑ i, abc i = k }

private instance subdivVertFintype (k : ℕ) : Fintype (SubdivVert k) :=
  Fintype.subtype (Finset.Nat.antidiagonalTuple 3 k) fun x => by
    simp [Finset.Nat.mem_antidiagonalTuple]

private instance subdivVertDecEq (k : ℕ) : DecidableEq (SubdivVert k) :=
  inferInstanceAs (DecidableEq { abc : Fin 3 → ℕ // ∑ i, abc i = k })

/-- The coordinate map: send a subdivision vertex to its barycentric point in Δ². -/
private noncomputable def subdivCoord (k : ℕ) (hk : 0 < k) (v : SubdivVert k) : Fin 3 → ℝ :=
  fun i => (v.1 i : ℝ) / (k : ℝ)

private theorem subdivCoord_mem (k : ℕ) (hk : 0 < k) (v : SubdivVert k) :
    subdivCoord k hk v ∈ stdSimplex2 := by
  constructor
  · intro i; apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [subdivCoord, ← Finset.sum_div]
    rw [show (∑ i : Fin 3, (v.1 i : ℝ)) = (∑ i : Fin 3, v.1 i : ℕ) from by push_cast; rfl]
    rw [v.2]; field_simp

/-- Distance between adjacent subdivision vertices is at most √2/k.
    Two vertices are adjacent if they differ by at most 1 in each coordinate. -/
private theorem subdivCoord_dist (k : ℕ) (hk : 0 < k) (v w : SubdivVert k)
    (hadj : ∀ i, (v.1 i : ℤ) - (w.1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1) :
    dist (subdivCoord k hk v) (subdivCoord k hk w) ≤ Real.sqrt 2 / k := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [dist_pi_le_iff (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hk'))]
  intro i
  rw [Real.dist_eq, subdivCoord, subdivCoord, div_sub_div_same]
  rw [abs_div, abs_of_nonneg (le_of_lt hk')]
  apply div_le_div_of_nonneg_right _ (le_of_lt hk')
  have hi := hadj i
  simp only [Set.mem_Icc] at hi
  calc |(v.1 i : ℝ) - (w.1 i : ℝ)|
      ≤ 1 := by
        rw [show (v.1 i : ℝ) - (w.1 i : ℝ) = ((v.1 i : ℤ) - (w.1 i : ℤ) : ℤ) from by push_cast; ring]
        rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) from by norm_cast]
        exact_mod_cast abs_le.mpr ⟨hi.1, hi.2⟩
    _ ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)

/-- Data bundle for a subdivision triangulation with adjacency. -/
private structure SubdivData (k : ℕ) where
  m : ℕ
  T : Triangulation m
  decode : Fin m → SubdivVert k
  adj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
    ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1

/-- The regular k-subdivision as a `Triangulation` with adjacency proof.
    The key properties are that:
    - Each triangle has 3 vertices from `SubdivVert k` (encoded as `Fin m`)
    - The triangulation covers Δ²
    - Any two vertices in the same triangle differ by ≤ 1 in each coordinate -/
private noncomputable def subdivTriangulation (k : ℕ) (_hk : 0 < k) :
    SubdivData k := by
  classical
  let m := Fintype.card (SubdivVert k)
  let eqv := Fintype.equivFin (SubdivVert k)
  let encode : SubdivVert k → Fin m := eqv
  let decode : Fin m → SubdivVert k := eqv.symm
  -- Helper to make a SubdivVert from (a, b) with a + b ≤ k
  let mkVert : ∀ (a b : ℕ), a + b ≤ k → SubdivVert k := fun a b h =>
    ⟨![a, b, k - a - b], by simp [Fin.sum_univ_three]; omega⟩
  -- Define triangles as a subset of Finset.powerset (Finset.univ : Finset (Fin m))
  -- filtered by the triangulation predicate
  -- An up-triangle has vertices (i,j), (i+1,j), (i,j+1) with i+j < k
  -- A down-triangle has vertices (i+1,j), (i,j+1), (i+1,j+1) with i+j+1 < k
  -- We define the predicate on triples of SubdivVert k
  let isUpTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j < k),
      v0 = mkVert i j (by omega) ∧
      v1 = mkVert (i+1) j (by omega) ∧
      v2 = mkVert i (j+1) (by omega)
  let isDownTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j + 1 < k),
      v0 = mkVert (i+1) j (by omega) ∧
      v1 = mkVert i (j+1) (by omega) ∧
      v2 = mkVert (i+1) (j+1) (by omega)
  -- Build the triangles as a finset
  let allTris : Finset (Finset (Fin m)) :=
    Finset.univ.biUnion fun (v0 : SubdivVert k) =>
      Finset.univ.biUnion fun (v1 : SubdivVert k) =>
        Finset.univ.biUnion fun (v2 : SubdivVert k) =>
          if (∃ (i j : ℕ) (_ : i + j < k),
                v0 = mkVert i j (by omega) ∧
                v1 = mkVert (i+1) j (by omega) ∧
                v2 = mkVert i (j+1) (by omega)) ∨
             (∃ (i j : ℕ) (_ : i + j + 1 < k),
                v0 = mkVert (i+1) j (by omega) ∧
                v1 = mkVert i (j+1) (by omega) ∧
                v2 = mkVert (i+1) (j+1) (by omega))
          then {({encode v0, encode v1, encode v2} : Finset (Fin m))}
          else ∅
  -- Helper: mkVert produces distinct SubdivVert's when first coords differ
  have mkVert_coord0 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 0 = a := by
    intro a b h; simp [mkVert, Matrix.cons_val_zero]
  have mkVert_coord1 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 1 = b := by
    intro a b h; simp [mkVert, Matrix.cons_val_one, Matrix.head_cons]
  have hcard : ∀ t ∈ allTris, t.card = 3 := by
    intro t ht
    simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
    obtain ⟨v0, v1, v2, hcond⟩ := ht
    split_ifs at hcond with htri
    · simp only [Finset.mem_singleton] at hcond
      subst hcond
      have hinj : Function.Injective encode := eqv.injective
      rcases htri with ⟨i, j, hij, rfl, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl, rfl⟩
      · -- Up triangle: (i,j), (i+1,j), (i,j+1)
        have h01 : mkVert i j (by omega) ≠ mkVert (i+1) j (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert i j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert i j (by omega)) ≠ encode (mkVert (i+1) j (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert i j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg; exact ⟨he01, he02⟩
      · -- Down triangle: (i+1,j), (i,j+1), (i+1,j+1)
        have h01 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert (i+1) j (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert i (j+1) (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert i (j+1) (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg; exact ⟨he01, he02⟩
    · simp at hcond
  refine ⟨m, ⟨allTris, hcard⟩, decode, ?_⟩
  -- Adjacency: any two vertices in the same triangle differ by ≤ 1 in each coordinate
  -- This follows from the construction: up-triangles have vertices (i,j),(i+1,j),(i,j+1)
  -- and down-triangles have vertices (i+1,j),(i,j+1),(i+1,j+1), all differing by ≤ 1.
  intro t ht a ha b hb idx
  simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
  obtain ⟨v0, v1, v2, hcond⟩ := ht
  split_ifs at hcond with htri
  · simp only [Finset.mem_singleton] at hcond
    have hmem : a ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ ha
    have hmem' : b ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    have hdec : ∀ x, (x = encode v0 ∨ x = encode v1 ∨ x = encode v2) →
        (decode x = v0 ∨ decode x = v1 ∨ decode x = v2) := by
      intro x hx; rcases hx with rfl | rfl | rfl <;>
        simp [decode, encode, Equiv.symm_apply_apply]
    have hda := hdec a hmem
    have hdb := hdec b hmem'
    rcases htri with ⟨ii, jj, hij, rfl, rfl, rfl⟩ | ⟨ii, jj, hij, rfl, rfl, rfl⟩
    · -- Up triangle: mkVert ii jj, mkVert (ii+1) jj, mkVert ii (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega)
    · -- Down triangle: mkVert (ii+1) jj, mkVert ii (jj+1), mkVert (ii+1) (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega)
  · simp at hcond

/-! ### Boundary parity for Sperner coloring

The boundary parity condition for the Sperner coloring on the k-subdivision.
The sum of 12-edge counts over all triangles is odd.

**Proof sketch:**
Define `count12 t` = number of {u,v} pairs in triangle t with {col u, col v} = {1,2}.
- `h_rainbow_iff`: A triangle with colors {0,1,2} has exactly one 1-2 pair → count12 = 1.
- `h_range`: For a 3-element set, count12 ∈ {0,1,2}.
- `h_odd_sum`: By double counting, ∑ count12 = ∑_{12-edges e} (triangles containing e).
  Interior edges contribute 2 (even), boundary edges contribute 1.
  Boundary 12-edges exist only on the e₁e₂ face (x₀=0), since:
    • e₀e₁ face has colors ∈ {0,1} (no color-2 vertex)
    • e₀e₂ face has colors ∈ {0,2} (no color-1 vertex)
  On the e₁e₂ face, vertices go from e₂ (color 2) to e₁ (color 1) through k edges.
  The number of 1↔2 color changes is odd (parity argument: starts at 2, ends at 1).
  Therefore ∑ count12 ≡ (boundary 12-edges) ≡ 1 (mod 2). -/
/-- A binary sequence starting at `false` and ending at `true` has an odd number
    of transitions. -/
private lemma transitions_parity_nat : ∀ (m : ℕ) (f : Fin (m + 1) → Bool),
    (Finset.univ.filter (fun i : Fin m => f i.castSucc ≠ f i.succ)).card % 2 =
    (if f 0 = f ⟨m, by omega⟩ then 0 else 1) := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    have hih := ih (f ∘ Fin.castSucc)
    simp only [Function.comp, Fin.castSucc_zero, Fin.castSucc_succ] at hih
    simp only [Fin.castSucc_mk] at hih
    have card_decomp :
        (Finset.univ.filter (fun i : Fin (m + 1) => f i.castSucc ≠ f i.succ)).card =
        (Finset.univ.filter (fun i : Fin m => f i.castSucc.castSucc ≠ f i.castSucc.succ)).card +
        (if f (Fin.last m).castSucc ≠ f (Fin.last m).succ then 1 else 0) := by
      have h1 : (Finset.univ.filter (fun i : Fin (m + 1) => f i.castSucc ≠ f i.succ)).card =
          ∑ i : Fin (m + 1), (if f i.castSucc ≠ f i.succ then 1 else 0) :=
        Finset.card_filter _ _
      have h2 : ∑ i : Fin (m + 1), (if f i.castSucc ≠ f i.succ then 1 else 0) =
          (∑ i : Fin m, if f i.castSucc.castSucc ≠ f i.castSucc.succ then 1 else 0) +
          (if f (Fin.last m).castSucc ≠ f (Fin.last m).succ then 1 else 0) :=
        Fin.sum_univ_castSucc _
      have h3 : (∑ i : Fin m, if f i.castSucc.castSucc ≠ f i.castSucc.succ then 1 else 0) =
          (Finset.univ.filter (fun i : Fin m => f i.castSucc.castSucc ≠ f i.castSucc.succ)).card :=
        (Finset.card_filter _ _).symm
      linarith
    rw [card_decomp]
    have hlast_cs : f (Fin.last m).castSucc = f ⟨m, by omega⟩ :=
      congrArg f (by simp [Fin.last, Fin.castSucc])
    have hlast_succ : f (Fin.last m).succ = f ⟨m + 1, by omega⟩ :=
      congrArg f (by simp [Fin.last, Fin.val_succ])
    rw [hlast_cs, hlast_succ]
    rcases Bool.eq_false_or_eq_true (f 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (f (⟨m, by omega⟩ : Fin (m + 2))) with hm | hm <;>
    rcases Bool.eq_false_or_eq_true (f (⟨m + 1, by omega⟩ : Fin (m + 2))) with hm1 | hm1 <;>
    simp only [h0, hm, hm1, ne_eq, not_true, not_false_eq_true, ite_true, ite_false,
        Bool.false_eq_true, Bool.true_eq_false, Nat.add_zero] at hih ⊢ <;>
    omega

private lemma odd_transitions (n : ℕ) (s : Fin (n + 1) → Bool)
    (h0 : s 0 = false) (hlast : s ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = true) :
    Odd (Finset.card (Finset.univ.filter (fun (i : Fin n) =>
      s i.castSucc ≠ s i.succ))) := by
  rw [Nat.odd_iff]
  have h := transitions_parity_nat n s
  rw [h0, hlast] at h
  simpa using h

private theorem subdivSperner_odd_sum
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (hne : ∀ x ∈ stdSimplex2, f x ≠ x)
    (k : ℕ) (hk : 0 < k)
    (m : ℕ) (T : Triangulation m) (decode : Fin m → SubdivVert k)
    (hadj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
      ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1)
    (col : Fin m → Fin 3)
    (hcol_boundary : ∀ v j, (decode v).1 j = 0 → col v ≠ j)
    (h_odd_sum_hyp : Odd (∑ t ∈ T.triangles,
      (t.filter (fun v => col v = 1)).card * (t.filter (fun v => col v = 2)).card)) :
    ∃ count12 : Finset (Fin m) → ℕ,
      (∀ t ∈ T.triangles, isRainbow col t ↔ count12 t = 1) ∧
      (∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2) ∧
      Odd (∑ t ∈ T.triangles, count12 t) := by
  -- Define count12 t = (# vertices colored 1) * (# vertices colored 2) in t
  let count12 : Finset (Fin m) → ℕ := fun t =>
    (t.filter (fun v => col v = 1)).card * (t.filter (fun v => col v = 2)).card
  refine ⟨count12, ?_, ?_, ?_⟩
  · -- h_rainbow_iff: rainbow ↔ count12 = 1
    intro t ht
    simp only [isRainbow, count12]
    have hcard := T.triangle_card t ht
    have d01 : Disjoint (t.filter (fun v => col v = 0)) (t.filter (fun v => col v = 1)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
    have d02 : Disjoint (t.filter (fun v => col v = 0)) (t.filter (fun v => col v = 2)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
    have d12 : Disjoint (t.filter (fun v => col v = 1)) (t.filter (fun v => col v = 2)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
    have hunion : t.filter (fun v => col v = 0) ∪ t.filter (fun v => col v = 1) ∪ t.filter (fun v => col v = 2) = t := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
      · intro hx; match col x, (col x).isLt with
        | ⟨0, _⟩, _ => left; left; exact ⟨hx, rfl⟩
        | ⟨1, _⟩, _ => left; right; exact ⟨hx, rfl⟩
        | ⟨2, _⟩, _ => right; exact ⟨hx, rfl⟩
    have hpart : (t.filter (fun v => col v = 0)).card + (t.filter (fun v => col v = 1)).card + (t.filter (fun v => col v = 2)).card = 3 := by
      calc _ = (t.filter (fun v => col v = 0) ∪ t.filter (fun v => col v = 1)).card + (t.filter (fun v => col v = 2)).card := by
            rw [Finset.card_union_of_disjoint d01]
        _ = (t.filter (fun v => col v = 0) ∪ t.filter (fun v => col v = 1) ∪ t.filter (fun v => col v = 2)).card := by
            rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d02, d12⟩)]
        _ = t.card := by rw [hunion]
        _ = 3 := hcard
    constructor
    · -- rainbow → count12 = 1
      intro h
      have h0 : (0 : Fin 3) ∈ t.image col := by rw [h]; simp
      have h1 : (1 : Fin 3) ∈ t.image col := by rw [h]; simp
      have h2 : (2 : Fin 3) ∈ t.image col := by rw [h]; simp
      rw [Finset.mem_image] at h0 h1 h2
      obtain ⟨_, ha, hca⟩ := h0; obtain ⟨_, hb, hcb⟩ := h1; obtain ⟨_, hc, hcc⟩ := h2
      have : 1 ≤ (t.filter (fun v => col v = 0)).card := Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨ha, hca⟩⟩
      have : 1 ≤ (t.filter (fun v => col v = 1)).card := Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hb, hcb⟩⟩
      have : 1 ≤ (t.filter (fun v => col v = 2)).card := Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hc, hcc⟩⟩
      nlinarith
    · -- count12 = 1 → rainbow
      intro h
      have hn1 : (t.filter (fun v => col v = 1)).card = 1 := Nat.eq_one_of_mul_eq_one_right h
      have hn2 : (t.filter (fun v => col v = 2)).card = 1 := Nat.eq_one_of_mul_eq_one_left h
      have hn0 : (t.filter (fun v => col v = 0)).card = 1 := by omega
      have : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
      rw [this, Finset.eq_univ_iff_forall]
      intro x; rw [Finset.mem_image]
      fin_cases x
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (t.filter (fun v => col v = 0)).card)
        exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (t.filter (fun v => col v = 1)).card)
        exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (t.filter (fun v => col v = 2)).card)
        exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · -- h_range: count12 ∈ {0, 1, 2}
    intro t ht
    simp only [count12]
    have hcard := T.triangle_card t ht
    have d12 : Disjoint (t.filter (fun v => col v = 1)) (t.filter (fun v => col v = 2)) := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
    have hsum : (t.filter (fun v => col v = 1)).card + (t.filter (fun v => col v = 2)).card ≤ 3 := by
      calc _ = (t.filter (fun v => col v = 1) ∪ t.filter (fun v => col v = 2)).card :=
            (Finset.card_union_of_disjoint d12).symm
        _ ≤ t.card := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
        _ = 3 := hcard
    have ha : (t.filter (fun v => col v = 1)).card ≤ 3 := by omega
    have hb : (t.filter (fun v => col v = 2)).card ≤ 3 := by omega
    interval_cases (t.filter (fun v => col v = 1)).card <;> interval_cases (t.filter (fun v => col v = 2)).card <;> omega
  · -- h_odd_sum: provided as hypothesis
    exact h_odd_sum_hyp

/-- From a rainbow triangle in the subdivision, extract three vertices with the
    desired geometric properties. -/
private theorem rainbow_triangle_gives_vertices
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (hne : ∀ x ∈ stdSimplex2, f x ≠ x)
    (k : ℕ) (hk : 0 < k) (m : ℕ) (T : Triangulation m) (decode : Fin m → SubdivVert k)
    (col : Fin m → Fin 3) (t : Finset (Fin m)) (ht : t ∈ T.triangles)
    (hcard : t.card = 3) (hrainbow : isRainbow col t)
    (hcol_def : ∀ v, col v = spernerColor f (subdivCoord k hk (decode v)))
    (hadj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
      ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1) :
    ∃ v : Fin 3 → (Fin 3 → ℝ),
      (∀ i, v i ∈ stdSimplex2) ∧
      (∀ i, f (v i) i < (v i) i) ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 2 / k) := by
  -- Extract the 3 vertices with distinct colors from the rainbow triangle
  rw [isRainbow] at hrainbow
  -- t has 3 elements, image under col is {0,1,2}
  -- We need to find vertices with each color
  have h0 : (0 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  have h1 : (1 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  have h2 : (2 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  rw [Finset.mem_image] at h0 h1 h2
  obtain ⟨a, ha, hca⟩ := h0
  obtain ⟨b, hb, hcb⟩ := h1
  obtain ⟨c, hc, hcc⟩ := h2
  -- Define v i = subdivCoord of the vertex with color i
  let vert : Fin 3 → Fin m := ![a, b, c]
  refine ⟨fun i => subdivCoord k hk (decode (vert i)), ?_, ?_, ?_⟩
  · -- v i ∈ stdSimplex2
    intro i; exact subdivCoord_mem k hk (decode (vert i))
  · -- f (v i) i < (v i) i
    intro i
    have hcol_i : col (vert i) = i := by
      fin_cases i <;> simp only [vert, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> assumption
    rw [hcol_def] at hcol_i
    unfold spernerColor at hcol_i
    split_ifs at hcol_i with hex
    · have := hex.choose_spec; rw [hcol_i] at this; exact this
    · -- ¬∃ j, f v j < v j means f(v) ≥ v componentwise, and ∑ = 1 forces f(v) = v.
      -- But hne says f(v) ≠ v, contradiction.
      push_neg at hex
      have hv_mem := subdivCoord_mem k hk (decode (vert i))
      have hfv_mem := hfS _ hv_mem
      have heq : f (subdivCoord k hk (decode (vert i))) = subdivCoord k hk (decode (vert i)) := by
        ext j
        exact le_antisymm (by
          by_contra hlt; push_neg at hlt
          have : ∑ l, f (subdivCoord k hk (decode (vert i))) l >
                 ∑ l, subdivCoord k hk (decode (vert i)) l :=
            Finset.sum_lt_sum (fun l _ => hex l)
              ⟨j, Finset.mem_univ _, hlt⟩
          linarith [hfv_mem.2, hv_mem.2]) (hex j)
      exact absurd heq (hne _ hv_mem)
  · -- Distance bound: vertices in the same triangle are adjacent
    -- This requires knowledge of the triangulation structure (adjacency).
    -- Gap: we need that decode maps triangle vertices to adjacent SubdivVert's
    -- (differing by ≤1 in each coordinate). This is a property of the construction
    -- in subdivTriangulation which we axiomatize here.
    intro i j
    apply subdivCoord_dist
    intro idx
    have hvi : vert i ∈ t := by
      fin_cases i <;> simp [vert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        assumption
    have hvj : vert j ∈ t := by
      fin_cases j <;> simp [vert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        assumption
    exact hadj t ht (vert i) hvi (vert j) hvj idx

/-- **Geometric Sperner:** For each k ≥ 1, the Sperner coloring of the k-th regular
    subdivision of Δ² applied to a continuous f : Δ² → Δ² yields three points
    v₀, v₁, v₂ ∈ Δ² forming a rainbow triangle. -/
private theorem sperner_coloring_rainbow_triangles
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (_hfc : Continuous f) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (hne : ∀ x ∈ stdSimplex2, f x ≠ x)
    (k : ℕ) (hk : 0 < k) :
    ∃ v : Fin 3 → (Fin 3 → ℝ),
      (∀ i, v i ∈ stdSimplex2) ∧
      (∀ i, f (v i) i < (v i) i) ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 2 / k) := by
  obtain ⟨m, T, decode, hadj⟩ := subdivTriangulation k hk
  set col : Fin m → Fin 3 := fun v => spernerColor f (subdivCoord k hk (decode v))
  have hcol_boundary : ∀ v j, (decode v).1 j = 0 → col v ≠ j := by
    intro v j hvj
    have hv_mem := subdivCoord_mem k hk (decode v)
    have hvj_coord : subdivCoord k hk (decode v) j = 0 := by
      simp [subdivCoord, hvj]
    exact spernerColor_boundary hv_mem (hfS _ hv_mem) hvj_coord (hne _ hv_mem)
  -- Prove the odd sum for the concrete triangulation
  -- Key idea: ∑_t n₁(t)·n₂(t) counts ordered (color-1, color-2) pairs within triangles.
  -- By double counting mod 2, this equals the number of boundary 12-edges (mod 2).
  -- Interior edges have codegree 2 (even), boundary edges have codegree 1 (odd).
  -- The only face with both colors 1 and 2 is the e₁e₂ face (where coord 0 = 0).
  -- On that face, odd_transitions gives an odd number of 1↔2 transitions.
  have h_odd_sum_concrete : Odd (∑ t ∈ T.triangles,
      (t.filter (fun v => col v = 1)).card * (t.filter (fun v => col v = 2)).card) := by
    sorry
    /-
    ## Edge-triangle incidence parity (sorry analysis)

    ### What this sorry needs to prove

    `Odd (∑ t ∈ T.triangles, n₁(t) * n₂(t))`
    where n₁(t) = |{v ∈ t | col v = 1}|, n₂(t) = |{v ∈ t | col v = 2}|.

    This corresponds directly to the tex proof of Sperner's lemma (§ Sperner's Lemma
    in chapter28.tex), specifically the "partial dual graph" argument using
    the handshaking lemma (equation (4)).

    ### Mathematical proof (correct, follows tex)

    1. **Sum-swap (double counting).**
       ∑_t n₁(t)·n₂(t) = ∑_{(u,v): col u=1, col v=2} codeg(u,v)
       where codeg(u,v) = |{t ∈ T.triangles : u ∈ t ∧ v ∈ t}|.

    2. **Codegree analysis for the regular k-subdivision.**
       Triangles are of two types:
       - Up-triangle ▲(i,j): vertices {(i,j), (i+1,j), (i,j+1)}, exists when i+j < k
       - Down-triangle ▽(i,j): vertices {(i+1,j), (i,j+1), (i+1,j+1)}, exists when i+j+1 < k

       Edges come in three types (by coordinate difference):
       - Type A: (i,j)↔(i+1,j) — in ▲(i,j) [if i+j<k] and ▽(i,j-1) [if j>0 ∧ i+j<k]
       - Type B: (i,j)↔(i,j+1) — in ▲(i,j) [if i+j<k] and ▽(i-1,j) [if i>0 ∧ i+j<k]
       - Type C: (i+1,j)↔(i,j+1) — in ▲(i,j) [if i+j<k] and ▽(i,j) [if i+j+1<k]

       Boundary edges (codeg = 1):
       - Type A with j=0 (on e₀e₁ face, coord 1 = 0)
       - Type B with i=0 (on e₁e₂ face, coord 0 = 0)
       - Type C with i+j+1=k (on e₀e₂ face, coord 2 = 0)

       Interior edges (codeg = 2): all others.

    3. **Mod 2:** ∑ n₁·n₂ ≡ #{boundary 12-edges} (mod 2).

    4. **Boundary 12-edges only on e₁e₂ face (coord 0 = 0).**
       - e₀e₁ face (coord 2 = 0): hcol_boundary ⟹ col ≠ 2, so no color-2 vertex → no 12-pair
       - e₀e₂ face (coord 1 = 0): hcol_boundary ⟹ col ≠ 1, so no color-1 vertex → no 12-pair
       - e₁e₂ face (coord 0 = 0): col ∈ {1,2}. First vertex (0,0,k) → col=2,
         last vertex (0,k,0) → col=1. By `odd_transitions`, odd number of changes.

    5. **∴** ∑ n₁·n₂ is odd. ∎

    ### Why formalization failed (5 worker attempts)

    The core obstacle is **Step 1 (sum-swap)** in Lean 4 / Mathlib.

    `allTris` is defined as a 3-layer `Finset.biUnion` over `SubdivVert k`:
    ```
    allTris = Finset.univ.biUnion (fun v0 =>
      Finset.univ.biUnion (fun v1 =>
        Finset.univ.biUnion (fun v2 => if ... then {t} else ∅)))
    ```

    To perform the sum-swap, we need:
    ```
    ∑ t ∈ allTris, ∑ u ∈ t, ∑ v ∈ t, [col u = 1] * [col v = 2]
    = ∑ u : Fin m, ∑ v : Fin m, [col u = 1] * [col v = 2] * codeg(u,v)
    ```

    This requires:
    (a) `Finset.sum_biUnion` with disjointness proof — but allTris may have duplicate
        entries from different (v0,v1,v2) triples producing the same set
    (b) Expressing `u ∈ t` for `t ∈ allTris` requires unwinding the 3-layer biUnion
    (c) `codeg(u,v)` requires enumerating all triangles containing a given pair,
        which means solving `∃ i j, ...` conditions for each edge type

    **Step 2 (codegree = 1 or 2)** is also difficult because it requires:
    (a) Case-splitting on edge type (A/B/C)
    (b) For each type, showing exactly which ▲ and ▽ contain the edge
    (c) Proving these are the ONLY triangles containing the edge (exhaustive search
        over the biUnion definition)

    Each sub-step is individually provable but requires ~50-100 lines of Lean.
    The total proof would be ~300-500 lines of mechanical Finset manipulation.

    ### Possible remediation approaches

    1. **Redefine allTris** using `Finset.image` over `Fin k × Fin k` (up-triangles)
       and `Fin k × Fin k` (down-triangles) separately, instead of 3-layer biUnion.
       This would make membership and codegree proofs much more tractable.

    2. **Add codegree as a field of SubdivData**, proved directly in `subdivTriangulation`
       where `allTris`, `encode`, `mkVert` are all in scope.

    3. **Use ZMod 2 linear algebra** to avoid explicit codegree computation:
       define the incidence matrix over ZMod 2 and use matrix rank arguments.

    4. **Path-tracing argument**: bypass the sum entirely, directly construct a
       rainbow triangle by following the dual-graph path from a boundary 12-edge
       using well-founded recursion on visited triangle count.

    Note: The Brouwer FPT is independently proved via covering spaces in
    `Ch28/BrouwerCovering.lean` (sorry-free). This Sperner route is the
    tex-aligned alternative proof.
    -/
  obtain ⟨count12, h_rainbow_iff, h_range, h_odd_sum⟩ :=
    subdivSperner_odd_sum f hfS hne k hk m T decode hadj col hcol_boundary h_odd_sum_concrete
  obtain ⟨t, ht, hrainbow⟩ := sperner_lemma_exists T col count12 h_rainbow_iff h_range h_odd_sum
  exact rainbow_triangle_gives_vertices f hfS hne k hk m T decode col t ht
    (T.triangle_card t ht) hrainbow (fun v => rfl) hadj

/-- **Brouwer's fixed-point theorem on the standard 2-simplex (Sperner route).**

    If f : Δ² → Δ² is continuous, then f has a fixed point.
    Uses `sperner_coloring_rainbow_triangles` for each k, compactness of Δ²,
    and the sum-to-one constraint. -/
private theorem brouwer_fixed_point_simplex2_sperner
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hfc : Continuous f) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2) :
    ∃ x ∈ stdSimplex2, f x = x := by
  -- Use contradiction: assume no fixed point, then spernerColor is always well-defined
  by_contra hno
  push_neg at hno
  have hne : ∀ x ∈ stdSimplex2, f x ≠ x := by
    intro x hx heq; exact hno x hx heq
  -- For each k ≥ 1, get rainbow triangle vertices
  choose vk hvk_mem hvk_col hvk_diam using
    fun k => sperner_coloring_rainbow_triangles f hfc hfS hne (k + 1) (Nat.succ_pos k)
  -- x k = vk k 0 ∈ stdSimplex2
  set x : ℕ → (Fin 3 → ℝ) := fun k => vk k 0
  -- Extract convergent subsequence by compactness
  obtain ⟨xstar, hxstar_mem, φ, hφ_strict, hφ_lim⟩ :=
    stdSimplex2_isCompact.tendsto_subseq (fun k => hvk_mem k 0)
  have hfxstar_mem : f xstar ∈ stdSimplex2 := hfS xstar hxstar_mem
  -- For each i, show f(xstar) i ≤ xstar i, then sum constraint gives equality
  suffices hle : ∀ i, f xstar i ≤ xstar i by
    have heq : f xstar = xstar := by
      ext i; exact le_antisymm (hle i) (by
        by_contra hlt; push_neg at hlt
        have : ∑ j, f xstar j < ∑ j, xstar j :=
          Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
        linarith [hfxstar_mem.2, hxstar_mem.2])
    exact hne xstar hxstar_mem heq
  -- For each i, vk (φ n) i → xstar (since vk (φ n) 0 → xstar and diameter → 0)
  -- and f(vk (φ n) i) i < (vk (φ n) i) i, so by continuity f(xstar) i ≤ xstar i
  intro i
  -- Step 1: vk (φ n) i → xstar
  -- This follows because dist(vk (φ n) i, vk (φ n) 0) ≤ √2/(φ n + 1) → 0
  -- and vk (φ n) 0 = x (φ n) → xstar
  have hvi_tends : Filter.Tendsto (fun n => vk (φ n) i) Filter.atTop (nhds xstar) := by
    rw [Metric.tendsto_atTop] at hφ_lim ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hφ_lim (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (Real.sqrt 2 / (ε / 2))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hφn_ge : N₂ ≤ φ n := by
      have hmono : ∀ m, m ≤ φ m := by
        intro m; induction m with
        | zero => omega
        | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ_strict (Nat.lt_succ_of_le le_rfl)))
      exact le_trans (le_max_right N₁ N₂ |>.trans hn) (hmono n)
    have h_diam : Real.sqrt 2 / (↑(φ n + 1) : ℝ) < ε / 2 := by
      rw [Nat.cast_add, Nat.cast_one, div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(φ n) + 1)]
      calc Real.sqrt 2 < ε / 2 * ↑N₂ := by
              rw [div_lt_iff₀ (half_pos hε)] at hN₂; linarith
        _ ≤ ε / 2 * (↑(φ n) + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact_mod_cast Nat.le_succ_of_le hφn_ge
    have h_sub : dist (x (φ n)) xstar < ε / 2 := hN₁ n (le_max_left _ _ |>.trans hn)
    calc dist (vk (φ n) i) xstar
        ≤ dist (vk (φ n) i) (vk (φ n) 0) + dist (vk (φ n) 0) xstar := dist_triangle _ _ _
      _ ≤ Real.sqrt 2 / (↑(φ n + 1) : ℝ) + dist (x (φ n)) xstar := by
          gcongr; exact hvk_diam (φ n) i 0
      _ < ε / 2 + ε / 2 := add_lt_add h_diam h_sub
      _ = ε := by ring
  -- Step 2: f continuous ⟹ f(vk (φ n) i) i → f(xstar) i
  have hfi_cont : Continuous (fun v => f v i) := (continuous_apply i).comp hfc
  have hfi_tends := (hfi_cont.tendsto xstar).comp hvi_tends
  -- Step 3: f(vk (φ n) i) i < (vk (φ n) i) i ⟹ f(xstar) i ≤ xstar i
  have hvi_i_tends := ((continuous_apply i).tendsto xstar).comp hvi_tends
  exact le_of_tendsto_of_tendsto hfi_tends hvi_i_tends
    (Filter.eventually_atTop.mpr ⟨0, fun n _ => le_of_lt (hvk_col (φ n) i)⟩)



end chapter28
