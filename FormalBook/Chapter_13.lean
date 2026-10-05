/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Basic.Real.Sign
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto
/-!
# Three applications of Euler's formula

This development proves Euler's formula for combinatorial maps satisfying a Jordan separation
property, planar graph bounds, nonplanarity of `K₅` and `K₃,₃`, the Sylvester-Gallai theorem via
Kelly's argument, and Pick's theorem for nondegenerate lattice triangles.

The monochromatic-lines application and Pick's theorem for general lattice polygons remain
unfinished. The passage from geometric plane drawings to combinatorial maps is also not formalized.
-/

@[expose] public section

/-! ════════════════ Part: Multigraph ════════════════ -/

/-!
# Connected components of finite multigraphs

A (directed) multigraph is given by a type of vertices `V`, a type of edges `E` and two maps
`src tgt : E → V`.  For a set `S` of edges we consider the equivalence relation "joined by a path
of edges of `S`" and the number of its classes (connected components of the spanning subgraph
with edge set `S`).  The key fact used in the proof of Euler's formula is how this number
changes when a single edge is added.
-/


namespace Chapter13

/-! Small version-independent helper lemmas (stable replacements for core/Mathlib lemmas whose
names have changed between releases). -/

theorem ch13_if_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ch13_if_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem ch13_mem_setOf {α : Type*} {p : α → Prop} {a : α} : (a ∈ {x | p x}) = p a := rfl

theorem ch13_mem_sdiff {α : Type*} {s t : Set α} {a : α} : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := Iff.rfl

end Chapter13

namespace Chapter13
namespace Multigraph

variable {V E : Type*} (src tgt : E → V)

/-- `u` and `v` are joined by an edge of `S`. -/
def Adj (S : Set E) (u v : V) : Prop := ∃ e ∈ S, src e = u ∧ tgt e = v

/-- `u` and `v` are joined by a path (ignoring orientations) using edges of `S`. -/
def Conn (S : Set E) : V → V → Prop := Relation.EqvGen (Adj src tgt S)

/-- The number of connected components of the spanning subgraph with edge set `S`. -/
noncomputable def numComp (S : Set E) : ℕ := Nat.card (Quot (Adj src tgt S))

variable {src tgt}

theorem conn_equivalence (S : Set E) : Equivalence (Conn src tgt S) :=
  Relation.EqvGen.is_equivalence _

theorem Conn.refl {S : Set E} (u : V) : Conn src tgt S u u := (conn_equivalence S).refl u

theorem Conn.symm {S : Set E} {u v : V} (h : Conn src tgt S u v) : Conn src tgt S v u :=
  (conn_equivalence S).symm h

theorem Conn.trans {S : Set E} {u v w : V} (h : Conn src tgt S u v) (h' : Conn src tgt S v w) :
    Conn src tgt S u w :=
  (conn_equivalence S).trans h h'

theorem Conn.mono {S T : Set E} (hST : S ⊆ T) {u v : V} (h : Conn src tgt S u v) :
    Conn src tgt T u v := by
  unfold Conn at h
  induction h
  case rel x y hr =>
    obtain ⟨e, he, h1, h2⟩ := hr
    exact Relation.EqvGen.rel _ _ ⟨e, hST he, h1, h2⟩
  case refl x => exact (conn_equivalence T).refl x
  case symm x y _ ih => exact (conn_equivalence T).symm ih
  case trans x y z _ _ ih₁ ih₂ => exact (conn_equivalence T).trans ih₁ ih₂

theorem conn_of_mem {S : Set E} {e : E} (he : e ∈ S) : Conn src tgt S (src e) (tgt e) :=
  Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩

theorem conn_empty_iff {u v : V} : Conn src tgt (∅ : Set E) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => obtain ⟨e, he, -⟩ := hxy; exact absurd he (Set.notMem_empty e)
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · rintro rfl; exact Conn.refl u

/-- Description of the connectivity relation after adding one edge. -/
theorem conn_insert_iff {S : Set E} {e : E} {u v : V} :
    Conn src tgt (insert e S) u v ↔
      Conn src tgt S u v ∨ (Conn src tgt S u (src e) ∧ Conn src tgt S (tgt e) v) ∨
        (Conn src tgt S u (tgt e) ∧ Conn src tgt S (src e) v) := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      obtain ⟨e', he', rfl, rfl⟩ := hxy
      rcases he' with rfl | he'
      · exact Or.inr (Or.inl ⟨Conn.refl _, Conn.refl _⟩)
      · exact Or.inl (conn_of_mem he')
    | refl x => exact Or.inl (Conn.refl x)
    | symm x y _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
      · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
    | trans x y z _ _ ih1 ih2 =>
      rcases ih1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ih2 with k | ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact Or.inl (h.trans k)
      · exact Or.inr (Or.inl ⟨h.trans k1, k2⟩)
      · exact Or.inr (Or.inr ⟨h.trans k1, k2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2.trans k⟩)
      · exact Or.inr (Or.inl ⟨h1, k2⟩)
      · exact Or.inl (h1.trans k2)
      · exact Or.inr (Or.inr ⟨h1, h2.trans k⟩)
      · exact Or.inl (h1.trans k2)
      · exact Or.inr (Or.inr ⟨h1, k2⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono (Set.subset_insert _ _)
    · exact ((h1.mono (Set.subset_insert _ _)).trans (conn_of_mem (Set.mem_insert _ _))).trans
        (h2.mono (Set.subset_insert _ _))
    · exact ((h1.mono (Set.subset_insert _ _)).trans
        (conn_of_mem (Set.mem_insert _ _)).symm).trans (h2.mono (Set.subset_insert _ _))

theorem quot_mk_eq_iff {S : Set E} {u v : V} :
    Quot.mk (Adj src tgt S) u = Quot.mk _ v ↔ Conn src tgt S u v :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

theorem numComp_empty : numComp src tgt (∅ : Set E) = Nat.card V := by
  unfold numComp
  apply Nat.card_congr
  symm
  refine Equiv.ofBijective (Quot.mk _) ⟨fun u v h => ?_, Quot.mk_surjective⟩
  exact conn_empty_iff.1 (quot_mk_eq_iff.1 h)

theorem numComp_eq_one {S : Set E} [hV : Nonempty V] (h : ∀ u v, Conn src tgt S u v) :
    numComp src tgt S = 1 := by
  unfold numComp
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨Quot.mk _ (Classical.choice hV)⟩⟩
  induction a using Quot.ind
  induction b using Quot.ind
  exact quot_mk_eq_iff.2 (h _ _)

open Classical in
/-- Adding an edge decreases the number of components by one if the edge joins two
different components, and leaves it unchanged otherwise. -/
theorem numComp_insert [Finite V] (S : Set E) (e : E) :
    numComp src tgt (insert e S) + (if Conn src tgt S (src e) (tgt e) then 0 else 1) =
      numComp src tgt S := by
  unfold numComp
  have hmono : ∀ a b, Adj src tgt S a b → Adj src tgt (insert e S) a b :=
    fun _ _ ⟨e', he', h1, h2⟩ => ⟨e', Set.mem_insert_of_mem _ he', h1, h2⟩
  set g : Quot (Adj src tgt S) → Quot (Adj src tgt (insert e S)) := Quot.map id hmono with hg
  have gmk : ∀ u, g (Quot.mk _ u) = Quot.mk _ u := fun u => rfl
  have gsurj : Function.Surjective g := by
    intro q; induction q using Quot.ind with | mk u => exact ⟨Quot.mk _ u, rfl⟩
  split_ifs with hab
  · rw [add_zero]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective g ⟨fun a b h => ?_, gsurj⟩
    induction a using Quot.ind with | mk u =>
    induction b using Quot.ind with | mk v =>
    rw [gmk, gmk, quot_mk_eq_iff, conn_insert_iff] at h
    rw [quot_mk_eq_iff]
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact (h1.trans hab).trans h2
    · exact (h1.trans hab.symm).trans h2
  · have : Nat.card (Quot (Adj src tgt S)) = Nat.card (Option (Quot (Adj src tgt (insert e S))))
        := by
      apply Nat.card_congr
      refine Equiv.ofBijective
        (fun q => if q = Quot.mk _ (tgt e) then none else some (g q)) ⟨fun a b h => ?_, ?_⟩
      · induction a using Quot.ind with | mk u =>
        induction b using Quot.ind with | mk v =>
        simp only [quot_mk_eq_iff] at h ⊢
        by_cases hu : Conn src tgt S u (tgt e) <;> by_cases hv : Conn src tgt S v (tgt e) <;>
          simp only [hu, hv, ite_true, ite_false, reduceCtorEq, Option.some.injEq] at h
        · exact hu.trans hv.symm
        · rw [gmk, gmk, quot_mk_eq_iff, conn_insert_iff] at h
          rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h
          · exact absurd h2.symm hv
          · exact absurd h1 hu
      · intro o
        cases o with
        | none => exact ⟨Quot.mk _ (tgt e), by simp⟩
        | some q =>
          induction q using Quot.ind with | mk u =>
          by_cases hu : Conn src tgt S u (tgt e)
          · refine ⟨Quot.mk _ (src e), ?_⟩
            have : ¬ Conn src tgt S (src e) (tgt e) := hab
            simp only [quot_mk_eq_iff, this, ite_false, gmk, Option.some.injEq]
            exact (conn_of_mem (Set.mem_insert _ _)).trans
              ((hu.mono (Set.subset_insert _ _)).symm)
          · refine ⟨Quot.mk _ u, ?_⟩
            simp only [quot_mk_eq_iff, hu, ite_false, gmk]
    have hfin : Finite (Quot (Adj src tgt (insert e S))) := Finite.of_surjective g gsurj
    rw [this, Finite.card_option]

end Multigraph
end Chapter13

/-! ════════════════ Part: CombMap ════════════════ -/

/-!
# Combinatorial maps (plane graphs) and Euler's formula

A *plane graph* is encoded combinatorially, as is standard, by a *combinatorial map*:

* `D` is a finite set of *darts* (half-edges); every edge consists of two darts, one at each
  of its ends (a loop also has two darts);
* `α : D → D` is the fixed-point free involution exchanging the two darts of an edge;
* `σ : D → D` is the permutation which sends every dart to the next dart in the counterclockwise
  cyclic order of the darts around its vertex (this is the information that a drawing in the
  plane provides).

The *vertices* are the orbits of `σ`, the *edges* the orbits of `α`, and the *faces* are the
orbits of `φ = σ ∘ α`: walking along the boundary of a face, one leaves a vertex along a dart
`d`, arrives at the other end along `α d`, and turns to the next dart `σ (α d)`.
A dart `d` thus lies on exactly one vertex and on exactly one face; the two faces on the two
sides of the edge of `d` are the faces of `d` and of `α d`.

## Planarity

Being drawn in the plane (or on the sphere) is expressed by the combinatorial form of the
**Jordan curve theorem**, which is exactly the topological input used in the book's proof
("otherwise it would separate some vertices of `G` inside the cycle from vertices outside"):

> if an edge `e` together with a path of edges from a set `S` (not containing `e`) forms a
> closed curve, then the two faces on the two sides of `e` cannot be joined by a chain of faces
> in which consecutive faces share an edge that is neither `e` nor in `S`.

We show (following the "self-dual" proof of von Staudt presented in the book) that this implies
Euler's formula `n - e + f = 2` for connected maps.  Conversely, Euler's formula implies the
Jordan property, so both describe the same class of maps (the maps of genus `0`).
-/


namespace Chapter13

/-- A combinatorial map: a finite set of darts with a rotation `σ` around the vertices and a
fixed-point free involution `α` exchanging the two darts of every edge. -/
structure CombMap (D : Type*) where
  /-- rotation of the darts around their vertex -/
  σ : Equiv.Perm D
  /-- the involution exchanging the two darts of an edge -/
  α : Equiv.Perm D
  α_α : ∀ d, α (α d) = d
  α_ne : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} (M : CombMap D)

/-- The face permutation `φ = σ ∘ α`. -/
def φ : Equiv.Perm D := M.α.trans M.σ

/-- Vertices are the orbits of `σ`. -/
def Vertex : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.σ)
/-- Edges are the orbits of `α`. -/
def Edge : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.α)
/-- Faces are the orbits of `φ = σ ∘ α`. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.φ)

/-- The vertex at which a dart starts. -/
def vtx (d : D) : M.Vertex := Quotient.mk _ d
/-- The edge a dart belongs to. -/
def edgeOf (d : D) : M.Edge := Quotient.mk _ d
/-- The face on the left of a dart. -/
def face (d : D) : M.Face := Quotient.mk _ d

/-- number of vertices -/
noncomputable def numVertices : ℕ := Nat.card M.Vertex
/-- number of edges -/
noncomputable def numEdges : ℕ := Nat.card M.Edge
/-- number of faces -/
noncomputable def numFaces : ℕ := Nat.card M.Face

/-- The degree of a vertex: the number of darts at it (a loop counts twice). -/
noncomputable def degree (v : M.Vertex) : ℕ := Nat.card {d : D // M.vtx d = v}

/-- The number of sides of a face (an edge which has the face on both sides counts twice). -/
noncomputable def sides (x : M.Face) : ℕ := Nat.card {d : D // M.face d = x}

/-- The map is connected: any two darts can be joined by moving around vertices and along
edges. -/
def Connected : Prop := ∀ d d' : D, Relation.EqvGen (fun x y => y = M.σ x ∨ y = M.α x) d d'

/-- Connectivity of vertices using only the edges in `S`. -/
def ConnV (S : Set M.Edge) : M.Vertex → M.Vertex → Prop :=
  Multigraph.Conn M.vtx (M.vtx ∘ M.α) {d | M.edgeOf d ∈ S}

/-- Connectivity of faces in the dual graph, crossing only the edges in `S`. -/
def ConnF (S : Set M.Edge) : M.Face → M.Face → Prop :=
  Multigraph.Conn M.face (M.face ∘ M.α) {d | M.edgeOf d ∈ S}

/-- **Planarity** (combinatorial Jordan curve property): a closed curve formed by an edge `e`
and a path of edges of `S` separates the two faces on the two sides of `e`. -/
def IsPlanar : Prop :=
  ∀ (S : Set M.Edge) (d : D), M.edgeOf d ∉ S → M.ConnV S (M.vtx d) (M.vtx (M.α d)) →
    ¬ M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d))

/-! ### Basic lemmas -/

instance [Finite D] : Finite M.Vertex := Quotient.finite _
instance [Finite D] : Finite M.Edge := Quotient.finite _
instance [Finite D] : Finite M.Face := Quotient.finite _
noncomputable instance [Finite D] : Fintype M.Vertex := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Edge := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Face := Fintype.ofFinite _
instance [h : Nonempty D] : Nonempty M.Vertex := ⟨M.vtx (Classical.choice h)⟩
instance [h : Nonempty D] : Nonempty M.Edge := ⟨M.edgeOf (Classical.choice h)⟩
instance [h : Nonempty D] : Nonempty M.Face := ⟨M.face (Classical.choice h)⟩

theorem φ_apply (d : D) : M.φ d = M.σ (M.α d) := rfl

theorem vtx_σ (d : D) : M.vtx (M.σ d) = M.vtx d :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))

theorem vtx_eq_iff {d d' : D} : M.vtx d = M.vtx d' ↔ M.σ.SameCycle d d' := Quotient.eq

theorem face_φ (d : D) : M.face (M.φ d) = M.face d :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))

theorem face_eq_iff {d d' : D} : M.face d = M.face d' ↔ M.φ.SameCycle d d' := Quotient.eq

theorem vtx_φ (d : D) : M.vtx (M.φ d) = M.vtx (M.α d) := M.vtx_σ _

theorem face_σ (d : D) : M.face (M.σ d) = M.face (M.α d) := by
  have : M.σ d = M.φ (M.α d) := by simp [φ_apply, M.α_α]
  rw [this, face_φ]

theorem α_symm (d : D) : M.α.symm d = M.α d := by
  rw [Equiv.symm_apply_eq, M.α_α]

theorem α_zpow (i : ℤ) (d : D) : (M.α ^ i) d = d ∨ (M.α ^ i) d = M.α d := by
  induction i using Int.induction_on generalizing d with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply]
    rcases ih (M.α d) with h | h
    · exact Or.inr h
    · exact Or.inl (h.trans (M.α_α d))
  | pred i ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, α_symm]
    rcases ih (M.α d) with h | h
    · exact Or.inr h
    · exact Or.inl (h.trans (M.α_α d))

theorem edgeOf_eq_iff {d t : D} : M.edgeOf t = M.edgeOf d ↔ t = d ∨ t = M.α d := by
  rw [show M.edgeOf t = M.edgeOf d ↔ M.α.SameCycle t d from Quotient.eq]
  constructor
  · rintro ⟨i, hi⟩
    rcases M.α_zpow i t with h | h
    · exact Or.inl (h.symm.trans hi)
    · right
      rw [← hi, h, M.α_α]
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨-1, by simp [Equiv.Perm.inv_def]⟩

theorem edgeOf_α (d : D) : M.edgeOf (M.α d) = M.edgeOf d := M.edgeOf_eq_iff.2 (Or.inr rfl)

theorem vtx_surjective : Function.Surjective M.vtx := Quotient.mk_surjective
theorem edgeOf_surjective : Function.Surjective M.edgeOf := Quotient.mk_surjective
theorem face_surjective : Function.Surjective M.face := Quotient.mk_surjective

/-! ### Adding an edge -/

/-- Generic connectivity relation for a labelling `g` of the darts (`g = vtx` gives the graph,
`g = face` the dual graph). -/
def connBy {X : Type*} (g : D → X) (S : Set M.Edge) : X → X → Prop :=
  Multigraph.Conn g (g ∘ M.α) {d | M.edgeOf d ∈ S}

/-- Generic number of components. -/
noncomputable def compBy {X : Type*} (g : D → X) (S : Set M.Edge) : ℕ :=
  Multigraph.numComp g (g ∘ M.α) {d | M.edgeOf d ∈ S}

theorem darts_insert (S : Set M.Edge) (d : D) :
    {t | M.edgeOf t ∈ insert (M.edgeOf d) S} = insert d (insert (M.α d) {t | M.edgeOf t ∈ S}) := by
  ext t
  simp only [Set.mem_insert_iff, ch13_mem_setOf, M.edgeOf_eq_iff]
  tauto

open Classical in
theorem compBy_insert {X : Type*} [Finite X] (g : D → X) (S : Set M.Edge) (d : D) :
    M.compBy g (insert (M.edgeOf d) S) + (if M.connBy g S (g d) (g (M.α d)) then 0 else 1) =
      M.compBy g S := by
  unfold compBy connBy
  rw [darts_insert]
  have h1 := Multigraph.numComp_insert (src := g) (tgt := g ∘ M.α)
    (insert (M.α d) {t | M.edgeOf t ∈ S}) d
  have h2 := Multigraph.numComp_insert (src := g) (tgt := g ∘ M.α) {t | M.edgeOf t ∈ S} (M.α d)
  have hc : Multigraph.Conn g (g ∘ M.α) (insert (M.α d) {t | M.edgeOf t ∈ S}) (g d)
      ((g ∘ M.α) d) := by
    have := Multigraph.conn_of_mem (src := g) (tgt := g ∘ M.α)
      (Set.mem_insert (M.α d) {t | M.edgeOf t ∈ S})
    simp only [Function.comp_apply, M.α_α] at this ⊢
    exact this.symm
  rw [ch13_if_pos hc, add_zero] at h1
  rw [h1, ← h2]
  congr 1
  have : Multigraph.Conn g (g ∘ M.α) {t | M.edgeOf t ∈ S} (g (M.α d)) ((g ∘ M.α) (M.α d)) ↔
      Multigraph.Conn g (g ∘ M.α) {t | M.edgeOf t ∈ S} (g d) (g (M.α d)) := by
    simp only [Function.comp_apply, M.α_α]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  simp only [this]

theorem compBy_empty {X : Type*} (g : D → X) : M.compBy g ∅ = Nat.card X := by
  unfold compBy
  have : {d | M.edgeOf d ∈ (∅ : Set M.Edge)} = ∅ := by ext; simp
  rw [this, Multigraph.numComp_empty]

theorem connBy_mono {X : Type*} (g : D → X) {S T : Set M.Edge} (h : S ⊆ T) {x y : X}
    (hxy : M.connBy g S x y) : M.connBy g T x y := by
  unfold connBy at *
  exact Multigraph.Conn.mono (S := {d | M.edgeOf d ∈ S}) (T := {d | M.edgeOf d ∈ T})
    (fun _ ht => h ht) hxy

theorem connBy_edge {X : Type*} (g : D → X) {S : Set M.Edge} {d : D} (hd : M.edgeOf d ∈ S) :
    M.connBy g S (g d) (g (M.α d)) :=
  Multigraph.conn_of_mem (src := g) (tgt := g ∘ M.α) (show d ∈ {t | M.edgeOf t ∈ S} from hd)

/-! ### Connectivity -/

theorem connV_univ_of_connected (hM : M.Connected) (d d' : D) :
    M.ConnV Set.univ (M.vtx d) (M.vtx d') := by
  induction hM d d' with
  | rel x y hxy =>
    rcases hxy with rfl | rfl
    · rw [vtx_σ]; exact Multigraph.Conn.refl _
    · exact M.connBy_edge M.vtx (Set.mem_univ _)
  | refl x => exact Multigraph.Conn.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem connF_univ_of_connected (hM : M.Connected) (d d' : D) :
    M.ConnF Set.univ (M.face d) (M.face d') := by
  induction hM d d' with
  | rel x y hxy =>
    rcases hxy with rfl | rfl
    · rw [face_σ]; exact M.connBy_edge M.face (Set.mem_univ _)
    · exact M.connBy_edge M.face (Set.mem_univ _)
  | refl x => exact Multigraph.Conn.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Two parity lemmas -/

open Classical in
/-- Along the cycles of a permutation, a property changes an even number of times. -/
theorem even_card_changes (p : Equiv.Perm D) (A : Finset D) (hA : ∀ t ∈ A, p t ∈ A)
    (χ : D → Prop) : Even (A.filter (fun t => ¬ (χ t ↔ χ (p t)))).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, Finset.card_filter, Nat.cast_sum]
  set b : D → ZMod 2 := fun t => if χ t then 1 else 0
  have key : ∀ t, ((if ¬ (χ t ↔ χ (p t)) then 1 else 0 : ℕ) : ZMod 2) = b t + b (p t) := by
    intro t
    by_cases h1 : χ t <;> by_cases h2 : χ (p t) <;> (simp [b, h1, h2]; try decide)
  simp_rw [key, Finset.sum_add_distrib]
  have himg : A.image p = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact hA t ht
    · rw [Finset.card_image_of_injective _ p.injective]
  have : ∑ t ∈ A, b (p t) = ∑ t ∈ A, b t := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun x _ y _ h => p.injective h)]
  rw [this, ← two_mul]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_mul]

/-- A finite set stable under a fixed-point free involution has even cardinality. -/
theorem even_card_of_involution (A : Finset D) (hA : ∀ t ∈ A, M.α t ∈ A) : Even A.card := by
  classical
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
    · simp
    · set A' := (A.erase t).erase (M.α t)
      have hαt : M.α t ∈ A.erase t := Finset.mem_erase.2 ⟨M.α_ne t, hA t ht⟩
      have hcard : A.card = A'.card + 2 := by
        have h0 := Finset.card_pos.2 ⟨_, hαt⟩
        simp only [A']
        rw [Finset.card_erase_of_mem hαt, Finset.card_erase_of_mem ht] at *
        omega
      have hsub : A' ⊂ A :=
        (Finset.erase_ssubset hαt).trans_subset (Finset.erase_subset _ _)
      have hA' : ∀ s ∈ A', M.α s ∈ A' := by
        intro s hs
        simp only [A', Finset.mem_erase] at hs ⊢
        exact ⟨fun h => hs.2.1 (M.α.injective h), fun h => hs.1 (by rw [← h, M.α_α]),
          hA s hs.2.2⟩
      rw [hcard]
      exact (ih A' hsub hA').add even_two

/-! ### The key lemma: at least one of a primal and a dual connection exists -/

open Classical in
/-- For an edge `e = {d, α d}` not in `S`: either the ends of `e` are joined by a path in `S`,
or the two faces beside `e` are joined in the dual graph avoiding `S` and `e`.
(This holds for every map; planarity says that not both can happen.) -/
theorem connV_or_connF [Fintype D] (S : Set M.Edge) (d : D) (hd : M.edgeOf d ∉ S) :
    M.ConnV S (M.vtx d) (M.vtx (M.α d)) ∨
      M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := by
  by_contra h
  push Not at h
  obtain ⟨hV, hF⟩ := h
  -- the vertices reachable from the start of `d`
  set K : D → Prop := fun t => M.ConnV S (M.vtx d) (M.vtx t) with hK
  -- darts of the cut, other than `d` and `α d`
  set C' : Set D := {t | ¬ (K t ↔ K (M.α t)) ∧ M.edgeOf t ≠ M.edgeOf d} with hC'
  have hC'sub : C' ⊆ {t | M.edgeOf t ∈ Sᶜ \ {M.edgeOf d}} := by
    rintro t ⟨ht1, ht2⟩
    refine ⟨fun hS => ht1 ?_, ht2⟩
    have : M.ConnV S (M.vtx t) (M.vtx (M.α t)) := M.connBy_edge M.vtx hS
    exact ⟨fun h => h.trans this, fun h => h.trans this.symm⟩
  set L : D → Prop := fun t => Multigraph.Conn M.face (M.face ∘ M.α) C' (M.face d) (M.face t)
    with hL
  have hLαd : ¬ L (M.α d) := fun h => hF (Multigraph.Conn.mono hC'sub h)
  have hKαd : ¬ K (M.α d) := hV
  -- count the darts of the cut lying on faces reachable from the face of `d`
  set N := (Finset.univ.filter (fun t => ¬ (K t ↔ K (M.α t)) ∧ L t)).card with hN
  have heven : Even N := by
    have := even_card_changes M.φ (Finset.univ.filter L) (by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      simp only [L, face_φ]; exact ht) K
    rw [Finset.filter_filter] at this
    convert this using 2
    ext t
    simp only [K, vtx_φ, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hodd : Odd N := by
    have hsplit : Finset.univ.filter (fun t => ¬ (K t ↔ K (M.α t)) ∧ L t) =
        insert d (Finset.univ.filter (fun t => t ∈ C' ∧ L t)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, C',
        ch13_mem_setOf]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases he : M.edgeOf t = M.edgeOf d
        · rcases M.edgeOf_eq_iff.1 he with rfl | rfl
          · exact Or.inl rfl
          · exact absurd h2 hLαd
        · exact Or.inr ⟨⟨h1, he⟩, h2⟩
      · rintro (rfl | ⟨⟨h1, _⟩, h2⟩)
        · refine ⟨?_, Multigraph.Conn.refl _⟩
          simp only [K]
          exact fun h => hKαd (h.1 (Multigraph.Conn.refl _))
        · exact ⟨h1, h2⟩
    have hdnot : d ∉ Finset.univ.filter (fun t => t ∈ C' ∧ L t) := by
      simp [C']
    rw [hN, hsplit, Finset.card_insert_of_notMem hdnot]
    apply Even.add_one
    apply M.even_card_of_involution
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, C', ch13_mem_setOf] at ht ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    refine ⟨⟨?_, by rwa [edgeOf_α]⟩, ?_⟩
    · rw [M.α_α]; tauto
    · have : Multigraph.Conn M.face (M.face ∘ M.α) C' (M.face t) (M.face (M.α t)) :=
        Multigraph.conn_of_mem (src := M.face) (tgt := M.face ∘ M.α)
          (show t ∈ C' from ⟨h1, h2⟩)
      exact h3.trans this
  exact (Nat.not_even_iff_odd.2 hodd) heven

/-! ### Euler's formula -/

/-- The potential `c(S) - c*(Sᶜ)` used in the proof of Euler's formula. -/
noncomputable def potential (S : Set M.Edge) : ℤ :=
  (M.compBy M.vtx S : ℤ) - (M.compBy M.face Sᶜ : ℤ)

open Classical in
theorem potential_insert [Fintype D] (hP : M.IsPlanar) (S : Set M.Edge) (d : D)
    (hd : M.edgeOf d ∉ S) : M.potential (insert (M.edgeOf d) S) = M.potential S - 1 := by
  have h1 := M.compBy_insert M.vtx S d
  have h2 := M.compBy_insert M.face (Sᶜ \ {M.edgeOf d}) d
  have hc : insert (M.edgeOf d) (Sᶜ \ {M.edgeOf d}) = Sᶜ := by
    ext x
    by_cases hx : x = M.edgeOf d
    · subst hx; simp [hd]
    · simp [hx]
  rw [hc] at h2
  have hc' : (insert (M.edgeOf d) S)ᶜ = Sᶜ \ {M.edgeOf d} := by
    ext x; simp [not_or, and_comm]
  have hxor := M.connV_or_connF S d hd
  have hP' := hP S d hd
  unfold potential
  rw [hc', ← h1, ← h2]
  change (_ : ℤ) = _
  by_cases ha : M.ConnV S (M.vtx d) (M.vtx (M.α d))
  · have hb : ¬ M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := hP' ha
    have ha' : M.connBy M.vtx S (M.vtx d) (M.vtx (M.α d)) := ha
    have hb' : ¬ M.connBy M.face (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := hb
    simp only [ha', hb', ite_true, ite_false]
    push_cast; ring
  · have hb : M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := hxor.resolve_left ha
    have ha' : ¬ M.connBy M.vtx S (M.vtx d) (M.vtx (M.α d)) := ha
    have hb' : M.connBy M.face (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := hb
    simp only [ha', hb', ite_true, ite_false]
    push_cast; ring

theorem potential_finset [Fintype D] (hP : M.IsPlanar) (S : Finset M.Edge) :
    M.potential (S : Set M.Edge) = M.potential ∅ - S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert e S he ih =>
    obtain ⟨d, rfl⟩ := M.edgeOf_surjective e
    rw [Finset.coe_insert, M.potential_insert hP _ d (by simpa using he), ih,
      Finset.card_insert_of_notMem he]
    push_cast; ring

/-! ### Connected components -/

/-- The relation "`y` is obtained from `x` by turning around a vertex or by crossing to the other
end of the edge"; its equivalence classes are the connected components of the map. -/
def DartRel (x y : D) : Prop := y = M.σ x ∨ y = M.α x

/-- The number of connected components of the map. -/
noncomputable def numComponents : ℕ := Nat.card (Quot M.DartRel)

theorem connected_iff : M.Connected ↔ ∀ d d', Relation.EqvGen M.DartRel d d' := Iff.rfl

theorem eqvGen_pow (f : Equiv.Perm D) (hf : ∀ x, Relation.EqvGen M.DartRel x (f x)) (n : ℕ)
    (x : D) : Relation.EqvGen M.DartRel x ((f ^ n) x) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans _ _ _ (hf _)

theorem eqvGen_of_sameCycle [Finite D] (f : Equiv.Perm D)
    (hf : ∀ x, Relation.EqvGen M.DartRel x (f x)) {x y : D} (h : f.SameCycle x y) :
    Relation.EqvGen M.DartRel x y := by
  obtain ⟨i, -, rfl⟩ := h.exists_pow_eq'
  exact M.eqvGen_pow f hf i x

theorem eqvGen_σ (x : D) : Relation.EqvGen M.DartRel x (M.σ x) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

theorem eqvGen_α (x : D) : Relation.EqvGen M.DartRel x (M.α x) :=
  Relation.EqvGen.rel _ _ (Or.inr rfl)

theorem eqvGen_φ (x : D) : Relation.EqvGen M.DartRel x (M.φ x) :=
  (M.eqvGen_α x).trans _ _ _ (M.eqvGen_σ _)

/-- For the graph and for its dual, the number of connected components (using all edges) is the
number of connected components of the map. -/
theorem compBy_univ_eq {X : Type*} (g : D → X) (hg : Function.Surjective g)
    (hsame : ∀ d d', g d = g d' → Relation.EqvGen M.DartRel d d')
    (hstep : ∀ d d', M.DartRel d d' → M.connBy g Set.univ (g d) (g d')) :
    M.compBy g Set.univ = M.numComponents := by
  unfold compBy numComponents
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Quot.lift (fun d => Quot.mk _ (g d))
    (fun a b h => Multigraph.quot_mk_eq_iff.2 (hstep a b h))) ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quot.ind with | mk d =>
    induction b using Quot.ind with | mk d' =>
    simp only at hab
    have hc := Multigraph.quot_mk_eq_iff.1 hab
    apply Quot.eqvGen_sound
    have key : ∀ u v, Multigraph.Conn g (g ∘ M.α) {t | M.edgeOf t ∈ Set.univ} u v →
        ∀ d d', g d = u → g d' = v → Relation.EqvGen M.DartRel d d' := by
      intro u v h
      induction h with
      | rel u v huv =>
        obtain ⟨t, -, h1, h2⟩ := huv
        intro d d' hd hd'
        exact ((hsame d t (hd.trans h1.symm)).trans _ _ _ (M.eqvGen_α t)).trans _ _ _
          (hsame _ _ (h2.trans hd'.symm))
      | refl u => intro d d' hd hd'; exact hsame d d' (hd.trans hd'.symm)
      | symm u v _ ih => intro d d' hd hd'; exact (ih d' d hd' hd).symm _ _
      | trans u v w _ _ ih1 ih2 =>
        intro d d' hd hd'
        obtain ⟨m, hm⟩ := hg v
        exact (ih1 d m hd hm).trans _ _ _ (ih2 m d' hm hd')
    exact key _ _ hc d d' rfl rfl
  · intro q
    induction q using Quot.ind with | mk x =>
    obtain ⟨d, rfl⟩ := hg x
    exact ⟨Quot.mk _ d, rfl⟩

theorem compBy_vtx_univ [Finite D] : M.compBy M.vtx Set.univ = M.numComponents := by
  apply M.compBy_univ_eq M.vtx M.vtx_surjective
  · intro d d' h
    exact M.eqvGen_of_sameCycle M.σ M.eqvGen_σ (M.vtx_eq_iff.1 h)
  · rintro d d' (rfl | rfl)
    · rw [vtx_σ]; exact Multigraph.Conn.refl _
    · exact M.connBy_edge M.vtx (Set.mem_univ _)

theorem compBy_face_univ [Finite D] : M.compBy M.face Set.univ = M.numComponents := by
  apply M.compBy_univ_eq M.face M.face_surjective
  · intro d d' h
    exact M.eqvGen_of_sameCycle M.φ M.eqvGen_φ (M.face_eq_iff.1 h)
  · rintro d d' (rfl | rfl)
    · rw [face_σ]; exact M.connBy_edge M.face (Set.mem_univ _)
    · exact M.connBy_edge M.face (Set.mem_univ _)

theorem numComponents_eq_one [Nonempty D] (hM : M.Connected) : M.numComponents = 1 := by
  unfold numComponents
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨Quot.mk _ (Classical.arbitrary D)⟩⟩
  induction a using Quot.ind
  induction b using Quot.ind
  exact Quot.eqvGen_sound (hM _ _)

/-! ### Euler's formula -/

/-- **Euler's formula, general form.** For a plane graph with `n` vertices, `e` edges, `f` faces
and `c` connected components, `n - e + f = 2 c`. -/
theorem euler_formula_general [Fintype D] (hP : M.IsPlanar) :
    (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2 * M.numComponents := by
  classical
  have h := M.potential_finset hP Finset.univ
  simp only [Finset.coe_univ, Finset.card_univ] at h
  unfold potential at h
  rw [Set.compl_univ, Set.compl_empty, M.compBy_vtx_univ, M.compBy_face_univ, M.compBy_empty,
    M.compBy_empty] at h
  unfold numVertices numEdges numFaces
  rw [← Nat.card_eq_fintype_card] at h
  linarith

/-- **Euler's formula.** If `M` is a connected plane graph (with at least one edge) with
`n` vertices, `e` edges and `f` faces, then `n - e + f = 2`. -/
theorem euler_formula [Fintype D] [Nonempty D] (hP : M.IsPlanar) (hM : M.Connected) :
    (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2 := by
  rw [M.euler_formula_general hP, M.numComponents_eq_one hM]
  norm_num

/-! ### The converse: Euler's formula implies the Jordan curve property -/

open Classical in
/-- Without assuming planarity, adding an edge decreases the potential by `1`, except when both
a primal and a dual connection exist, in which case the potential does not change. -/
theorem potential_insert_eq [Fintype D] (S : Set M.Edge) (d : D) (hd : M.edgeOf d ∉ S) :
    M.potential (insert (M.edgeOf d) S) = M.potential S - 1 +
      (if M.ConnV S (M.vtx d) (M.vtx (M.α d)) ∧
          M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) then 1 else 0) := by
  have h1 := M.compBy_insert M.vtx S d
  have h2 := M.compBy_insert M.face (Sᶜ \ {M.edgeOf d}) d
  have hc : insert (M.edgeOf d) (Sᶜ \ {M.edgeOf d}) = Sᶜ := by
    ext x
    by_cases hx : x = M.edgeOf d
    · subst hx; simp [hd]
    · simp [hx]
  rw [hc] at h2
  have hc' : (insert (M.edgeOf d) S)ᶜ = Sᶜ \ {M.edgeOf d} := by
    ext x; simp [not_or, and_comm]
  have hxor := M.connV_or_connF S d hd
  unfold potential
  rw [hc', ← h1, ← h2]
  change (_ : ℤ) = _
  have e1 : M.ConnV S (M.vtx d) (M.vtx (M.α d)) = M.connBy M.vtx S (M.vtx d) (M.vtx (M.α d)) :=
    rfl
  have e2 : M.ConnF (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) =
      M.connBy M.face (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) := rfl
  rw [e1, e2] at hxor ⊢
  by_cases ha : M.connBy M.vtx S (M.vtx d) (M.vtx (M.α d)) <;>
    by_cases hb : M.connBy M.face (Sᶜ \ {M.edgeOf d}) (M.face d) (M.face (M.α d)) <;>
    simp only [ha, hb, ite_true, ite_false, and_true, and_false] <;>
    push_cast <;> first | (exfalso; tauto) | ring

open Classical in
theorem potential_union_le [Fintype D] (S : Finset M.Edge) (U : Finset M.Edge)
    (hSU : Disjoint S U) : M.potential (S : Set M.Edge) - U.card ≤
      M.potential ((S ∪ U : Finset M.Edge) : Set M.Edge) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert e U he ih =>
    obtain ⟨d, rfl⟩ := M.edgeOf_surjective e
    have hdS : M.edgeOf d ∉ ((S ∪ U : Finset M.Edge) : Set M.Edge) := by
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or]
      exact ⟨Finset.disjoint_right.1 hSU (Finset.mem_insert_self _ _), he⟩
    have := M.potential_insert_eq _ d hdS
    have hU : Disjoint S U := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hSU
    have h' := ih hU
    rw [Finset.union_insert, Finset.coe_insert, this, Finset.card_insert_of_notMem he]
    push_cast at h' ⊢
    split_ifs <;> linarith

/-- **Converse of Euler's formula.** A connected map satisfying `n - e + f = 2` has the Jordan
curve property; hence planarity can equivalently be defined through Euler's formula. -/
theorem isPlanar_of_euler [Fintype D] [Nonempty D] (hM : M.Connected)
    (hE : (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2) : M.IsPlanar := by
  classical
  intro S d hd hV hF
  set S' : Finset M.Edge := S.toFinset
  have hS' : (S' : Set M.Edge) = S := Set.coe_toFinset S
  have hdS' : M.edgeOf d ∉ S' := by simpa [S'] using hd
  -- from `∅` to `S`
  have h1 := M.potential_union_le ∅ S' (Finset.disjoint_empty_left _)
  simp only [Finset.empty_union, Finset.coe_empty] at h1
  -- adding the edge of `d`
  have h2 := M.potential_insert_eq S d hd
  rw [ch13_if_pos ⟨hV, hF⟩] at h2
  -- from `insert e S` to everything
  have h3 := M.potential_union_le (insert (M.edgeOf d) S') (Finset.univ \ insert (M.edgeOf d) S')
    Finset.disjoint_sdiff
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), Finset.coe_insert, hS'] at h3
  rw [hS'] at h1
  have hcard : (Finset.univ \ insert (M.edgeOf d) S').card + S'.card + 1 = Fintype.card M.Edge := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem hdS',
      Finset.card_univ]
    have : S'.card + 1 ≤ Fintype.card M.Edge := by
      rw [← Finset.card_insert_of_notMem hdS']; exact Finset.card_le_univ _
    omega
  -- the potential of everything and of nothing
  have hV1 : M.compBy M.vtx Set.univ = 1 := by
    apply Multigraph.numComp_eq_one
    intro u v
    obtain ⟨d, rfl⟩ := M.vtx_surjective u
    obtain ⟨d', rfl⟩ := M.vtx_surjective v
    exact M.connV_univ_of_connected hM d d'
  have hF1 : M.compBy M.face Set.univ = 1 := by
    apply Multigraph.numComp_eq_one
    intro u v
    obtain ⟨d, rfl⟩ := M.face_surjective u
    obtain ⟨d', rfl⟩ := M.face_surjective v
    exact M.connF_univ_of_connected hM d d'
  have hP0 : M.potential ∅ = M.numVertices - 1 := by
    unfold potential
    rw [Set.compl_empty, hF1, M.compBy_empty]; rfl
  have hPu : M.potential ((Finset.univ : Finset M.Edge) : Set M.Edge) = 1 - M.numFaces := by
    unfold potential
    rw [Finset.coe_univ, Set.compl_univ, hV1, M.compBy_empty]; rfl
  rw [hPu] at h3
  rw [hP0] at h1
  have hne : (M.numEdges : ℤ) = Fintype.card M.Edge := by
    unfold numEdges; rw [Nat.card_eq_fintype_card]
  have hcard' : ((Finset.univ \ insert (M.edgeOf d) S').card : ℤ) + S'.card + 1 =
      Fintype.card M.Edge := by exact_mod_cast hcard
  linarith

end CombMap

end Chapter13

/-! ════════════════ Part: Proposition ════════════════ -/

/-!
# Consequences of Euler's formula

* the double counting identities (1)–(4) of the book;
* the Proposition: a simple plane graph with `n > 2` vertices
  (A) has at most `3n - 6` edges,
  (B) has a vertex of degree at most `5`,
  (C) for every two-colouring of its edges has a vertex with at most two colour changes in the
      cyclic order of the edges around it;
* `K₅` and `K₃,₃` are not planar.
-/


namespace Chapter13

namespace CombMap

variable {D : Type*} (M : CombMap D)

/-- The map is *simple*: there are no loops and no multiple edges. -/
def Simple : Prop :=
  (∀ d, M.vtx (M.α d) ≠ M.vtx d) ∧
    ∀ d d', M.vtx d = M.vtx d' → M.vtx (M.α d) = M.vtx (M.α d') → d = d'

/-- The (simple) graph underlying a map: two different vertices are adjacent if some edge joins
them. -/
def graph : SimpleGraph M.Vertex :=
  SimpleGraph.fromRel fun v w => ∃ d, M.vtx d = v ∧ M.vtx (M.α d) = w

/-- Two vertices are adjacent in `M.graph` iff they are different and joined by an edge. -/
theorem graph_adj {v w : M.Vertex} :
    M.graph.Adj v w ↔ v ≠ w ∧ ∃ d, M.vtx d = v ∧ M.vtx (M.α d) = w := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | ⟨d, h1, h2⟩)
  · exact h
  · exact ⟨M.α d, h2, by rw [M.α_α, h1]⟩

/-- The number of colour changes at the vertex `v` for an edge colouring `col`: the number of
corners at `v` (pairs of cyclically consecutive darts `d`, `σ d`) whose two edges have different
colours. -/
noncomputable def colorChanges (col : M.Edge → Bool) (v : M.Vertex) : ℕ :=
  Nat.card {d : D // M.vtx d = v ∧ col (M.edgeOf d) ≠ col (M.edgeOf (M.σ d))}

/-! ### Counting darts -/

section Counting

variable [Fintype D]

open Classical in
theorem card_eq_sum_fiber {X : Type*} [Fintype X] (g : D → X) :
    Fintype.card D = ∑ x : X, Nat.card {d : D // g d = x} := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mul_card_le_of_fiber {X : Type*} [Fintype X] (g : D → X) (k : ℕ)
    (h : ∀ x, k ≤ Nat.card {d : D // g d = x}) : k * Fintype.card X ≤ Fintype.card D := by
  rw [card_eq_sum_fiber g, mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun x _ => h x

theorem card_le_mul_of_fiber {X : Type*} [Fintype X] (g : D → X) (k : ℕ)
    (h : ∀ x, Nat.card {d : D // g d = x} ≤ k) : Fintype.card D ≤ k * Fintype.card X := by
  rw [card_eq_sum_fiber g, mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun x _ => h x

/-- Every edge has two darts: `|D| = 2 e`. -/
theorem card_darts_eq_two_mul_numEdges : Fintype.card D = 2 * M.numEdges := by
  classical
  rw [card_eq_sum_fiber M.edgeOf, numEdges, Nat.card_eq_fintype_card, mul_comm,
    ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨d, rfl⟩ := M.edgeOf_surjective x
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : Finset.univ.filter (fun t => M.edgeOf t = M.edgeOf d) = {d, M.α d} := by
    ext t
    simp [M.edgeOf_eq_iff]
  rw [this, Finset.card_pair (M.α_ne d).symm]

/-- The handshake lemma: the sum of the degrees is `2 e`. -/
theorem sum_degree : ∑ v : M.Vertex, M.degree v = 2 * M.numEdges := by
  rw [← card_darts_eq_two_mul_numEdges, card_eq_sum_fiber M.vtx]
  rfl

/-- The sum of the numbers of sides of the faces is `2 e`. -/
theorem sum_sides : ∑ x : M.Face, M.sides x = 2 * M.numEdges := by
  rw [← card_darts_eq_two_mul_numEdges, card_eq_sum_fiber M.face]
  rfl

open Classical in
theorem degree_le_card (v : M.Vertex) : M.degree v ≤ Fintype.card D := by
  rw [degree, Nat.card_eq_fintype_card]; exact Fintype.card_subtype_le _

open Classical in
theorem sides_le_card (x : M.Face) : M.sides x ≤ Fintype.card D := by
  rw [sides, Nat.card_eq_fintype_card]; exact Fintype.card_subtype_le _

open Classical in
/-- Grouping a sum over a finite type according to the values of a function `g` with values
in `range (N+1)`. -/
theorem card_eq_sum_range {X : Type*} [Fintype X] (g : X → ℕ) (N : ℕ) (hg : ∀ x, g x ≤ N) :
    Fintype.card X = ∑ i ∈ Finset.range (N + 1), Nat.card {x : X // g x = i} := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.range (N + 1))
    (fun x _ => by simpa [Nat.lt_succ_iff] using hg x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
theorem sum_eq_sum_range {X : Type*} [Fintype X] (g : X → ℕ) (N : ℕ) (hg : ∀ x, g x ≤ N) :
    ∑ x : X, g x = ∑ i ∈ Finset.range (N + 1), i * Nat.card {x : X // g x = i} := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := Finset.range (N + 1))
    (fun x _ => by simpa [Nat.lt_succ_iff] using hg x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_const,
    smul_eq_mul, mul_comm, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **(1)** `n = n₀ + n₁ + n₂ + ⋯`, where `nᵢ` is the number of vertices of degree `i`. -/
theorem numVertices_eq_sum :
    M.numVertices = ∑ i ∈ Finset.range (Fintype.card D + 1),
      Nat.card {v : M.Vertex // M.degree v = i} := by
  rw [numVertices, Nat.card_eq_fintype_card]
  exact card_eq_sum_range _ _ M.degree_le_card

/-- **(2)** `2e = n₁ + 2 n₂ + 3 n₃ + ⋯`. -/
theorem two_mul_numEdges_eq_sum :
    2 * M.numEdges = ∑ i ∈ Finset.range (Fintype.card D + 1),
      i * Nat.card {v : M.Vertex // M.degree v = i} := by
  rw [← sum_degree]
  exact sum_eq_sum_range _ _ M.degree_le_card

/-- **(3)** `f = f₁ + f₂ + f₃ + ⋯`, where `fₖ` is the number of faces with `k` sides. -/
theorem numFaces_eq_sum :
    M.numFaces = ∑ k ∈ Finset.range (Fintype.card D + 1),
      Nat.card {x : M.Face // M.sides x = k} := by
  rw [numFaces, Nat.card_eq_fintype_card]
  exact card_eq_sum_range _ _ M.sides_le_card

/-- **(4)** `2e = f₁ + 2 f₂ + 3 f₃ + ⋯`. -/
theorem two_mul_numEdges_eq_sum_sides :
    2 * M.numEdges = ∑ k ∈ Finset.range (Fintype.card D + 1),
      k * Nat.card {x : M.Face // M.sides x = k} := by
  rw [← sum_sides]
  exact sum_eq_sum_range _ _ M.sides_le_card

end Counting

/-! ### Faces have at least three sides -/
/-! ### Small faces -/

theorem nonempty_of_numVertices_pos (h : 0 < M.numVertices) : Nonempty D := by
  unfold numVertices at h
  obtain ⟨v⟩ := (Nat.card_pos_iff.1 h).1
  obtain ⟨d, -⟩ := M.vtx_surjective v
  exact ⟨d⟩


/-- In a map, being in the same connected component is preserved by a set of darts closed under
`σ`, `σ⁻¹` and `α`. -/
theorem mem_iff_of_closed (T : Set D) (hσ : ∀ d ∈ T, M.σ d ∈ T)
    (hσ' : ∀ d ∈ T, M.σ.symm d ∈ T) (hα : ∀ d ∈ T, M.α d ∈ T) {x y : D}
    (h : Relation.EqvGen M.DartRel x y) : (x ∈ T ↔ y ∈ T) := by
  induction h with
  | rel x y hxy =>
    rcases hxy with rfl | rfl
    · exact ⟨hσ x, fun h => by simpa using hσ' _ h⟩
    · exact ⟨hα x, fun h => by simpa [M.α_α] using hα _ h⟩
  | refl => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem le_sides [Fintype D] (d : D) (k : ℕ) (h : ∀ i, 0 < i → i < k → (M.φ ^ i) d ≠ d) :
    k ≤ M.sides (M.face d) := by
  classical
  rw [sides, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpow : ∀ i j, i < j → (M.φ ^ i) d = (M.φ ^ j) d → (M.φ ^ (j - i)) d = d := by
    intro i j hij h'
    have : (M.φ ^ j) d = (M.φ ^ i) ((M.φ ^ (j - i)) d) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
    rw [this] at h'
    exact ((M.φ ^ i).injective h').symm
  have hinj : Set.InjOn (fun i : ℕ => (M.φ ^ i) d) (Finset.range k) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact h (j - i) (by omega) (by omega) (hpow i j hlt hij)
    · exact h (i - j) (by omega) (by omega) (hpow j i hlt hij.symm)
  calc k = ((Finset.range k).image fun i : ℕ => (M.φ ^ i) d).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (M.face_eq_iff).2 (Equiv.Perm.SameCycle.symm ⟨i, by simp⟩)

/-- A simple map has no face with only one side. -/
theorem φ_ne_self (hS : M.Simple) (d : D) : M.φ d ≠ d := by
  intro h
  apply hS.1 d
  rw [← M.vtx_φ, h]

theorem two_le_sides [Fintype D] (hS : M.Simple) (x : M.Face) : 2 ≤ M.sides x := by
  obtain ⟨d, rfl⟩ := M.face_surjective x
  apply M.le_sides d 2
  intro i hi hi2
  interval_cases i
  simpa using M.φ_ne_self hS d

/-- In a simple map, a face with two sides is the face of a component consisting of a single
edge: both darts of that edge are fixed by the rotation `σ`. -/
theorem σ_fixed_of_φ_sq (hS : M.Simple) {d : D} (h : (M.φ ^ 2) d = d) :
    M.σ d = d ∧ M.σ (M.α d) = M.α d := by
  set d₂ := M.φ d with hd₂
  have hφd₂ : M.φ d₂ = d := by rw [hd₂, ← Equiv.Perm.mul_apply, ← pow_two, h]
  -- the edges of `α d` and `d₂` have the same ends, hence coincide
  have h1 : M.α d = d₂ := by
    apply hS.2
    · rw [hd₂, M.vtx_φ]
    · rw [M.α_α, ← M.vtx_φ, hφd₂]
  refine ⟨?_, by rw [← M.φ_apply, ← hd₂, h1]⟩
  have := hφd₂
  rw [M.φ_apply, ← h1, M.α_α] at this
  exact this

theorem φ_sq_of_sides_le_two [Fintype D] (hS : M.Simple) {d : D} (h : M.sides (M.face d) ≤ 2) :
    (M.φ ^ 2) d = d := by
  by_contra h'
  have := M.le_sides d 3 (by
    intro i hi hi3
    interval_cases i
    · simpa using M.φ_ne_self hS d
    · exact h')
  omega

/-- The connected component of a dart `d` with `σ d = d` and `σ (α d) = α d` consists of `d`
and `α d` only. -/
theorem eq_of_eqvGen_of_σ_fixed {d : D} (h1 : M.σ d = d) (h2 : M.σ (M.α d) = M.α d) {d' : D}
    (h : Relation.EqvGen M.DartRel d d') : d' = d ∨ d' = M.α d := by
  have := (M.mem_iff_of_closed {d, M.α d}
    (by rintro t (rfl | rfl) <;> simp [h1, h2])
    (by
      rintro t (rfl | rfl)
      · left; exact (Equiv.symm_apply_eq _).2 h1.symm
      · right; exact (Equiv.symm_apply_eq _).2 h2.symm)
    (by rintro t (rfl | rfl) <;> simp [M.α_α]) h).1 (Set.mem_insert d _)
  simpa using this

/-- If all darts are `d` or `α d`, there are at most two vertices. -/
theorem numVertices_le_two_of_forall {d : D} (hall : ∀ t, t = d ∨ t = M.α d) :
    M.numVertices ≤ 2 := by
  unfold numVertices
  have hsurj : Function.Surjective (fun b : Bool => if b then M.vtx d else M.vtx (M.α d)) := by
    intro v
    obtain ⟨t, rfl⟩ := M.vtx_surjective v
    rcases hall t with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  calc Nat.card M.Vertex ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

/-- In a connected simple map with more than two vertices no face has two sides. -/
theorem φ_sq_ne_self (hS : M.Simple) (hM : M.Connected) (hn : 2 < M.numVertices) (d : D) :
    (M.φ ^ 2) d ≠ d := by
  intro h
  obtain ⟨h1, h2⟩ := M.σ_fixed_of_φ_sq hS h
  have := M.numVertices_le_two_of_forall (fun t => M.eq_of_eqvGen_of_σ_fixed h1 h2 (hM d t))
  omega

/-- The number of faces with at most two sides. -/
noncomputable def numSmallFaces : ℕ := Nat.card {x : M.Face // M.sides x ≤ 2}

/-- In a simple map, distinct faces with at most two sides lie in distinct components. -/
theorem numSmallFaces_le [Fintype D] (hS : M.Simple) : M.numSmallFaces ≤ M.numComponents := by
  unfold numSmallFaces numComponents
  apply Nat.card_le_card_of_injective (fun x => Quot.mk M.DartRel x.1.out)
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only at hxy
  have hxy' := Quot.eqvGen_exact hxy
  have hx' : M.face x.out = x := Quotient.out_eq x
  have hy' : M.face y.out = y := Quotient.out_eq y
  rw [← hx'] at hx
  obtain ⟨h1, h2⟩ := M.σ_fixed_of_φ_sq hS (M.φ_sq_of_sides_le_two hS hx)
  simp only [Subtype.mk.injEq]
  rw [← hx', ← hy']
  rcases M.eq_of_eqvGen_of_σ_fixed h1 h2 hxy' with h | h
  · rw [h]
  · rw [h, ← M.face_φ (M.α _), M.φ_apply, M.α_α, h1]

theorem one_le_numComponents [Finite D] [Nonempty D] : 1 ≤ M.numComponents := by
  unfold numComponents
  have : Nonempty (Quot M.DartRel) := ⟨Quot.mk _ (Classical.arbitrary D)⟩
  exact Nat.card_pos

/-- A connected simple map with a face with at most two sides has at most two vertices. -/
theorem numSmallFaces_eq_zero [Fintype D] (hS : M.Simple)
    (hc : M.numComponents = 1) (hn : 2 < M.numVertices) : M.numSmallFaces = 0 := by
  by_contra h0
  unfold numSmallFaces at h0
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.1 h0).1
  obtain ⟨d, rfl⟩ := M.face_surjective x
  obtain ⟨h1, h2⟩ := M.σ_fixed_of_φ_sq hS (M.φ_sq_of_sides_le_two hS hx)
  have hall : ∀ t, t = d ∨ t = M.α d := by
    intro t
    unfold numComponents at hc
    have : Subsingleton (Quot M.DartRel) := (Nat.card_eq_one_iff_unique.1 hc).1
    exact M.eq_of_eqvGen_of_σ_fixed h1 h2 (Quot.eqvGen_exact (Subsingleton.elim _ _))
  have := M.numVertices_le_two_of_forall hall
  omega

/-- In a connected simple map with more than two vertices every face has at least three
sides. -/
theorem three_le_sides [Fintype D] (hS : M.Simple) (hM : M.Connected) (hn : 2 < M.numVertices)
    (x : M.Face) : 3 ≤ M.sides x := by
  have := M.nonempty_of_numVertices_pos (by omega)
  have h0 := M.numSmallFaces_eq_zero hS (M.numComponents_eq_one hM) hn
  by_contra h
  unfold numSmallFaces at h0
  have : Nonempty {x : M.Face // M.sides x ≤ 2} := ⟨⟨x, by omega⟩⟩
  rw [Nat.card_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact h0.false (Classical.choice this)
  · exact not_finite_iff_infinite.2 h0 inferInstance

/-! ### The Proposition -/

theorem numSmallFaces_eq_sum [Fintype D] :
    M.numSmallFaces = ∑ x : M.Face, if M.sides x ≤ 2 then 1 else 0 := by
  classical
  rw [numSmallFaces, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-- Counting the sides: `3 f ≤ 2 e + (number of faces with at most two sides)`. -/
theorem three_mul_numFaces_le [Fintype D] (hS : M.Simple) :
    3 * M.numFaces ≤ 2 * M.numEdges + M.numSmallFaces := by
  rw [← sum_sides, numSmallFaces_eq_sum, ← Finset.sum_add_distrib, numFaces,
    Nat.card_eq_fintype_card, ← Finset.card_univ, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x _ => ?_
  have := M.two_le_sides hS x
  split_ifs <;> omega

theorem numSmallFaces_le_six_mul [Fintype D] [Nonempty D] (hS : M.Simple)
    (hn : 2 < M.numVertices) : M.numSmallFaces + 6 ≤ 6 * M.numComponents := by
  have h1 := M.numSmallFaces_le hS
  have h2 := M.one_le_numComponents
  by_cases hc : M.numComponents = 1
  · rw [M.numSmallFaces_eq_zero hS hc hn, hc]
  · omega

/-- **Proposition (A).** A simple plane graph with `n > 2` vertices has at most `3n - 6`
edges. -/
theorem numEdges_le [Fintype D] (hP : M.IsPlanar) (hS : M.Simple) (hn : 2 < M.numVertices) :
    M.numEdges ≤ 3 * M.numVertices - 6 := by
  have := M.nonempty_of_numVertices_pos (by omega)
  have hE := M.euler_formula_general hP
  have h3 := M.three_mul_numFaces_le hS
  have h6 := M.numSmallFaces_le_six_mul hS hn
  have : (M.numEdges : ℤ) ≤ 3 * M.numVertices - 6 := by
    have h3' : (3 * M.numFaces : ℤ) ≤ 2 * M.numEdges + M.numSmallFaces := by exact_mod_cast h3
    have h6' : (M.numSmallFaces : ℤ) + 6 ≤ 6 * M.numComponents := by exact_mod_cast h6
    linarith
  omega

/-- **Proposition (B).** A simple plane graph with `n > 2` vertices has a vertex of degree at
most `5`. -/
theorem exists_degree_le_five [Fintype D] (hP : M.IsPlanar) (hS : M.Simple)
    (hn : 2 < M.numVertices) : ∃ v : M.Vertex, M.degree v ≤ 5 := by
  by_contra h
  push Not at h
  have h6 := mul_card_le_of_fiber M.vtx 6 (fun v => h v)
  have hA := M.numEdges_le hP hS hn
  have hv : M.numVertices = Fintype.card M.Vertex := Nat.card_eq_fintype_card
  rw [M.card_darts_eq_two_mul_numEdges, ← hv] at h6
  omega

theorem card_filter_eq_sum_fiber [Fintype D] {X : Type*} [Fintype X] [DecidableEq X] (g : D → X)
    (Q : D → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card = ∑ x : X, (Finset.univ.filter (fun t => g t = x ∧ Q t)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.filter_filter]
  congr 1
  ext t
  simp [and_comm]

theorem bool_ne_iff (a b : Bool) : a ≠ b ↔ ¬ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp

/-- **Proposition (C).** If the edges of a simple plane graph with `n > 2` vertices are coloured
with two colours, then there is a vertex with at most two colour changes in the cyclic order of
the edges around it. -/
theorem exists_colorChanges_le_two [Fintype D] (hP : M.IsPlanar) (hS : M.Simple)
    (hn : 2 < M.numVertices) (col : M.Edge → Bool) :
    ∃ v : M.Vertex, M.colorChanges col v ≤ 2 := by
  classical
  have := M.nonempty_of_numVertices_pos (by omega)
  by_contra hcon
  push Not at hcon
  set χ : D → Prop := fun t => col (M.edgeOf t) = true with hχ
  -- colour changes at a vertex
  have hcv : ∀ v, M.colorChanges col v =
      (Finset.univ.filter (fun d => M.vtx d = v ∧ ¬ (χ d ↔ χ (M.σ d)))).card := by
    intro v
    rw [colorChanges, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine congrArg Finset.card ?_
    ext d
    simp [χ, bool_ne_iff]
  -- at every vertex the number of colour changes is even, hence at least four
  have h4 : ∀ v, 4 ≤ M.colorChanges col v := by
    intro v
    have heven := even_card_changes M.σ (Finset.univ.filter (fun d => M.vtx d = v))
      (by intro t ht; simpa [vtx_σ] using ht) χ
    have heven' : Even (Finset.univ.filter (fun d => M.vtx d = v ∧ ¬ (χ d ↔ χ (M.σ d)))).card := by
      rw [Finset.filter_filter] at heven
      convert heven using 2
      ext t; simp
    have := hcon v
    rw [hcv] at this ⊢
    rcases heven' with ⟨k, hk⟩
    omega
  -- total number of corners with colour changes
  set c := (Finset.univ.filter (fun d => ¬ (χ d ↔ χ (M.σ d)))).card with hc
  have hc1 : 4 * M.numVertices ≤ c := by
    rw [hc, card_filter_eq_sum_fiber M.vtx, numVertices, Nat.card_eq_fintype_card, mul_comm,
      ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun v _ => by rw [← hcv]; exact h4 v
  -- count the same corners face by face: the corner between `α t` and `σ (α t) = φ t` lies on
  -- the face of `t`
  have hc2 : c = (Finset.univ.filter (fun t => ¬ (χ t ↔ χ (M.φ t)))).card := by
    rw [hc]
    apply Finset.card_bij (fun d _ => M.α d)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      simpa [χ, φ_apply, M.α_α, edgeOf_α] using hd
    · intro a _ b _ h; exact M.α.injective h
    · intro t ht
      refine ⟨M.α t, ?_, M.α_α t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      simpa [χ, φ_apply, edgeOf_α] using ht
  -- a face with `k` sides has an even number `≤ k` of corners with colour changes
  have hface : ∀ x : M.Face,
      (Finset.univ.filter (fun t => M.face t = x ∧ ¬ (χ t ↔ χ (M.φ t)))).card + 4 ≤
        2 * M.sides x + 2 * (if M.sides x ≤ 2 then 1 else 0) := by
    intro x
    have heven := even_card_changes M.φ (Finset.univ.filter (fun d => M.face d = x))
      (by intro t ht; simpa [face_φ] using ht) χ
    have heven' : Even
        (Finset.univ.filter (fun t => M.face t = x ∧ ¬ (χ t ↔ χ (M.φ t)))).card := by
      rw [Finset.filter_filter] at heven
      convert heven using 2
      ext t; simp
    have hle : (Finset.univ.filter (fun t => M.face t = x ∧ ¬ (χ t ↔ χ (M.φ t)))).card ≤
        M.sides x := by
      rw [sides, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact Finset.card_le_card (fun t ht => by simp_all)
    have h2 := M.two_le_sides hS x
    rcases heven' with ⟨k, hk⟩
    split_ifs <;> omega
  have hc3 : c + 4 * M.numFaces ≤ 4 * M.numEdges + 2 * M.numSmallFaces := by
    rw [hc2, card_filter_eq_sum_fiber M.face, numFaces, Nat.card_eq_fintype_card,
      ← Finset.card_univ, mul_comm, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib,
      numSmallFaces_eq_sum, Finset.mul_sum]
    calc _ ≤ ∑ x : M.Face, (2 * M.sides x + 2 * (if M.sides x ≤ 2 then 1 else 0)) :=
          Finset.sum_le_sum fun x _ => hface x
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_sides]; ring
  have hE := M.euler_formula_general hP
  have h1 := M.numSmallFaces_le hS
  have h2 := M.one_le_numComponents
  have : (4 * M.numVertices : ℤ) + 4 * M.numFaces ≤ 4 * M.numEdges + 2 * M.numSmallFaces := by
    have : 4 * M.numVertices + 4 * M.numFaces ≤ 4 * M.numEdges + 2 * M.numSmallFaces := by omega
    exact_mod_cast this
  have h1' : (M.numSmallFaces : ℤ) ≤ M.numComponents := by exact_mod_cast h1
  have h2' : (1 : ℤ) ≤ M.numComponents := by exact_mod_cast h2
  linarith

end CombMap

end Chapter13

/-! ════════════════ Part: NonPlanar ════════════════ -/

/-!
# `K₅` and `K₃,₃` are not planar

A finite simple graph is called planar if it is the underlying graph of a simple plane map
(a combinatorial map with the Jordan curve property, see `Chapter13.CombMap.IsPlanar`).
(Graphs with isolated vertices are not covered by this notion, since every vertex of a map
carries a dart; this is irrelevant for `K₅` and `K₃,₃`.)
-/


namespace Chapter13

/-- A simple graph is *planar* if it is (isomorphic to) the underlying graph of a simple plane
map. -/
def IsPlanarGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (D : Type) (_ : Fintype D) (M : CombMap D), M.IsPlanar ∧ M.Simple ∧ Nonempty (M.graph ≃g G)

namespace CombMap

variable {D : Type*} (M : CombMap D)

theorem card_neighbors_le_degree [Finite D] (v : M.Vertex) :
    Nat.card {w // M.graph.Adj v w} ≤ M.degree v := by
  have hd : ∀ w : {w // M.graph.Adj v w}, ∃ d : D, M.vtx d = v ∧ M.vtx (M.α d) = w.1 :=
    fun w => (M.graph_adj.1 w.2).2
  choose f hf using hd
  apply Nat.card_le_card_of_injective (fun w => (⟨f w, (hf w).1⟩ : {d // M.vtx d = v}))
  intro w w' h
  simp only [Subtype.mk.injEq] at h
  apply Subtype.ext
  rw [← (hf w).2, ← (hf w').2, h]

/-- A connected underlying graph gives a connected map. -/
theorem connected_of_graph_connected [Finite D] (h : M.graph.Connected) : M.Connected := by
  intro d d'
  have key : ∀ u v, Relation.ReflTransGen M.graph.Adj u v →
      ∀ d d', M.vtx d = u → M.vtx d' = v → Relation.EqvGen M.DartRel d d' := by
    intro u v huv
    induction huv with
    | refl =>
      intro d d' hd hd'
      exact M.eqvGen_of_sameCycle M.σ M.eqvGen_σ (M.vtx_eq_iff.1 (hd.trans hd'.symm))
    | tail _ hvw ih =>
      intro d d' hd hd'
      obtain ⟨-, t, ht1, ht2⟩ := M.graph_adj.1 hvw
      exact ((ih d t hd ht1).trans _ _ _ (M.eqvGen_α t)).trans _ _ _
        (M.eqvGen_of_sameCycle M.σ M.eqvGen_σ (M.vtx_eq_iff.1 (ht2.trans hd'.symm)))
  exact key _ _ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (h.preconnected _ _)) d d' rfl rfl

end CombMap

open CombMap

/-- **`K₅` is not planar.** -/
theorem not_isPlanarGraph_K5 : ¬ IsPlanarGraph (SimpleGraph.completeGraph (Fin 5)) := by
  rintro ⟨D, _, M, hP, hS, ⟨ψ⟩⟩
  have hn : M.numVertices = 5 := by
    rw [numVertices, Nat.card_congr ψ.toEquiv]; simp
  have hdeg : ∀ v, 4 ≤ M.degree v := by
    intro v
    refine le_trans (le_of_eq ?_) (M.card_neighbors_le_degree v)
    rw [Nat.card_congr (Equiv.subtypeEquiv ψ.toEquiv (fun w => ψ.map_adj_iff.symm)),
      Nat.card_eq_fintype_card]
    have key : ∀ a : Fin 5, Fintype.card {b // (SimpleGraph.completeGraph (Fin 5)).Adj a b} = 4 :=
      by decide
    exact (key _).symm
  have h4 := mul_card_le_of_fiber M.vtx 4 hdeg
  have hv : M.numVertices = Fintype.card M.Vertex := Nat.card_eq_fintype_card
  rw [M.card_darts_eq_two_mul_numEdges, ← hv, hn] at h4
  have hA := M.numEdges_le hP hS (by omega)
  omega

theorem completeBipartite_adj_iff (a b : Fin 3 ⊕ Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b ↔ a.isLeft ≠ b.isLeft := by
  cases a <;> cases b <;> simp [completeBipartiteGraph]

theorem K33_connected : (completeBipartiteGraph (Fin 3) (Fin 3)).Connected := by
  refine SimpleGraph.Connected.mk (fun u v => ?_)
  by_cases h : u.isLeft = v.isLeft
  · set w : Fin 3 ⊕ Fin 3 := if u.isLeft then Sum.inr 0 else Sum.inl 0 with hw
    have hu : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u w := by
      rw [completeBipartite_adj_iff]; cases u <;> simp [w]
    have hv : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj w v := by
      rw [completeBipartite_adj_iff, ← h]; cases u <;> simp [w]
    exact hu.reachable.trans hv.reachable
  · exact ((completeBipartite_adj_iff u v).2 h).reachable

/-- **`K₃,₃` is not planar.** -/
theorem not_isPlanarGraph_K33 : ¬ IsPlanarGraph (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  rintro ⟨D, _, M, hP, hS, ⟨ψ⟩⟩
  classical
  have hn : M.numVertices = 6 := by
    rw [numVertices, Nat.card_congr ψ.toEquiv]; simp
  have hdeg : ∀ v, 3 ≤ M.degree v := by
    intro v
    refine le_trans (le_of_eq ?_) (M.card_neighbors_le_degree v)
    rw [Nat.card_congr (Equiv.subtypeEquiv ψ.toEquiv (fun w => ψ.map_adj_iff.symm)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp_rw [completeBipartite_adj_iff]
    have key : ∀ a : Fin 3 ⊕ Fin 3,
        (Finset.univ.filter (fun u : Fin 3 ⊕ Fin 3 => a.isLeft ≠ u.isLeft)).card = 3 := by decide
    exact (key _).symm
  have h3 := mul_card_le_of_fiber M.vtx 3 hdeg
  have hv : M.numVertices = Fintype.card M.Vertex := Nat.card_eq_fintype_card
  rw [M.card_darts_eq_two_mul_numEdges, ← hv, hn] at h3
  -- the map is connected
  have hconn : M.graph.Connected := by
    rw [ψ.connected_iff]
    exact K33_connected
  have hM := M.connected_of_graph_connected hconn
  have := M.nonempty_of_numVertices_pos (by omega)
  -- every edge joins the two sides
  have hside : ∀ t : D, (ψ (M.vtx t)).isLeft ≠ (ψ (M.vtx (M.α t))).isLeft := by
    intro t
    rw [← completeBipartite_adj_iff, ψ.map_adj_iff]
    exact M.graph_adj.2 ⟨(hS.1 t).symm, t, rfl, rfl⟩
  -- hence all faces have at least four sides
  have hfaces : ∀ x : M.Face, 4 ≤ M.sides x := by
    intro x
    obtain ⟨d, rfl⟩ := M.face_surjective x
    apply M.le_sides d 4
    intro i hi hi4
    interval_cases i
    · simpa using M.φ_ne_self hS d
    · exact M.φ_sq_ne_self hS hM (by omega) d
    · intro h
      have e1 := hside d
      have e2 := hside (M.φ d)
      have e3 := hside ((M.φ ^ 2) d)
      have v1 : M.vtx (M.α d) = M.vtx (M.φ d) := (M.vtx_φ d).symm
      have v2 : M.vtx (M.α (M.φ d)) = M.vtx ((M.φ ^ 2) d) := by
        rw [pow_two, Equiv.Perm.mul_apply, M.vtx_φ]
      have v3 : M.vtx (M.α ((M.φ ^ 2) d)) = M.vtx d := by
        rw [← M.vtx_φ, ← Equiv.Perm.mul_apply, ← pow_succ', h]
      rw [v1] at e1
      rw [v2] at e2
      rw [v3] at e3
      revert e1 e2 e3
      cases (ψ (M.vtx d)).isLeft <;> cases (ψ (M.vtx (M.φ d))).isLeft <;>
        cases (ψ (M.vtx ((M.φ ^ 2) d))).isLeft <;> simp
  have h4 := mul_card_le_of_fiber M.face 4 hfaces
  rw [M.card_darts_eq_two_mul_numEdges] at h4
  have hE := M.euler_formula hP hM
  have hf : M.numFaces = Fintype.card M.Face := Nat.card_eq_fintype_card
  rw [← hf] at h4
  rw [hn] at hE
  omega

end Chapter13

/-! ════════════════ Part: PickEuler ════════════════ -/

/-!
# 3. Pick's theorem: the Euler-formula count of the book

In the book, Pick's theorem is derived from Euler's formula: if a lattice polygon `Q` with
`n_int` interior and `n_bd` boundary lattice points is triangulated into elementary triangles
(using all lattice points of `Q` as vertices), the resulting plane graph has `n = n_int + n_bd`
vertices, `f - 1` triangular inner faces and one outer face bounded by `n_bd` edges, hence

  `f - 1 = 2 n_int + n_bd - 2`,

and since every elementary triangle has area `1/2`, `A(Q) = (f - 1) / 2 = n_int + n_bd / 2 - 1`.

Here we prove this counting step for combinatorial plane maps: for every connected plane map whose
faces, except one distinguished outer face, are triangles,
`f - 1 = 2 (n - s) + s - 2`, where `s` is the number of sides of the outer face.
-/


namespace Chapter13

namespace CombMap

variable {D : Type*} (M : CombMap D)

/-- **The Euler count in the proof of Pick's theorem.**  In a connected plane map all of whose
faces except the outer face are triangles, the number of triangles is `2 n_int + n_bd - 2`, where
`n_bd` is the number of sides of the outer face and `n_int = n - n_bd`. -/
theorem numTriangles_eq [Fintype D] [Nonempty D] (hP : M.IsPlanar) (hM : M.Connected)
    (outer : M.Face) (htri : ∀ x, x ≠ outer → M.sides x = 3) :
    (M.numFaces : ℤ) - 1 =
      2 * ((M.numVertices : ℤ) - M.sides outer) + M.sides outer - 2 := by
  classical
  have he := M.euler_formula hP hM
  have hs := M.sum_sides
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ outer),
    Finset.sum_congr rfl (fun x hx => htri x (Finset.ne_of_mem_erase hx)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul] at hs
  have hf : Fintype.card M.Face = M.numFaces := by
    rw [numFaces, Nat.card_eq_fintype_card]
  rw [hf] at hs
  have hpos : 1 ≤ M.numFaces := by
    rw [← hf]; exact Fintype.card_pos
  have hs' : (M.sides outer : ℤ) + ((M.numFaces : ℤ) - 1) * 3 = 2 * M.numEdges := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hs
    push_cast [Nat.cast_sub hpos] at this
    linarith
  linarith

end CombMap

end Chapter13

/-! ════════════════ Part: PlaneBasics ════════════════ -/

/-!
# Basic analytic geometry in the plane `ℝ × ℝ`

Points of the plane are elements of `ℝ × ℝ`.  Lines through two points are the affine spans
`line[ℝ, a, b]`, and collinearity is Mathlib's `Collinear ℝ`.  We relate these notions to the
cross product `u.1 * v.2 - u.2 * v.1`.
-/


namespace Chapter13

namespace Plane

/-- The cross product (determinant) of two vectors of the plane. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The dot product. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The squared Euclidean norm. -/
def nsq (u : ℝ × ℝ) : ℝ := u.1 ^ 2 + u.2 ^ 2

theorem nsq_pos {u : ℝ × ℝ} (hu : u ≠ 0) : 0 < nsq u := by
  unfold nsq
  rcases u with ⟨x, y⟩
  by_contra h
  apply hu
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  simp [hx, hy]

theorem lineMap_eq (a b : ℝ × ℝ) (r : ℝ) : AffineMap.lineMap a b r = a + r • (b - a) := by
  rw [AffineMap.lineMap_apply]; simp [add_comm]

theorem mem_line_iff_exists (a b c : ℝ × ℝ) :
    c ∈ line[ℝ, a, b] ↔ ∃ r : ℝ, c = a + r • (b - a) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [lineMap_eq]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

/-- If `cross u w = 0` and `u ≠ 0`, then `w` is a multiple of `u`. -/
theorem exists_smul_of_cross_eq_zero {u w : ℝ × ℝ} (hu : u ≠ 0) (h : cross u w = 0) :
    ∃ r : ℝ, w = r • u := by
  rcases u with ⟨u1, u2⟩
  rcases w with ⟨w1, w2⟩
  unfold cross at h
  simp only at h
  by_cases h1 : u1 = 0
  · have h2 : u2 ≠ 0 := by rintro rfl; exact hu (by simp [h1])
    refine ⟨w2 / u2, ?_⟩
    have : w1 = 0 := by
      subst h1
      have : u2 * w1 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h2
      · exact h
    ext <;> simp [h1, this]; field_simp
  · refine ⟨w1 / u1, ?_⟩
    ext
    · simp; field_simp
    · simp; field_simp; linarith

theorem mem_line_iff {a b : ℝ × ℝ} (hab : a ≠ b) (c : ℝ × ℝ) :
    c ∈ line[ℝ, a, b] ↔ cross (b - a) (c - a) = 0 := by
  rw [mem_line_iff_exists]
  constructor
  · rintro ⟨r, rfl⟩
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  · intro h
    have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    obtain ⟨r, hr⟩ := exists_smul_of_cross_eq_zero hu h
    exact ⟨r, by rw [← hr]; abel⟩

/-- A finite set of points not all on a line contains a triple `a ≠ b`, `p` with `p` off the line
`ab`. -/
theorem exists_triple_of_not_collinear {S : Set (ℝ × ℝ)} (hS : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ p ∈ S, a ≠ b ∧ cross (b - a) (p - a) ≠ 0 := by
  by_contra h
  push Not at h
  apply hS
  by_cases hne : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hne
    rw [collinear_iff_of_mem ha]
    refine ⟨b - a, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := exists_smul_of_cross_eq_zero (sub_ne_zero.2 hab.symm) (h a ha b hb p hp hab)
    exact ⟨r, by rw [← hr, vadd_eq_add]; abel⟩
  · push Not at hne
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact collinear_empty ℝ (ℝ × ℝ)
    · have : S = {a} := Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => hne b hb a ha⟩
      rw [this]; exact collinear_singleton ℝ a

end Plane

end Chapter13

/-! ════════════════ Part: SylvesterGallai ════════════════ -/

/-!
# 1. The Sylvester–Gallai theorem

**Theorem.** Given any set of `n ≥ 3` points in the plane, not all on one line, there is always a
line that contains exactly two of the points.

The book derives this from part (B) of the Proposition, after transferring the problem to an
arrangement of great circles on the sphere.  Making that topological transfer rigorous would
require realizing the arrangement as a plane graph; instead we give a complete proof via
L. M. Kelly's classical argument (the one presented in Chapter 11 of the book): among all pairs of
a point `p` and a connecting line `ℓ` not through `p`, choose one with minimal distance; then
`ℓ` contains exactly two points.
-/


namespace Chapter13

open Plane

/-- squared distance from `p` to the line `ab`, as an algebraic expression -/
noncomputable def sqDist (p a b : ℝ × ℝ) : ℝ := cross (b - a) (p - a) ^ 2 / nsq (b - a)

/-- Among three distinct reals, two lie (weakly) on the same side of `τ`, the first one closer
to `τ`. -/
theorem exists_same_side (τ r₁ r₂ r₃ : ℝ) (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃) :
    ∃ s t : ℝ, s ≠ t ∧ (s = r₁ ∨ s = r₂ ∨ s = r₃) ∧ (t = r₁ ∨ t = r₂ ∨ t = r₃) ∧
      0 ≤ (s - τ) * (t - τ) ∧ |s - τ| ≤ |t - τ| := by
  have pick : ∀ x y : ℝ, x ≠ y → 0 ≤ (x - τ) * (y - τ) →
      ∃ s t : ℝ, s ≠ t ∧ ((s = x ∧ t = y) ∨ (s = y ∧ t = x)) ∧
        0 ≤ (s - τ) * (t - τ) ∧ |s - τ| ≤ |t - τ| := by
    intro x y hxy hs
    rcases le_total |x - τ| |y - τ| with h | h
    · exact ⟨x, y, hxy, Or.inl ⟨rfl, rfl⟩, hs, h⟩
    · exact ⟨y, x, hxy.symm, Or.inr ⟨rfl, rfl⟩, by linarith [mul_comm (x - τ) (y - τ)], h⟩
  have same : ∀ x y : ℝ, (0 ≤ x - τ ↔ 0 ≤ y - τ) → 0 ≤ (x - τ) * (y - τ) := by
    intro x y hxy
    by_cases hx : 0 ≤ x - τ
    · exact mul_nonneg hx (hxy.1 hx)
    · have hy : ¬ 0 ≤ y - τ := fun h => hx (hxy.2 h)
      push Not at hx hy
      exact (mul_pos_of_neg_of_neg hx hy).le
  by_cases h₁₂ : (0 ≤ r₁ - τ ↔ 0 ≤ r₂ - τ)
  · obtain ⟨s, t, hst, hc, h1, h2⟩ := pick r₁ r₂ h12 (same _ _ h₁₂)
    refine ⟨s, t, hst, ?_, ?_, h1, h2⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · by_cases h₁₃ : (0 ≤ r₁ - τ ↔ 0 ≤ r₃ - τ)
    · obtain ⟨s, t, hst, hc, h1, h2⟩ := pick r₁ r₃ h13 (same _ _ h₁₃)
      refine ⟨s, t, hst, ?_, ?_, h1, h2⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · have h₂₃ : (0 ≤ r₂ - τ ↔ 0 ≤ r₃ - τ) := by tauto
      obtain ⟨s, t, hst, hc, h1, h2⟩ := pick r₂ r₃ h23 (same _ _ h₂₃)
      refine ⟨s, t, hst, ?_, ?_, h1, h2⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Kelly's key step: if `x`, `y` are points of the line `ab` lying on the same side of the foot
of the perpendicular from `p`, with `x` closer to the foot, then `x` is closer to the line `py`
than `p` is to the line `ab`. -/
theorem kelly_step {p a b : ℝ × ℝ} (hab : a ≠ b) (hp : cross (b - a) (p - a) ≠ 0) (s t : ℝ)
    (hst : s ≠ t)
    (hside : 0 ≤ (s - dot (p - a) (b - a) / nsq (b - a)) * (t - dot (p - a) (b - a) / nsq (b - a)))
    (hcl : |s - dot (p - a) (b - a) / nsq (b - a)| ≤ |t - dot (p - a) (b - a) / nsq (b - a)|) :
    cross ((a + t • (b - a)) - p) ((a + s • (b - a)) - p) ≠ 0 ∧
      sqDist (a + s • (b - a)) p (a + t • (b - a)) < sqDist p a b := by
  set u := b - a with hu
  have hN : 0 < nsq u := nsq_pos (sub_ne_zero.2 hab.symm)
  set N := nsq u with hNdef
  set κ := cross u (p - a) with hκ
  set τ := dot (p - a) u / N with hτ
  have hcross : cross ((a + t • u) - p) ((a + s • u) - p) = (s - t) * κ := by
    simp only [hκ, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have hnorm : nsq ((a + t • u) - p) = (t - τ) ^ 2 * N + κ ^ 2 / N := by
    rw [hτ, hκ]
    simp only [hNdef, nsq, cross, dot, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hN ⊢
    field_simp
    ring
  refine ⟨by rw [hcross]; exact mul_ne_zero (sub_ne_zero.2 hst) hp, ?_⟩
  unfold sqDist
  rw [hcross, hnorm]
  change ((s - t) * κ) ^ 2 / ((t - τ) ^ 2 * N + κ ^ 2 / N) < κ ^ 2 / N
  -- reduce to a real inequality
  have hkey : (s - t) ^ 2 ≤ (t - τ) ^ 2 := by
    have h1 : (s - τ) * (t - τ) = |s - τ| * |t - τ| := by
      rw [← abs_mul, abs_of_nonneg hside]
    have h2 : |s - τ| ^ 2 ≤ |s - τ| * |t - τ| :=
      by nlinarith [abs_nonneg (s - τ), abs_nonneg (t - τ)]
    have h3 : (s - τ) ^ 2 = |s - τ| ^ 2 := (sq_abs _).symm
    have h4 : (t - τ) ^ 2 = |t - τ| ^ 2 := (sq_abs _).symm
    nlinarith
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hden : 0 < (t - τ) ^ 2 * N + κ ^ 2 / N := by positivity
  rw [mul_pow, div_lt_div_iff₀ hden hN]
  have : κ ^ 2 * (κ ^ 2 / N) > 0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hkey hκ2.le, mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hkey hκ2.le) hN.le]

/-- **The Sylvester–Gallai theorem.** Given any finite set of points in the plane, not all on one
line, there is always a line that contains exactly two of the points. -/
theorem sylvester_gallai (S : Finset (ℝ × ℝ)) (hS : ¬ Collinear ℝ (S : Set (ℝ × ℝ))) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ c ∈ S, c ∈ line[ℝ, a, b] → c = a ∨ c = b := by
  classical
  -- the finite set of point-line pairs with the point off the line
  set T := (S ×ˢ S ×ˢ S).filter
    (fun x : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) => x.2.1 ≠ x.2.2 ∧ cross (x.2.2 - x.2.1) (x.1 - x.2.1) ≠ 0)
  have hT : T.Nonempty := by
    obtain ⟨a, ha, b, hb, p, hp, hab, hc⟩ := exists_triple_of_not_collinear hS
    exact ⟨(p, a, b), Finset.mem_filter.2 ⟨by simp only [Finset.mem_product]; exact
      ⟨Finset.mem_coe.1 hp, Finset.mem_coe.1 ha, Finset.mem_coe.1 hb⟩, hab, hc⟩⟩
  obtain ⟨⟨p, a, b⟩, hmem, hmin⟩ := T.exists_min_image (fun x => sqDist x.1 x.2.1 x.2.2) hT
  simp only [T, Finset.mem_filter, Finset.mem_product] at hmem
  obtain ⟨⟨hp, ha, hb⟩, hab, hpab⟩ := hmem
  refine ⟨a, ha, b, hb, hab, fun c hc hcl => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨γ, rfl⟩ := (mem_line_iff_exists a b c).1 hcl
  have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hγ0 : γ ≠ 0 := by rintro rfl; exact hne.1 (by simp)
  have hγ1 : γ ≠ 1 := by rintro rfl; exact hne.2 (by simp)
  set τ := dot (p - a) (b - a) / nsq (b - a)
  obtain ⟨s, t, hst, hs, ht, hside, hcl'⟩ :=
    exists_same_side τ 0 1 γ zero_ne_one hγ0.symm hγ1.symm
  -- the points with parameters `0`, `1`, `γ` are `a`, `b`, `c`
  have hpt : ∀ r, (r = 0 ∨ r = 1 ∨ r = γ) → a + r • (b - a) ∈ S := by
    rintro r (rfl | rfl | rfl)
    · simpa using ha
    · simpa using hb
    · exact hc
  obtain ⟨hcr, hlt⟩ := kelly_step hab hpab s t hst hside hcl'
  have hyp : p ≠ a + t • (b - a) := by
    intro h
    apply hpab
    rw [h]
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  have := hmin (a + s • (b - a), p, a + t • (b - a))
    (Finset.mem_filter.2 ⟨by simp [hpt s hs, hpt t ht, hp], hyp, hcr⟩)
  simp only at this
  linarith

end Chapter13

/-! ════════════════ Part: PickLemma ════════════════ -/

/-!
# 3. Pick's theorem: elementary triangles and lattice bases

* the box *Lattice bases*: every basis of `ℤ²` has determinant `±1`, all basis parallelograms have
  the same area `1`;
* the **Lemma**: every elementary lattice triangle has area `1/2`, proved as in the book: the
  parallelogram `P = Δ ∪ σ(Δ)` (with `σ x = p₁ + p₂ - x`) is elementary as well, so the edge
  vectors form a lattice basis; hence `P` has area `1` and `Δ` has area `1/2`.
-/


namespace Chapter13

open MeasureTheory Plane

-- Make the product Haar measure instance explicit for `volume` on `ℝ × ℝ`.
local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- A lattice point of the plane: a point with integer coordinates. -/
def IsLatticePoint (p : ℝ × ℝ) : Prop := ∃ m n : ℤ, p = ((m : ℝ), (n : ℝ))

/-! ### Lattice bases -/

/-- **Lattice bases.** If two integer vectors `e₁ = (a, b)`, `e₂ = (c, d)` generate the lattice
`ℤ²`, then `|det(e₁, e₂)| = 1`. -/
theorem lattice_basis_det (e₁ e₂ : ℤ × ℤ)
    (h : ∀ z : ℤ × ℤ, ∃ l₁ l₂ : ℤ, z = l₁ • e₁ + l₂ • e₂) :
    |e₁.1 * e₂.2 - e₁.2 * e₂.1| = 1 := by
  obtain ⟨a, b, hab⟩ := h (1, 0)
  obtain ⟨c, d, hcd⟩ := h (0, 1)
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hab hcd
  have key : (e₁.1 * e₂.2 - e₁.2 * e₂.1) * (a * d - b * c) =
      (a * e₁.1 + b * e₂.1) * (c * e₁.2 + d * e₂.2) -
        (c * e₁.1 + d * e₂.1) * (a * e₁.2 + b * e₂.2) := by ring
  rw [← hab.1, ← hab.2, ← hcd.1, ← hcd.2] at key
  norm_num at key
  rcases Int.eq_one_or_neg_one_of_mul_eq_one key with h1 | h1 <;> simp [h1]

/-! ### Areas of parallelograms and triangles -/

/-- The linear map `(s, t) ↦ s • v₁ + t • v₂`. -/
noncomputable def linComb (v₁ v₂ : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight v₁ + (LinearMap.snd ℝ ℝ ℝ).smulRight v₂

theorem linComb_apply (v₁ v₂ x : ℝ × ℝ) : linComb v₁ v₂ x = x.1 • v₁ + x.2 • v₂ := rfl

theorem det_linComb (v₁ v₂ : ℝ × ℝ) : LinearMap.det (linComb v₁ v₂) = cross v₁ v₂ := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, linComb, Module.Basis.finTwoProd, cross]
  ring

/-- The parallelogram with corner `p₀` spanned by `v₁` and `v₂`. -/
def parallelogram (p₀ v₁ v₂ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p₀ + s • v₁ + t • v₂}

theorem volume_image_add (p₀ : ℝ × ℝ) (A : Set (ℝ × ℝ)) :
    volume ((fun x => p₀ + x) '' A) = volume A := by
  rw [Set.image_add_left, measure_preimage_add]

theorem parallelogram_eq_image (p₀ v₁ v₂ : ℝ × ℝ) :
    parallelogram p₀ v₁ v₂ =
      (fun x => p₀ + x) '' (linComb v₁ v₂ '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  ext x
  simp only [parallelogram, ch13_mem_setOf, Set.mem_image, Set.mem_prod, linComb_apply]
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    exact ⟨s • v₁ + t • v₂, ⟨(s, t), ⟨hs, ht⟩, rfl⟩, by abel⟩
  · rintro ⟨y, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, by simp only; abel⟩

/-- The area of a parallelogram is the absolute value of the determinant of its edge vectors. -/
theorem volume_parallelogram (p₀ v₁ v₂ : ℝ × ℝ) :
    volume (parallelogram p₀ v₁ v₂) = ENNReal.ofReal |cross v₁ v₂| := by
  rw [parallelogram_eq_image, volume_image_add, Measure.addHaar_image_linearMap, det_linComb,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The triangle with corner `p₀` and edge vectors `v₁`, `v₂`, described by coordinates. -/
def triangleSet (p₀ v₁ v₂ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ x = p₀ + s • v₁ + t • v₂}

theorem convexHull_triple (p₀ p₁ p₂ : ℝ × ℝ) :
    convexHull ℝ {p₀, p₁, p₂} = triangleSet p₀ (p₁ - p₀) (p₂ - p₀) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp⟩
      · exact ⟨1, 0, zero_le_one, le_rfl, by norm_num, by simp⟩
      · exact ⟨0, 1, le_rfl, zero_le_one, by norm_num, by simp⟩
    · rintro x ⟨s, t, hs, ht, hst, rfl⟩ y ⟨s', t', hs', ht', hst', rfl⟩ a b ha hb hab
      refine ⟨a * s + b * s', a * t + b * t', by positivity, by positivity, ?_, ?_⟩
      · nlinarith
      · ext <;> simp <;> first
          | linear_combination (p₀.1) * hab | linear_combination (p₀.2) * hab
  · rintro x ⟨s, t, hs, ht, hst, rfl⟩
    have hc := convex_convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ))
    have h0 : p₀ ∈ convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    have h1 : p₁ ∈ convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    have h2 : p₂ ∈ convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) := subset_convexHull ℝ _ (by simp)
    by_cases h : s + t = 0
    · have hs0 : s = 0 := by linarith
      have ht0 : t = 0 := by linarith
      simpa [hs0, ht0] using h0
    · have hpos : 0 < s + t := lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hq := hc.add_smul_sub_mem h1 h2 (t := t / (s + t))
        ⟨by positivity, by rw [div_le_one hpos]; linarith⟩
      have hx := hc.add_smul_sub_mem h0 hq (t := s + t) ⟨hpos.le, hst⟩
      convert hx using 1
      ext <;> simp <;> field_simp <;> ring

theorem coeff_unique {v₁ v₂ : ℝ × ℝ} (hD : cross v₁ v₂ ≠ 0) {s t s' t' : ℝ}
    (h : s • v₁ + t • v₂ = s' • v₁ + t' • v₂) : s = s' ∧ t = t' := by
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have h1 : (s - s') * cross v₁ v₂ = 0 := by
    unfold cross; linear_combination v₂.2 * e1 - v₂.1 * e2
  have h2 : (t - t') * cross v₁ v₂ = 0 := by
    unfold cross; linear_combination v₁.1 * e2 - v₁.2 * e1
  exact ⟨by simpa [sub_eq_zero, hD] using h1, by simpa [sub_eq_zero, hD] using h2⟩

theorem det_neg_id : LinearMap.det (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd]

/-- The area of a (non-degenerate) triangle is half the absolute value of the determinant of its
edge vectors.  Proof as in the book: the triangle and its image under the point reflection
`σ x = p₁ + p₂ - x` tile the parallelogram with corners `p₀, p₁, p₂, p₁ + p₂ - p₀`. -/
theorem volume_triangle (p₀ p₁ p₂ : ℝ × ℝ) (hD : cross (p₁ - p₀) (p₂ - p₀) ≠ 0) :
    volume (convexHull ℝ {p₀, p₁, p₂}) = ENNReal.ofReal (|cross (p₁ - p₀) (p₂ - p₀)| / 2) := by
  set v₁ := p₁ - p₀ with hv₁
  set v₂ := p₂ - p₀ with hv₂
  set Δ := convexHull ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) with hΔdef
  have hΔ : Δ = triangleSet p₀ v₁ v₂ := convexHull_triple p₀ p₁ p₂
  set σ : ℝ × ℝ → ℝ × ℝ := fun x => (p₁ + p₂) - x with hσ
  have hcomp : IsCompact Δ := by
    rw [hΔdef]
    apply Set.Finite.isCompact_convexHull
    exact Set.toFinite _
  have hmeas : MeasurableSet (σ '' Δ) :=
    (hcomp.image (by fun_prop)).isClosed.measurableSet
  -- the reflection preserves areas
  have hvolσ : volume (σ '' Δ) = volume Δ := by
    have : σ '' Δ = (fun x => (p₁ + p₂) + x) '' ((-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) '' Δ) := by
      rw [Set.image_image]; rfl
    rw [this, volume_image_add, Measure.addHaar_image_linearMap, det_neg_id]
    simp
  -- coordinates of the reflected points
  have hσc : ∀ s t : ℝ, σ (p₀ + s • v₁ + t • v₂) = p₀ + (1 - s) • v₁ + (1 - t) • v₂ := by
    intro s t
    simp only [hσ, hv₁, hv₂]
    ext <;> simp <;> ring
  -- the triangle and its reflection tile the parallelogram
  have hunion : Δ ∪ σ '' Δ = parallelogram p₀ v₁ v₂ := by
    rw [hΔ]
    ext x
    simp only [Set.mem_union, Set.mem_image, triangleSet, parallelogram, ch13_mem_setOf,
      Set.mem_Icc]
    constructor
    · rintro (⟨s, t, hs, ht, hst, rfl⟩ | ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩)
      · exact ⟨s, t, ⟨hs, by linarith⟩, ⟨ht, by linarith⟩, rfl⟩
      · exact ⟨1 - s, 1 - t, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hσc s t⟩
    · rintro ⟨s, t, ⟨hs0, hs1⟩, ⟨ht0, ht1⟩, rfl⟩
      by_cases h : s + t ≤ 1
      · exact Or.inl ⟨s, t, hs0, ht0, h, rfl⟩
      · refine Or.inr ⟨p₀ + (1 - s) • v₁ + (1 - t) • v₂,
          ⟨1 - s, 1 - t, by linarith, by linarith, by linarith, rfl⟩, ?_⟩
        rw [hσc]; simp
  -- they overlap only along the segment `p₁ p₂`
  have hp12 : p₁ ≠ p₂ := by
    rintro rfl; apply hD; simp only [hv₁, hv₂, cross]; ring
  have hinter : Δ ∩ σ '' Δ ⊆ (line[ℝ, p₁, p₂] : Set (ℝ × ℝ)) := by
    rw [hΔ]
    rintro x ⟨⟨s, t, hs, ht, hst, rfl⟩, ⟨y, ⟨s', t', hs', ht', hst', rfl⟩, hxy⟩⟩
    rw [hσc] at hxy
    have hxy' : (1 - s') • v₁ + (1 - t') • v₂ = s • v₁ + t • v₂ := by
      have := congrArg (fun z => z - p₀) hxy
      simp only [add_assoc, add_sub_cancel_left] at this
      exact this
    obtain ⟨e1, e2⟩ := coeff_unique hD hxy'
    have hst1 : s + t = 1 := by linarith
    rw [SetLike.mem_coe, mem_line_iff_exists]
    refine ⟨t, ?_⟩
    have ht' : s = 1 - t := by linarith
    rw [ht']
    simp only [hv₁, hv₂]
    ext <;> simp <;> ring
  have hline : volume (line[ℝ, p₁, p₂] : Set (ℝ × ℝ)) = 0 := by
    apply Measure.addHaar_affineSubspace
    intro htop
    have : p₀ ∈ line[ℝ, p₁, p₂] := by rw [htop]; exact AffineSubspace.mem_top _ _ _
    rw [mem_line_iff hp12] at this
    apply hD
    simp only [hv₁, hv₂, cross, Prod.fst_sub, Prod.snd_sub] at this ⊢
    linarith
  have key := measure_union_add_inter (μ := volume) Δ hmeas
  rw [hunion, measure_mono_null hinter hline, add_zero, hvolσ, volume_parallelogram] at key
  -- solve `ofReal |D| = 2 • vol Δ`
  have hfin : volume Δ ≠ ⊤ := by
    have : volume Δ ≤ volume (parallelogram p₀ v₁ v₂) := by
      rw [← hunion]; exact measure_mono Set.subset_union_left
    rw [volume_parallelogram] at this
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  rw [← ENNReal.ofReal_toReal hfin] at key ⊢
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg] at key
  have := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).1 key
  congr 1
  linarith

/-! ### Elementary triangles -/

/-- A triangle with integral vertices is *elementary* if it is non-degenerate and contains no
lattice points other than its vertices. -/
def IsElementaryTriangle (p₀ p₁ p₂ : ℝ × ℝ) : Prop :=
  IsLatticePoint p₀ ∧ IsLatticePoint p₁ ∧ IsLatticePoint p₂ ∧
    ¬ Collinear ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ)) ∧
    ∀ z, IsLatticePoint z → z ∈ convexHull ℝ {p₀, p₁, p₂} → z = p₀ ∨ z = p₁ ∨ z = p₂

theorem cross_ne_zero_of_not_collinear {p₀ p₁ p₂ : ℝ × ℝ}
    (h : ¬ Collinear ℝ ({p₀, p₁, p₂} : Set (ℝ × ℝ))) : cross (p₁ - p₀) (p₂ - p₀) ≠ 0 := by
  obtain ⟨a, ha, b, hb, p, hp, hab, hc⟩ := exists_triple_of_not_collinear h
  intro hD
  apply hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hp
  unfold cross at hD ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hD ⊢
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hp with rfl | rfl | rfl <;>
    first | ring1 | linear_combination hD | linear_combination -hD

theorem mem_convexHull_triple_iff (p₀ p₁ p₂ : ℝ × ℝ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t ≤ 1) : p₀ + s • (p₁ - p₀) + t • (p₂ - p₀) ∈ convexHull ℝ {p₀, p₁, p₂} := by
  rw [convexHull_triple]; exact ⟨s, t, hs, ht, hst, rfl⟩

/-- If a point `p₀ + s • v₁ + t • v₂` of an elementary triangle is a vertex, then `(s, t)` is
`(0, 0)`, `(1, 0)` or `(0, 1)`. -/
theorem coords_of_vertex {p₀ p₁ p₂ : ℝ × ℝ} (hD : cross (p₁ - p₀) (p₂ - p₀) ≠ 0) {s t : ℝ}
    (h : p₀ + s • (p₁ - p₀) + t • (p₂ - p₀) = p₀ ∨ p₀ + s • (p₁ - p₀) + t • (p₂ - p₀) = p₁ ∨
      p₀ + s • (p₁ - p₀) + t • (p₂ - p₀) = p₂) :
    (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
  rcases h with h | h | h
  · left
    apply coeff_unique hD
    have := congrArg (fun z => z - p₀) h
    simp only [add_assoc, add_sub_cancel_left, sub_self] at this
    simpa using this
  · right; left
    apply coeff_unique hD
    have := congrArg (fun z => z - p₀) h
    simp only [add_assoc, add_sub_cancel_left] at this
    simpa using this
  · right; right
    apply coeff_unique hD
    have := congrArg (fun z => z - p₀) h
    simp only [add_assoc, add_sub_cancel_left] at this
    simpa using this

/-- The edge vectors of an elementary triangle form a basis of the lattice: every lattice vector
has integral coordinates with respect to them. -/
theorem elementary_coords_int {p₀ p₁ p₂ : ℝ × ℝ} (h : IsElementaryTriangle p₀ p₁ p₂)
    (w₁ w₂ : ℤ) :
    (∃ k : ℤ, cross ((w₁ : ℝ), (w₂ : ℝ)) (p₂ - p₀) / cross (p₁ - p₀) (p₂ - p₀) = k) ∧
      (∃ k : ℤ, cross (p₁ - p₀) ((w₁ : ℝ), (w₂ : ℝ)) / cross (p₁ - p₀) (p₂ - p₀) = k) := by
  obtain ⟨⟨m₀, n₀, rfl⟩, ⟨m₁, n₁, rfl⟩, ⟨m₂, n₂, rfl⟩, hnc, hel⟩ := h
  have hD := cross_ne_zero_of_not_collinear hnc
  set D := cross (((m₁ : ℝ), (n₁ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ)))
    (((m₂ : ℝ), (n₂ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) with hDdef
  set a := cross ((w₁ : ℝ), (w₂ : ℝ)) (((m₂ : ℝ), (n₂ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) / D with ha
  set b := cross (((m₁ : ℝ), (n₁ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) ((w₁ : ℝ), (w₂ : ℝ)) / D with hb
  -- Cramer's rule
  have hw1 : (w₁ : ℝ) = a * (m₁ - m₀) + b * (m₂ - m₀) := by
    simp only [ha, hb]
    field_simp
    simp only [hDdef, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hw2 : (w₂ : ℝ) = a * (n₁ - n₀) + b * (n₂ - n₀) := by
    simp only [ha, hb]
    field_simp
    simp only [hDdef, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  set fa := Int.fract a
  set fb := Int.fract b
  have hfa0 : 0 ≤ fa := Int.fract_nonneg a
  have hfa1 : fa < 1 := Int.fract_lt_one a
  have hfb0 : 0 ≤ fb := Int.fract_nonneg b
  have hfb1 : fb < 1 := Int.fract_lt_one b
  have hfa : fa = a - ⌊a⌋ := rfl
  have hfb : fb = b - ⌊b⌋ := rfl
  -- the lattice point `z' = p₀ + fa • v₁ + fb • v₂`
  set M₁ : ℤ := m₀ + w₁ - ⌊a⌋ * (m₁ - m₀) - ⌊b⌋ * (m₂ - m₀)
  set M₂ : ℤ := n₀ + w₂ - ⌊a⌋ * (n₁ - n₀) - ⌊b⌋ * (n₂ - n₀)
  have hz' : ((m₀ : ℝ), (n₀ : ℝ)) + fa • (((m₁ : ℝ), (n₁ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) +
      fb • (((m₂ : ℝ), (n₂ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) = ((M₁ : ℝ), (M₂ : ℝ)) := by
    ext
    · simp only [M₁, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, hfa, hfb]
      push_cast
      linear_combination (-1 : ℝ) * hw1
    · simp only [M₂, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, hfa, hfb]
      push_cast
      linear_combination (-1 : ℝ) * hw2
  have hfrac : fa = 0 ∧ fb = 0 := by
    by_cases hsum : fa + fb ≤ 1
    · have hmem := mem_convexHull_triple_iff ((m₀ : ℝ), (n₀ : ℝ)) ((m₁ : ℝ), (n₁ : ℝ))
        ((m₂ : ℝ), (n₂ : ℝ)) fa fb hfa0 hfb0 hsum
      rw [hz'] at hmem
      have hv := hel _ ⟨M₁, M₂, rfl⟩ hmem
      rw [← hz'] at hv
      rcases coords_of_vertex hD hv with h | h | h
      · exact h
      · linarith [h.1]
      · linarith [h.2]
    · exfalso
      push Not at hsum
      have hmem := mem_convexHull_triple_iff ((m₀ : ℝ), (n₀ : ℝ)) ((m₁ : ℝ), (n₁ : ℝ))
        ((m₂ : ℝ), (n₂ : ℝ)) (1 - fa) (1 - fb) (by linarith) (by linarith) (by linarith)
      have hz'' : ((m₀ : ℝ), (n₀ : ℝ)) + (1 - fa) • (((m₁ : ℝ), (n₁ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) +
          (1 - fb) • (((m₂ : ℝ), (n₂ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) =
          (((m₁ + m₂ - M₁ : ℤ) : ℝ), ((n₁ + n₂ - M₂ : ℤ) : ℝ)) := by
        have e1 := congrArg Prod.fst hz'
        have e2 := congrArg Prod.snd hz'
        simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, Prod.snd_add,
          Prod.smul_snd, Prod.snd_sub] at e1 e2
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          push_cast
          linear_combination (-1 : ℝ) * e1
        · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          push_cast
          linear_combination (-1 : ℝ) * e2
      rw [hz''] at hmem
      have hv := hel _ ⟨_, _, rfl⟩ hmem
      rw [← hz''] at hv
      rcases coords_of_vertex hD hv with h | h | h
      · linarith [h.1]
      · linarith [h.2]
      · linarith [h.1]
  refine ⟨⟨⌊a⌋, ?_⟩, ⟨⌊b⌋, ?_⟩⟩
  · linarith [hfrac.1, Int.floor_add_fract a]
  · linarith [hfrac.2, Int.floor_add_fract b]

/-- The edge vectors of an elementary triangle have determinant `±1`. -/
theorem elementary_abs_cross {p₀ p₁ p₂ : ℝ × ℝ} (h : IsElementaryTriangle p₀ p₁ p₂) :
    |cross (p₁ - p₀) (p₂ - p₀)| = 1 := by
  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := elementary_coords_int h 1 0
  obtain ⟨⟨k₃, hk₃⟩, ⟨k₄, hk₄⟩⟩ := elementary_coords_int h 0 1
  have hD := cross_ne_zero_of_not_collinear h.2.2.2.1
  obtain ⟨⟨m₀, n₀, rfl⟩, ⟨m₁, n₁, rfl⟩, ⟨m₂, n₂, rfl⟩, -, -⟩ := h
  set D := cross (((m₁ : ℝ), (n₁ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ)))
    (((m₂ : ℝ), (n₂ : ℝ)) - ((m₀ : ℝ), (n₀ : ℝ))) with hDdef
  rw [div_eq_iff hD] at hk₁ hk₂ hk₃ hk₄
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at hk₁ hk₂ hk₃ hk₄
  push_cast at hk₁ hk₂ hk₃ hk₄
  -- `D = D² (k₄ k₁ - k₂ k₃)`, hence `D (k₄ k₁ - k₂ k₃) = 1`
  have hDeq : D = (m₁ - m₀ : ℝ) * (n₂ - n₀) - (n₁ - n₀) * (m₂ - m₀) := by
    simp [hDdef, cross]
  have h1 : D * (D * (k₄ * k₁ - k₂ * k₃)) = D * 1 := by
    linear_combination (-(k₄ * D)) * hk₁ + (-((n₂ : ℝ) - n₀)) * hk₄ + (k₃ * D) * hk₂ +
      (-((n₁ : ℝ) - n₀)) * hk₃ - hDeq
  have h2 : D * (k₄ * k₁ - k₂ * k₃) = 1 := mul_left_cancel₀ hD h1
  have h3 : ((m₁ - m₀) * (n₂ - n₀) - (n₁ - n₀) * (m₂ - m₀)) * (k₄ * k₁ - k₂ * k₃) = (1 : ℤ) := by
    rw [hDeq] at h2
    exact_mod_cast h2
  rw [hDeq]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h3 with h4 | h4
  · have : ((m₁ : ℝ) - m₀) * (n₂ - n₀) - (n₁ - n₀) * (m₂ - m₀) = 1 := by exact_mod_cast h4
    rw [this]; simp
  · have : ((m₁ : ℝ) - m₀) * (n₂ - n₀) - (n₁ - n₀) * (m₂ - m₀) = -1 := by exact_mod_cast h4
    rw [this]; simp

/-- **Lemma (Pick).** Every elementary triangle `Δ = conv {p₀, p₁, p₂}` has area `A(Δ) = 1/2`. -/
theorem area_elementary_triangle {p₀ p₁ p₂ : ℝ × ℝ} (h : IsElementaryTriangle p₀ p₁ p₂) :
    volume (convexHull ℝ {p₀, p₁, p₂}) = ENNReal.ofReal (1 / 2) := by
  rw [volume_triangle p₀ p₁ p₂ (cross_ne_zero_of_not_collinear h.2.2.2.1),
    elementary_abs_cross h]


end Chapter13

/-! ════════════════ Part: PickSign ════════════════ -/

/-!
# Sign bookkeeping for Pick's theorem

For a point `y` and a lattice triangle, the *Pick weight* of `y` is `2` if `y` lies in the
interior of the triangle, `1` if `y` lies on the boundary but is not a vertex, and `0` otherwise.
It only depends on the signs of the three barycentric determinants of `y`.  The finite sign
identities below (checked by `decide`) are what makes the weight additive when a triangle is
split into smaller triangles.
-/


namespace Chapter13

namespace PickSign

/-- `1` for a positive sign, `0` otherwise. -/
def posC (a : SignType) : ℤ := if a = 1 then 1 else 0

/-- The Pick weight as a function of the signs of the three barycentric determinants. -/
def G (a b c : SignType) : ℤ :=
  if a ≠ -1 ∧ b ≠ -1 ∧ c ≠ -1 then posC a + posC b + posC c - 1 else 0

/-- The sign information carried by `c₁ X₁ + c₂ X₂ + c₃ X₃ = 0` with all `cᵢ > 0`. -/
def SRel (a b c : SignType) : Prop :=
  ¬ (a ≠ -1 ∧ b ≠ -1 ∧ c ≠ -1 ∧ (a = 1 ∨ b = 1 ∨ c = 1)) ∧
  ¬ (a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ (a = -1 ∨ b = -1 ∨ c = -1))

instance (a b c : SignType) : Decidable (SRel a b c) := by unfold SRel; infer_instance

theorem G_rot (a b c : SignType) : G b c a = G a b c := by
  revert a b c; decide

theorem G_swap (a b c : SignType) : G a c b = G a b c := by
  revert a b c; decide

/-- Splitting a triangle at an interior point. -/
theorem key_interior : ∀ p q r u v w : SignType,
    (p = 1 ∨ q = 1 ∨ r = 1) →
    SRel q (-p) (-u) → SRel r (-q) (-v) → SRel p (-r) (-w) → SRel u v w →
    G p q r = G p u (-w) + G (-u) q v + G w (-v) r +
      2 * (if u = 0 ∧ v = 0 ∧ w = 0 then 1 else 0) := by
  decide

theorem closed_interior₁ : ∀ p q r u v w : SignType,
    SRel q (-p) (-u) → SRel r (-q) (-v) → SRel p (-r) (-w) → SRel u v w →
    (p ≠ -1 ∧ u ≠ -1 ∧ -w ≠ -1) → p ≠ -1 ∧ q ≠ -1 ∧ r ≠ -1 := by
  decide

theorem closed_interior₂ : ∀ p q r u v w : SignType,
    SRel q (-p) (-u) → SRel r (-q) (-v) → SRel p (-r) (-w) → SRel u v w →
    (q ≠ -1 ∧ v ≠ -1 ∧ -u ≠ -1) → p ≠ -1 ∧ q ≠ -1 ∧ r ≠ -1 := by
  decide

theorem closed_interior₃ : ∀ p q r u v w : SignType,
    SRel q (-p) (-u) → SRel r (-q) (-v) → SRel p (-r) (-w) → SRel u v w →
    (w ≠ -1 ∧ -v ≠ -1 ∧ r ≠ -1) → p ≠ -1 ∧ q ≠ -1 ∧ r ≠ -1 := by
  decide

/-- Splitting a triangle at a point of the edge opposite to the first vertex. -/
theorem key_edge : ∀ p q r t : SignType,
    (p = 1 ∨ q = 1 ∨ r = 1) → SRel r (-q) (-t) →
    G p q r = G p (-t) r + G p q t + (if p = 0 ∧ t = 0 then 1 else 0) := by
  decide

theorem closed_edge₁ : ∀ p q r t : SignType, SRel r (-q) (-t) →
    (p ≠ -1 ∧ -t ≠ -1 ∧ r ≠ -1) → p ≠ -1 ∧ q ≠ -1 ∧ r ≠ -1 := by
  decide

theorem closed_edge₂ : ∀ p q r t : SignType, SRel r (-q) (-t) →
    (p ≠ -1 ∧ q ≠ -1 ∧ t ≠ -1) → p ≠ -1 ∧ q ≠ -1 ∧ r ≠ -1 := by
  decide

/-- The weight of a vertex is `0`. -/
theorem G_vertex : G 1 0 0 = 0 := by decide

/-- Value of the weight: `2` inside, `1` on the boundary away from the vertices,
`0` at the vertices and outside. -/
theorem G_eq (a b c : SignType) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    G a b c = 2 * (if a = 1 ∧ b = 1 ∧ c = 1 then 1 else 0) +
      (if (a ≠ -1 ∧ b ≠ -1 ∧ c ≠ -1) ∧ ¬ (a = 1 ∧ b = 1 ∧ c = 1) then 1 else 0) -
      (if (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1)
        then 1 else 0) := by
  revert a b c; decide

theorem srel_of_eq {c₁ c₂ c₃ x₁ x₂ x₃ : ℤ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₃ : 0 < c₃)
    (h : c₁ * x₁ + c₂ * x₂ + c₃ * x₃ = 0) :
    SRel (SignType.sign x₁) (SignType.sign x₂) (SignType.sign x₃) := by
  have hs : ∀ x : ℤ, (SignType.sign x = 1 ∧ 0 < x) ∨ (SignType.sign x = 0 ∧ x = 0) ∨
      (SignType.sign x = -1 ∧ x < 0) := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exact Or.inr (Or.inr ⟨sign_neg hx, hx⟩)
    · exact Or.inr (Or.inl ⟨by simp [hx], hx⟩)
    · exact Or.inl ⟨sign_pos hx, hx⟩
  rcases hs x₁ with ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ | ⟨e₁, f₁⟩ <;>
  rcases hs x₂ with ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ | ⟨e₂, f₂⟩ <;>
  rcases hs x₃ with ⟨e₃, f₃⟩ | ⟨e₃, f₃⟩ | ⟨e₃, f₃⟩ <;>
  rw [e₁, e₂, e₃] <;>
  first
  | decide
  | (exfalso; subst_vars; nlinarith)

end PickSign

end Chapter13

/-! ════════════════ Part: PickTriangle ════════════════ -/

/-!
# Pick's theorem for lattice triangles: the counting identity

For a lattice triangle `a b c` (vertices in `ℤ²`, determinant `D ≠ 0`) we attach to every lattice
point `y` its *Pick weight*: `2` if `y` is an interior point, `1` if `y` is a boundary point that is
not a vertex, `0` otherwise.  We prove

  `∑ y, weight y = |D| - 1`,

by strong induction on `|D|`: if the triangle contains a lattice point other than its vertices we
split it into two or three smaller lattice triangles (the weights add up, up to a correction at the
splitting point), and otherwise the triangle is elementary and `|D| = 1` by the Lemma of the book.
Since `2 · area = |D|`, this is Pick's formula `area = n_int + n_bd / 2 - 1`.
-/


namespace Chapter13

namespace PickInt

open PickSign Plane

/-- Integer cross product. -/
def crossZ (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- The (doubled, oriented) area of the lattice triangle `a b c`. -/
def det (a b c : ℤ × ℤ) : ℤ := crossZ (b - a) (c - a)

/-- Barycentric determinants of a point `y` with respect to the triangle `a b c`. -/
def bA (_a b c y : ℤ × ℤ) : ℤ := crossZ (b - y) (c - y)
/-- Barycentric determinants of a point `y` with respect to the triangle `a b c`. -/
def bB (a _b c y : ℤ × ℤ) : ℤ := crossZ (c - y) (a - y)
/-- Barycentric determinants of a point `y` with respect to the triangle `a b c`. -/
def bC (a b _c y : ℤ × ℤ) : ℤ := crossZ (a - y) (b - y)

/-- The Pick weight of `y` with respect to the triangle `a b c`. -/
def wt (a b c y : ℤ × ℤ) : ℤ :=
  G (SignType.sign (det a b c * bA a b c y)) (SignType.sign (det a b c * bB a b c y))
    (SignType.sign (det a b c * bC a b c y))

/-- `y` lies in the closed triangle `a b c`. -/
def InTri (a b c y : ℤ × ℤ) : Prop :=
  0 ≤ det a b c * bA a b c y ∧ 0 ≤ det a b c * bB a b c y ∧ 0 ≤ det a b c * bC a b c y

/-- `y` lies in the open triangle `a b c`. -/
def InTriStrict (a b c y : ℤ × ℤ) : Prop :=
  0 < det a b c * bA a b c y ∧ 0 < det a b c * bB a b c y ∧ 0 < det a b c * bC a b c y

/-- Expand the integer triangle determinants and normalize the resulting polynomial identity. -/
macro "pickRing" : tactic =>
  `(tactic| (simp only [det, bA, bB, bC, crossZ, Prod.fst_sub, Prod.snd_sub]; try ring))

theorem sum_b (a b c y : ℤ × ℤ) : bA a b c y + bB a b c y + bC a b c y = det a b c := by
  pickRing

theorem sign_ne_neg_one_iff' (x : ℤ) : SignType.sign x ≠ -1 ↔ 0 ≤ x := by
  rw [Ne, sign_eq_neg_one_iff, not_lt]

theorem sign_mul_of_pos {k : ℤ} (hk : 0 < k) (z : ℤ) : SignType.sign (k * z) = SignType.sign z := by
  rw [sign_mul, sign_pos hk, one_mul]

theorem sign_eq_of_mul {D z t : ℤ} (hD : 0 < D) (h : D * z = t) :
    SignType.sign z = SignType.sign t := by
  rw [← h, sign_mul_of_pos hD]

theorem eq_of_cross {d e f : ℤ × ℤ} (h1 : crossZ d e = 0) (h2 : crossZ d f = 0)
    (h3 : crossZ e f ≠ 0) : d = 0 := by
  unfold crossZ at *
  have k1 : d.1 * (e.1 * f.2 - e.2 * f.1) = 0 := by linear_combination e.1 * h2 - f.1 * h1
  have k2 : d.2 * (e.1 * f.2 - e.2 * f.1) = 0 := by linear_combination e.2 * h2 - f.2 * h1
  rcases mul_eq_zero.1 k1 with k1 | k1
  · rcases mul_eq_zero.1 k2 with k2 | k2
    · exact Prod.ext k1 k2
    · exact absurd k2 h3
  · exact absurd k1 h3

theorem vertex_a {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) (hq : bB a b c y = 0)
    (hr : bC a b c y = 0) : y = a := by
  have := eq_of_cross (d := y - a) (e := c - a) (f := b - a) (by rw [← hq]; pickRing)
    (by rw [← neg_eq_zero, ← hr]; pickRing) (by
      intro h; apply hD; rw [← neg_eq_zero, ← h]; pickRing)
  exact sub_eq_zero.1 this

theorem vertex_b {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) (hp : bA a b c y = 0)
    (hr : bC a b c y = 0) : y = b := by
  have := eq_of_cross (d := y - b) (e := a - b) (f := c - b) (by rw [← hr]; pickRing)
    (by rw [← neg_eq_zero, ← hp]; pickRing) (by
      intro h; apply hD; rw [← neg_eq_zero, ← h]; pickRing)
  exact sub_eq_zero.1 this

theorem vertex_c {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) (hp : bA a b c y = 0)
    (hq : bB a b c y = 0) : y = c := by
  have := eq_of_cross (d := y - c) (e := b - c) (f := a - c) (by rw [← hp]; pickRing)
    (by rw [← neg_eq_zero, ← hq]; pickRing) (by
      intro h; apply hD; rw [← neg_eq_zero, ← h]; pickRing)
  exact sub_eq_zero.1 this

theorem InTri_iff_sign (a b c y : ℤ × ℤ) : InTri a b c y ↔
    SignType.sign (det a b c * bA a b c y) ≠ -1 ∧ SignType.sign (det a b c * bB a b c y) ≠ -1 ∧
      SignType.sign (det a b c * bC a b c y) ≠ -1 := by
  simp only [InTri, sign_ne_neg_one_iff']

theorem one_pos_of_sum {p q r D : ℤ} (hD : 0 < D) (h : p + q + r = D) :
    SignType.sign p = 1 ∨ SignType.sign q = 1 ∨ SignType.sign r = 1 := by
  by_cases hp : 0 < p
  · exact Or.inl (sign_pos hp)
  by_cases hq : 0 < q
  · exact Or.inr (Or.inl (sign_pos hq))
  exact Or.inr (Or.inr (sign_pos (by omega)))

theorem srel_neg {c₁ c₂ c₃ x₁ x₂ x₃ : ℤ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₃ : 0 < c₃)
    (h : c₁ * x₁ - c₂ * x₂ - c₃ * x₃ = 0) :
    SRel (SignType.sign x₁) (-SignType.sign x₂) (-SignType.sign x₃) := by
  have := srel_of_eq h₁ h₂ h₃ (x₁ := x₁) (x₂ := -x₂) (x₃ := -x₃) (by linear_combination h)
  rwa [Right.sign_neg, Right.sign_neg] at this

/-- Splitting the triangle `a b c` at an interior lattice point `x`. -/
theorem split_interior {a b c x : ℤ × ℤ} (hD : 0 < det a b c) (hα : 0 < bA a b c x)
    (hβ : 0 < bB a b c x) (hγ : 0 < bC a b c x) (y : ℤ × ℤ) :
    (wt a b c y = wt x b c y + wt a x c y + wt a b x y + 2 * (if y = x then 1 else 0)) ∧
    (InTri x b c y → InTri a b c y) ∧ (InTri a x c y → InTri a b c y) ∧
    (InTri a b x y → InTri a b c y) := by
  have d1 : det x b c = bA a b c x := rfl
  have d2 : det a x c = bB a b c x := by pickRing
  have d3 : det a b x = bC a b c x := by pickRing
  have e1 : det a b c * bB x b c y = bA a b c x * bB a b c y - bB a b c x * bA a b c y := by
    pickRing
  have e2 : det a b c * bC x b c y = -(bC a b c x * bA a b c y - bA a b c x * bC a b c y) := by
    pickRing
  have e3 : det a b c * bA a x c y = -(bA a b c x * bB a b c y - bB a b c x * bA a b c y) := by
    pickRing
  have e4 : det a b c * bC a x c y = bB a b c x * bC a b c y - bC a b c x * bB a b c y := by
    pickRing
  have e5 : det a b c * bA a b x y = bC a b c x * bA a b c y - bA a b c x * bC a b c y := by
    pickRing
  have e6 : det a b c * bB a b x y = -(bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    pickRing
  have s1 : SignType.sign (det x b c * bA x b c y) = SignType.sign (bA a b c y) := by
    rw [d1, sign_mul_of_pos hα]; rfl
  have s2 : SignType.sign (det x b c * bB x b c y) =
      SignType.sign (bA a b c x * bB a b c y - bB a b c x * bA a b c y) := by
    rw [d1, sign_mul_of_pos hα, sign_eq_of_mul hD e1]
  have s3 : SignType.sign (det x b c * bC x b c y) =
      -SignType.sign (bC a b c x * bA a b c y - bA a b c x * bC a b c y) := by
    rw [d1, sign_mul_of_pos hα, sign_eq_of_mul hD e2, Right.sign_neg]
  have t1 : SignType.sign (det a x c * bA a x c y) =
      -SignType.sign (bA a b c x * bB a b c y - bB a b c x * bA a b c y) := by
    rw [d2, sign_mul_of_pos hβ, sign_eq_of_mul hD e3, Right.sign_neg]
  have t2 : SignType.sign (det a x c * bB a x c y) = SignType.sign (bB a b c y) := by
    rw [d2, sign_mul_of_pos hβ]; rfl
  have t3 : SignType.sign (det a x c * bC a x c y) =
      SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    rw [d2, sign_mul_of_pos hβ, sign_eq_of_mul hD e4]
  have r1 : SignType.sign (det a b x * bA a b x y) =
      SignType.sign (bC a b c x * bA a b c y - bA a b c x * bC a b c y) := by
    rw [d3, sign_mul_of_pos hγ, sign_eq_of_mul hD e5]
  have r2 : SignType.sign (det a b x * bB a b x y) =
      -SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    rw [d3, sign_mul_of_pos hγ, sign_eq_of_mul hD e6, Right.sign_neg]
  have r3 : SignType.sign (det a b x * bC a b x y) = SignType.sign (bC a b c y) := by
    rw [d3, sign_mul_of_pos hγ]; rfl
  have m1 := sign_mul_of_pos hD (bA a b c y)
  have m2 := sign_mul_of_pos hD (bB a b c y)
  have m3 := sign_mul_of_pos hD (bC a b c y)
  have R1 := srel_neg (x₁ := bB a b c y) (x₂ := bA a b c y)
    (x₃ := bA a b c x * bB a b c y - bB a b c x * bA a b c y) hα hβ one_pos (by ring)
  have R2 := srel_neg (x₁ := bC a b c y) (x₂ := bB a b c y)
    (x₃ := bB a b c x * bC a b c y - bC a b c x * bB a b c y) hβ hγ one_pos (by ring)
  have R3 := srel_neg (x₁ := bA a b c y) (x₂ := bC a b c y)
    (x₃ := bC a b c x * bA a b c y - bA a b c x * bC a b c y) hγ hα one_pos (by ring)
  have R4 := srel_of_eq (x₁ := bA a b c x * bB a b c y - bB a b c x * bA a b c y)
    (x₂ := bB a b c x * bC a b c y - bC a b c x * bB a b c y)
    (x₃ := bC a b c x * bA a b c y - bA a b c x * bC a b c y) hγ hα hβ (by ring)
  have hpos := one_pos_of_sum hD (sum_b a b c y)
  have hDne : det a b c ≠ 0 := hD.ne'
  have heq : (SignType.sign (bA a b c x * bB a b c y - bB a b c x * bA a b c y) = 0 ∧
      SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) = 0 ∧
      SignType.sign (bC a b c x * bA a b c y - bA a b c x * bC a b c y) = 0) ↔ y = x := by
    simp only [sign_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      rw [← e1, mul_eq_zero] at h1
      rw [← e4, mul_eq_zero] at h2
      have h1' := h1.resolve_left hDne
      have h2' := h2.resolve_left hDne
      have := eq_of_cross (d := y - x) (e := c - x) (f := a - x) (by rw [← h1']; pickRing)
        (by rw [← h2']; pickRing)
        (by rw [show crossZ (c - x) (a - x) = bB a b c x from rfl]; omega)
      exact sub_eq_zero.1 this
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩ <;> ring
  have K := key_interior _ _ _ _ _ _ hpos R1 R2 R3 R4
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold wt
    rw [m1, m2, m3, s1, s2, s3, t1, t2, t3, r1, r2, r3, K]
    by_cases hyx : y = x
    · rw [ch13_if_pos (heq.mpr hyx), ch13_if_pos hyx]
    · rw [ch13_if_neg (fun h => hyx (heq.mp h)), ch13_if_neg hyx]
  · rw [InTri_iff_sign, InTri_iff_sign, s1, s2, s3, m1, m2, m3]
    exact closed_interior₁ _ _ _ _ _ _ R1 R2 R3 R4
  · rw [InTri_iff_sign, InTri_iff_sign, t1, t2, t3, m1, m2, m3]
    exact fun h => closed_interior₂ _ _ _ _ _ _ R1 R2 R3 R4 ⟨h.2.1, h.2.2, h.1⟩
  · rw [InTri_iff_sign, InTri_iff_sign, r1, r2, r3, m1, m2, m3]
    exact closed_interior₃ _ _ _ _ _ _ R1 R2 R3 R4

/-- Splitting the triangle `a b c` at a lattice point `x` of the open edge `bc`. -/
theorem split_edge {a b c x : ℤ × ℤ} (hD : 0 < det a b c) (hα : bA a b c x = 0)
    (hβ : 0 < bB a b c x) (hγ : 0 < bC a b c x) (y : ℤ × ℤ) :
    (wt a b c y = wt a b x y + wt a x c y + (if y = x then 1 else 0)) ∧
    (InTri a b x y → InTri a b c y) ∧ (InTri a x c y → InTri a b c y) := by
  have d2 : det a x c = bB a b c x := by pickRing
  have d3 : det a b x = bC a b c x := by pickRing
  have e3 : det a b c * bA a x c y = bB a b c x * bA a b c y := by
    have : det a b c * bA a x c y = -(bA a b c x * bB a b c y - bB a b c x * bA a b c y) := by
      pickRing
    rw [this, hα]; ring
  have e4 : det a b c * bC a x c y = bB a b c x * bC a b c y - bC a b c x * bB a b c y := by
    pickRing
  have e5 : det a b c * bA a b x y = bC a b c x * bA a b c y := by
    have : det a b c * bA a b x y = bC a b c x * bA a b c y - bA a b c x * bC a b c y := by
      pickRing
    rw [this, hα]; ring
  have e6 : det a b c * bB a b x y = -(bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    pickRing
  have t1 : SignType.sign (det a x c * bA a x c y) = SignType.sign (bA a b c y) := by
    rw [d2, sign_mul_of_pos hβ, sign_eq_of_mul hD e3, sign_mul_of_pos hβ]
  have t2 : SignType.sign (det a x c * bB a x c y) = SignType.sign (bB a b c y) := by
    rw [d2, sign_mul_of_pos hβ]; rfl
  have t3 : SignType.sign (det a x c * bC a x c y) =
      SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    rw [d2, sign_mul_of_pos hβ, sign_eq_of_mul hD e4]
  have r1 : SignType.sign (det a b x * bA a b x y) = SignType.sign (bA a b c y) := by
    rw [d3, sign_mul_of_pos hγ, sign_eq_of_mul hD e5, sign_mul_of_pos hγ]
  have r2 : SignType.sign (det a b x * bB a b x y) =
      -SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) := by
    rw [d3, sign_mul_of_pos hγ, sign_eq_of_mul hD e6, Right.sign_neg]
  have r3 : SignType.sign (det a b x * bC a b x y) = SignType.sign (bC a b c y) := by
    rw [d3, sign_mul_of_pos hγ]; rfl
  have m1 := sign_mul_of_pos hD (bA a b c y)
  have m2 := sign_mul_of_pos hD (bB a b c y)
  have m3 := sign_mul_of_pos hD (bC a b c y)
  have R := srel_neg (x₁ := bC a b c y) (x₂ := bB a b c y)
    (x₃ := bB a b c x * bC a b c y - bC a b c x * bB a b c y) hβ hγ one_pos (by ring)
  have hpos := one_pos_of_sum hD (sum_b a b c y)
  have hDne : det a b c ≠ 0 := hD.ne'
  have heq : (SignType.sign (bA a b c y) = 0 ∧
      SignType.sign (bB a b c x * bC a b c y - bC a b c x * bB a b c y) = 0) ↔ y = x := by
    simp only [sign_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rw [← e4, mul_eq_zero] at h2
      have h2' := h2.resolve_left hDne
      have k1 : crossZ (y - x) (c - b) = bA a b c x - bA a b c y := by pickRing
      have k3 : crossZ (c - b) (a - x) = det a b c - bA a b c x := by pickRing
      have := eq_of_cross (d := y - x) (e := c - b) (f := a - x) (by rw [k1, h1, hα]; ring)
        (by rw [← h2']; pickRing) (by rw [k3, hα]; omega)
      exact sub_eq_zero.1 this
    · rintro rfl
      exact ⟨hα, by ring⟩
  have K := key_edge _ _ _ _ hpos R
  refine ⟨?_, ?_, ?_⟩
  · unfold wt
    rw [m1, m2, m3, t1, t2, t3, r1, r2, r3, K]
    by_cases hyx : y = x
    · rw [ch13_if_pos (heq.mpr hyx), ch13_if_pos hyx]
    · rw [ch13_if_neg (fun h => hyx (heq.mp h)), ch13_if_neg hyx]
  · rw [InTri_iff_sign, InTri_iff_sign, r1, r2, r3, m1, m2, m3]
    exact closed_edge₁ _ _ _ _ R
  · rw [InTri_iff_sign, InTri_iff_sign, t1, t2, t3, m1, m2, m3]
    exact closed_edge₂ _ _ _ _ R

theorem det_rot (a b c : ℤ × ℤ) : det b c a = det a b c := by pickRing

theorem wt_rot (a b c y : ℤ × ℤ) : wt b c a y = wt a b c y := by
  unfold wt; rw [det_rot]; exact G_rot _ _ _

theorem InTri_rot (a b c y : ℤ × ℤ) : InTri b c a y ↔ InTri a b c y := by
  unfold InTri; rw [det_rot]
  exact ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩

theorem det_swap (a b c : ℤ × ℤ) : det a c b = -det a b c := by pickRing

theorem wt_swap (a b c y : ℤ × ℤ) : wt a c b y = wt a b c y := by
  unfold wt
  rw [show det a c b * bA a c b y = det a b c * bA a b c y by pickRing,
    show det a c b * bB a c b y = det a b c * bC a b c y by pickRing,
    show det a c b * bC a c b y = det a b c * bB a b c y by pickRing]
  exact G_swap _ _ _

theorem InTri_swap (a b c y : ℤ × ℤ) : InTri a c b y ↔ InTri a b c y := by
  unfold InTri
  rw [show det a c b * bA a c b y = det a b c * bA a b c y by pickRing,
    show det a c b * bB a c b y = det a b c * bC a b c y by pickRing,
    show det a c b * bC a c b y = det a b c * bB a b c y by pickRing]
  exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

theorem wt_of_not_inTri {a b c y : ℤ × ℤ} (h : ¬ InTri a b c y) : wt a b c y = 0 := by
  unfold wt G
  rw [ch13_if_neg]
  exact fun h' => h ((InTri_iff_sign a b c y).2 h')

theorem wt_a {a b c : ℤ × ℤ} (hD : 0 < det a b c) : wt a b c a = 0 := by
  unfold wt
  rw [show bA a b c a = det a b c by pickRing, show bB a b c a = 0 by pickRing,
    show bC a b c a = 0 by pickRing, mul_zero, sign_zero, sign_pos (mul_pos hD hD)]
  decide

theorem wt_b {a b c : ℤ × ℤ} (hD : 0 < det a b c) : wt a b c b = 0 := by
  unfold wt
  rw [show bB a b c b = det a b c by pickRing, show bA a b c b = 0 by pickRing,
    show bC a b c b = 0 by pickRing, mul_zero, sign_zero, sign_pos (mul_pos hD hD)]
  decide

theorem wt_c {a b c : ℤ × ℤ} (hD : 0 < det a b c) : wt a b c c = 0 := by
  unfold wt
  rw [show bC a b c c = det a b c by pickRing, show bA a b c c = 0 by pickRing,
    show bB a b c c = 0 by pickRing, mul_zero, sign_zero, sign_pos (mul_pos hD hD)]
  decide

/-- The induction hypothesis used in the proof of Pick's formula. -/
def PickIH (n : ℤ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ a b c : ℤ × ℤ, 0 < det a b c → det a b c < n → (∀ y, InTri a b c y → y ∈ S) →
    ∑ y ∈ S, wt a b c y = det a b c - 1

theorem sum_interior {a b c x : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (hD : 0 < det a b c)
    (hα : 0 < bA a b c x) (hβ : 0 < bB a b c x) (hγ : 0 < bC a b c x)
    (hS : ∀ y, InTri a b c y → y ∈ S) (hxS : x ∈ S) (IH : PickIH (det a b c) S) :
    ∑ y ∈ S, wt a b c y = det a b c - 1 := by
  have hsplit := split_interior hD hα hβ hγ
  have d1 : det x b c = bA a b c x := rfl
  have d2 : det a x c = bB a b c x := by pickRing
  have d3 : det a b x = bC a b c x := by pickRing
  have hsum := sum_b a b c x
  rw [Finset.sum_congr rfl (fun y _ => (hsplit y).1)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', ch13_if_pos hxS]
  rw [IH x b c (by omega) (by omega) (fun y hy => hS y ((hsplit y).2.1 hy)),
    IH a x c (by omega) (by omega) (fun y hy => hS y ((hsplit y).2.2.1 hy)),
    IH a b x (by omega) (by omega) (fun y hy => hS y ((hsplit y).2.2.2 hy))]
  omega

theorem sum_edge {a b c x : ℤ × ℤ} {S : Finset (ℤ × ℤ)} (hD : 0 < det a b c)
    (hα : bA a b c x = 0) (hβ : 0 < bB a b c x) (hγ : 0 < bC a b c x)
    (hS : ∀ y, InTri a b c y → y ∈ S) (hxS : x ∈ S) (IH : PickIH (det a b c) S) :
    ∑ y ∈ S, wt a b c y = det a b c - 1 := by
  have hsplit := split_edge hD hα hβ hγ
  have d2 : det a x c = bB a b c x := by pickRing
  have d3 : det a b x = bC a b c x := by pickRing
  have hsum := sum_b a b c x
  rw [Finset.sum_congr rfl (fun y _ => (hsplit y).1)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', ch13_if_pos hxS]
  rw [IH a b x (by omega) (by omega) (fun y hy => hS y ((hsplit y).2.1 hy)),
    IH a x c (by omega) (by omega) (fun y hy => hS y ((hsplit y).2.2 hy))]
  omega

/-- The lattice point of the plane corresponding to `z ∈ ℤ²`. -/
def toR (z : ℤ × ℤ) : ℝ × ℝ := ((z.1 : ℝ), (z.2 : ℝ))

theorem isLatticePoint_toR (z : ℤ × ℤ) : IsLatticePoint (toR z) := ⟨z.1, z.2, rfl⟩

theorem toR_injective : Function.Injective toR := by
  intro u v h
  simp only [toR, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

theorem cross_toR (u v w : ℤ × ℤ) :
    Plane.cross (toR u - toR w) (toR v - toR w) = ((crossZ (u - w) (v - w) : ℤ) : ℝ) := by
  simp only [Plane.cross, crossZ, toR, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

theorem det_toR (a b c : ℤ × ℤ) :
    Plane.cross (toR b - toR a) (toR c - toR a) = ((det a b c : ℤ) : ℝ) := cross_toR b c a

theorem bA_toR (a b c y : ℤ × ℤ) :
    Plane.cross (toR b - toR y) (toR c - toR y) = ((bA a b c y : ℤ) : ℝ) := cross_toR b c y

theorem bB_toR (a b c y : ℤ × ℤ) :
    Plane.cross (toR c - toR y) (toR a - toR y) = ((bB a b c y : ℤ) : ℝ) := cross_toR c a y

theorem bC_toR (a b c y : ℤ × ℤ) :
    Plane.cross (toR a - toR y) (toR b - toR y) = ((bC a b c y : ℤ) : ℝ) := cross_toR a b y

/-- Points of the (real) triangle `conv {A, B, C}` have nonnegative barycentric
determinants (relative to the orientation). -/
theorem barycentric_nonneg_of_mem {A B C z : ℝ × ℝ} (hz : z ∈ convexHull ℝ {A, B, C}) :
    0 ≤ Plane.cross (B - A) (C - A) * Plane.cross (B - z) (C - z) ∧
    0 ≤ Plane.cross (B - A) (C - A) * Plane.cross (C - z) (A - z) ∧
    0 ≤ Plane.cross (B - A) (C - A) * Plane.cross (A - z) (B - z) := by
  rw [convexHull_triple] at hz
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  have e1 : Plane.cross (B - (A + s • (B - A) + t • (C - A))) (C - (A + s • (B - A) + t • (C - A)))
      = (1 - s - t) * Plane.cross (B - A) (C - A) := by
    simp only [Plane.cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e2 : Plane.cross (C - (A + s • (B - A) + t • (C - A))) (A - (A + s • (B - A) + t • (C - A)))
      = s * Plane.cross (B - A) (C - A) := by
    simp only [Plane.cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have e3 : Plane.cross (A - (A + s • (B - A) + t • (C - A))) (B - (A + s • (B - A) + t • (C - A)))
      = t * Plane.cross (B - A) (C - A) := by
    simp only [Plane.cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [e1, e2, e3]
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ 1 - s - t := by linarith
    nlinarith [mul_self_nonneg (Plane.cross (B - A) (C - A))]
  · nlinarith [mul_self_nonneg (Plane.cross (B - A) (C - A))]
  · nlinarith [mul_self_nonneg (Plane.cross (B - A) (C - A))]

theorem not_collinear_of_cross_ne_zero {A B C : ℝ × ℝ} (h : Plane.cross (B - A) (C - A) ≠ 0) :
    ¬ Collinear ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  intro hcol
  rw [collinear_iff_of_mem (p₀ := A) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨rB, hB⟩ := hv B (by simp)
  obtain ⟨rC, hC⟩ := hv C (by simp)
  apply h
  rw [hB, hC]
  simp only [Plane.cross, vadd_eq_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The Lemma of the book, in the present language: a lattice triangle without lattice points
other than its vertices has `det = 1`. -/
theorem det_eq_one_of_elementary {a b c : ℤ × ℤ} (hD : 0 < det a b c)
    (h : ∀ y, InTri a b c y → y = a ∨ y = b ∨ y = c) : det a b c = 1 := by
  have hDR : Plane.cross (toR b - toR a) (toR c - toR a) ≠ 0 := by
    rw [det_toR]; exact_mod_cast hD.ne'
  have hel : IsElementaryTriangle (toR a) (toR b) (toR c) := by
    refine ⟨isLatticePoint_toR a, isLatticePoint_toR b, isLatticePoint_toR c,
      not_collinear_of_cross_ne_zero hDR, ?_⟩
    rintro z ⟨m, n, rfl⟩ hz
    have hz' : ((m : ℝ), (n : ℝ)) = toR (m, n) := rfl
    rw [hz'] at hz ⊢
    obtain ⟨h1, h2, h3⟩ := barycentric_nonneg_of_mem hz
    rw [det_toR, bA_toR a b c] at h1
    rw [det_toR, bB_toR a b c] at h2
    rw [det_toR, bC_toR a b c] at h3
    have hin : InTri a b c (m, n) := ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3⟩
    rcases h _ hin with e | e | e <;> rw [e] <;> simp
  have := elementary_abs_cross hel
  rw [det_toR] at this
  have : |det a b c| = 1 := by exact_mod_cast this
  rwa [abs_of_pos hD] at this

theorem sum_wt_of_pos (n : ℕ) : ∀ a b c : ℤ × ℤ, det a b c = n → 0 < det a b c →
    ∀ S : Finset (ℤ × ℤ), (∀ y, InTri a b c y → y ∈ S) →
    ∑ y ∈ S, wt a b c y = det a b c - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hD S hS
  have IH : PickIH (det a b c) S := fun a' b' c' h1 h2 h3 =>
    ih (det a' b' c').toNat (by omega) a' b' c' (by omega) h1 S h3
  have hDne : det a b c ≠ 0 := hD.ne'
  by_cases hex : ∃ x, InTri a b c x ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c
  · obtain ⟨x, hx, hxa, hxb, hxc⟩ := hex
    have hxS := hS x hx
    obtain ⟨h1, h2, h3⟩ := hx
    have hα : 0 ≤ bA a b c x := by nlinarith
    have hβ : 0 ≤ bB a b c x := by nlinarith
    have hγ : 0 ≤ bC a b c x := by nlinarith
    rcases hα.lt_or_eq with hα | hα
    · rcases hβ.lt_or_eq with hβ | hβ
      · rcases hγ.lt_or_eq with hγ | hγ
        · exact sum_interior hD hα hβ hγ hS hxS IH
        · -- `x` on the edge `ab`: rotate twice
          have hD' : 0 < det c a b := by rw [← det_rot c a b]; exact hD
          have hS' : ∀ y, InTri c a b y → y ∈ S := fun y hy =>
            hS y ((InTri_rot _ _ _ y).1 ((InTri_rot _ _ _ y).1 hy))
          have IH' : PickIH (det c a b) S := by rw [← det_rot c a b]; exact IH
          have := sum_edge (a := c) (b := a) (c := b) (x := x) hD' hγ.symm hα hβ hS' hxS IH'
          rw [← det_rot c a b] at this
          rw [← this]
          exact Finset.sum_congr rfl (fun y _ => wt_rot c a b y)
      · -- `x` on the edge `ca`: rotate once
        have hγ' : 0 < bC a b c x := by
          rcases hγ.lt_or_eq with hγ | hγ
          · exact hγ
          · exact absurd (vertex_a hDne hβ.symm hγ.symm) hxa
        have hD' : 0 < det b c a := by rw [det_rot]; exact hD
        have hS' : ∀ y, InTri b c a y → y ∈ S := fun y hy => hS y ((InTri_rot _ _ _ y).1 hy)
        have IH' : PickIH (det b c a) S := by rw [det_rot]; exact IH
        have := sum_edge (a := b) (b := c) (c := a) (x := x) hD' hβ.symm hγ' hα hS' hxS IH'
        rw [det_rot] at this
        rw [← this]
        exact Finset.sum_congr rfl (fun y _ => (wt_rot a b c y).symm)
    · have hβ' : 0 < bB a b c x := by
        rcases hβ.lt_or_eq with hβ | hβ
        · exact hβ
        · exact absurd (vertex_c hDne hα.symm hβ.symm) hxc
      have hγ' : 0 < bC a b c x := by
        rcases hγ.lt_or_eq with hγ | hγ
        · exact hγ
        · exact absurd (vertex_b hDne hα.symm hγ.symm) hxb
      exact sum_edge hD hα.symm hβ' hγ' hS hxS IH
  · push Not at hex
    have h1 := det_eq_one_of_elementary hD (fun y hy => by
      by_contra hc; push Not at hc; exact hc.2.2 (hex y hy hc.1 hc.2.1))
    rw [h1, sub_self]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : InTri a b c y
    · by_cases hya : y = a
      · rw [hya]; exact wt_a hD
      by_cases hyb : y = b
      · rw [hyb]; exact wt_b hD
      rw [hex y hy hya hyb]; exact wt_c hD
    · exact wt_of_not_inTri hy

/-- **Pick's formula for lattice triangles, weighted form.** For a nondegenerate lattice triangle,
the sum of the Pick weights of all lattice points equals `|det| - 1`. -/
theorem sum_wt {a b c : ℤ × ℤ} (hD : det a b c ≠ 0) (S : Finset (ℤ × ℤ))
    (hS : ∀ y, InTri a b c y → y ∈ S) : ∑ y ∈ S, wt a b c y = |det a b c| - 1 := by
  rcases hD.lt_or_gt with hD | hD
  · have hD' : 0 < det a c b := by rw [det_swap]; omega
    have := sum_wt_of_pos (det a c b).toNat a c b (by omega) hD' S
      (fun y hy => hS y ((InTri_swap a b c y).1 hy))
    rw [det_swap] at this
    rw [abs_of_neg hD, ← this]
    exact Finset.sum_congr rfl (fun y _ => (wt_swap a b c y).symm)
  · rw [abs_of_pos hD]
    exact sum_wt_of_pos (det a b c).toNat a b c (by omega) hD S hS

instance (a b c y : ℤ × ℤ) : Decidable (InTri a b c y) := by unfold InTri; infer_instance

instance (a b c y : ℤ × ℤ) : Decidable (InTriStrict a b c y) := by
  unfold InTriStrict; infer_instance

/-- The Pick weight is `2` at interior points, `1` at boundary points other than the vertices,
`0` at the vertices and outside. -/
theorem wt_eq {a b c : ℤ × ℤ} (hD : det a b c ≠ 0) (y : ℤ × ℤ) :
    wt a b c y = 2 * (if InTriStrict a b c y then 1 else 0) +
      (if InTri a b c y ∧ ¬ InTriStrict a b c y then 1 else 0) -
      (if y = a ∨ y = b ∨ y = c then 1 else 0) := by
  have hnz : ¬ (SignType.sign (det a b c * bA a b c y) = 0 ∧
      SignType.sign (det a b c * bB a b c y) = 0 ∧ SignType.sign (det a b c * bC a b c y) = 0) := by
    simp only [sign_eq_zero_iff, mul_eq_zero, hD, false_or]
    rintro ⟨h1, h2, h3⟩
    have := sum_b a b c y
    rw [h1, h2, h3] at this
    exact hD (by omega)
  unfold wt
  rw [G_eq _ _ _ hnz]
  have hS : (SignType.sign (det a b c * bA a b c y) = 1 ∧
      SignType.sign (det a b c * bB a b c y) = 1 ∧ SignType.sign (det a b c * bC a b c y) = 1) ↔
      InTriStrict a b c y := by
    simp only [sign_eq_one_iff, InTriStrict]
  have hC : (SignType.sign (det a b c * bA a b c y) ≠ -1 ∧
      SignType.sign (det a b c * bB a b c y) ≠ -1 ∧ SignType.sign (det a b c * bC a b c y) ≠ -1) ↔
      InTri a b c y := (InTri_iff_sign a b c y).symm
  have hV : ((SignType.sign (det a b c * bA a b c y) = 1 ∧
      SignType.sign (det a b c * bB a b c y) = 0 ∧ SignType.sign (det a b c * bC a b c y) = 0) ∨
      (SignType.sign (det a b c * bA a b c y) = 0 ∧
      SignType.sign (det a b c * bB a b c y) = 1 ∧ SignType.sign (det a b c * bC a b c y) = 0) ∨
      (SignType.sign (det a b c * bA a b c y) = 0 ∧
      SignType.sign (det a b c * bB a b c y) = 0 ∧ SignType.sign (det a b c * bC a b c y) = 1)) ↔
      (y = a ∨ y = b ∨ y = c) := by
    simp only [sign_eq_zero_iff, mul_eq_zero, hD, false_or, sign_eq_one_iff]
    constructor
    · rintro (⟨-, h2, h3⟩ | ⟨h1, -, h3⟩ | ⟨h1, h2, -⟩)
      · exact Or.inl (vertex_a hD h2 h3)
      · exact Or.inr (Or.inl (vertex_b hD h1 h3))
      · exact Or.inr (Or.inr (vertex_c hD h1 h2))
    · rintro (rfl | rfl | rfl)
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · rw [show bA y b c y = det y b c by pickRing]; exact mul_self_pos.2 hD
        · pickRing
        · pickRing
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · pickRing
        · rw [show bB a y c y = det a y c by pickRing]; exact mul_self_pos.2 hD
        · pickRing
      · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
        · pickRing
        · pickRing
        · rw [show bC a b y y = det a b y by pickRing]; exact mul_self_pos.2 hD
  rw [if_congr hS rfl rfl, if_congr (and_congr hC (not_congr hS)) rfl rfl, if_congr hV rfl rfl]

theorem abs_le_of_comb {P Q R K y x₁ x₂ x₃ M : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hK : P + Q + R = K) (hKp : 0 < K) (e : K * y = P * x₁ + Q * x₂ + R * x₃)
    (h₁ : |x₁| ≤ M) (h₂ : |x₂| ≤ M) (h₃ : |x₃| ≤ M) : |y| ≤ M := by
  rw [abs_le] at *
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  obtain ⟨h₃, h₃'⟩ := h₃
  have k1 := mul_le_mul_of_nonneg_left h₁ hP
  have k2 := mul_le_mul_of_nonneg_left h₂ hQ
  have k3 := mul_le_mul_of_nonneg_left h₃ hR
  have k1' := mul_le_mul_of_nonneg_left h₁' hP
  have k2' := mul_le_mul_of_nonneg_left h₂' hQ
  have k3' := mul_le_mul_of_nonneg_left h₃' hR
  constructor
  · by_contra h
    push Not at h
    nlinarith
  · by_contra h
    push Not at h
    nlinarith

/-- Lattice points of a lattice triangle lie in an explicit box. -/
theorem abs_le_of_inTri {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) (hy : InTri a b c y) :
    |y.1| ≤ |a.1| + |a.2| + |b.1| + |b.2| + |c.1| + |c.2| ∧
    |y.2| ≤ |a.1| + |a.2| + |b.1| + |b.2| + |c.1| + |c.2| := by
  obtain ⟨hP, hQ, hR⟩ := hy
  have hsum : det a b c * bA a b c y + det a b c * bB a b c y + det a b c * bC a b c y =
      det a b c * det a b c := by rw [← mul_add, ← mul_add, sum_b]
  have hDD : 0 < det a b c * det a b c := mul_self_pos.2 hD
  have e1 : det a b c * det a b c * y.1 = det a b c * bA a b c y * a.1 +
      det a b c * bB a b c y * b.1 + det a b c * bC a b c y * c.1 := by pickRing
  have e2 : det a b c * det a b c * y.2 = det a b c * bA a b c y * a.2 +
      det a b c * bB a b c y * b.2 + det a b c * bC a b c y * c.2 := by pickRing
  have n1 := abs_nonneg a.1
  have n2 := abs_nonneg a.2
  have n3 := abs_nonneg b.1
  have n4 := abs_nonneg b.2
  have n5 := abs_nonneg c.1
  have n6 := abs_nonneg c.2
  exact ⟨abs_le_of_comb hP hQ hR hsum hDD e1 (by linarith) (by linarith) (by linarith),
    abs_le_of_comb hP hQ hR hsum hDD e2 (by linarith) (by linarith) (by linarith)⟩

/-- A finite box containing all lattice points of the triangle `a b c`. -/
def box (a b c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let M := |a.1| + |a.2| + |b.1| + |b.2| + |c.1| + |c.2|
  Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M

theorem mem_box {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) (hy : InTri a b c y) : y ∈ box a b c := by
  obtain ⟨h1, h2⟩ := abs_le_of_inTri hD hy
  rw [abs_le] at h1 h2
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1, h2⟩

theorem inTri_a (a b c : ℤ × ℤ) : InTri a b c a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show bA a b c a = det a b c by pickRing]; exact mul_self_nonneg _
  · rw [show bB a b c a = 0 by pickRing, mul_zero]
  · rw [show bC a b c a = 0 by pickRing, mul_zero]

theorem inTri_b (a b c : ℤ × ℤ) : InTri a b c b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show bA a b c b = 0 by pickRing, mul_zero]
  · rw [show bB a b c b = det a b c by pickRing]; exact mul_self_nonneg _
  · rw [show bC a b c b = 0 by pickRing, mul_zero]

theorem inTri_c (a b c : ℤ × ℤ) : InTri a b c c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show bA a b c c = 0 by pickRing, mul_zero]
  · rw [show bB a b c c = 0 by pickRing, mul_zero]
  · rw [show bC a b c c = det a b c by pickRing]; exact mul_self_nonneg _

/-- **Pick's formula for lattice triangles, counting form**: `|det| = 2 n_int + n_bd - 2`,
where `n_int` is the number of lattice points in the open triangle and `n_bd` the number of
lattice points on its boundary. -/
theorem pick_count {a b c : ℤ × ℤ} (hD : det a b c ≠ 0) :
    |det a b c| = 2 * ((box a b c).filter (fun y => InTriStrict a b c y)).card +
      ((box a b c).filter (fun y => InTri a b c y ∧ ¬ InTriStrict a b c y)).card - 2 := by
  have h := sum_wt hD (box a b c) (fun y hy => mem_box hD hy)
  rw [Finset.sum_congr rfl (fun y _ => wt_eq hD y), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    Finset.sum_boole] at h
  have hab : a ≠ b := by rintro rfl; apply hD; pickRing
  have hac : a ≠ c := by rintro rfl; apply hD; pickRing
  have hbc : b ≠ c := by rintro rfl; apply hD; pickRing
  have hV : (box a b c).filter (fun y => y = a ∨ y = b ∨ y = c) = {a, b, c} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl | rfl)
      · exact ⟨mem_box hD (inTri_a _ _ _), Or.inl rfl⟩
      · exact ⟨mem_box hD (inTri_b _ _ _), Or.inr (Or.inl rfl)⟩
      · exact ⟨mem_box hD (inTri_c _ _ _), Or.inr (Or.inr rfl)⟩
  have h3 : ({a, b, c} : Finset (ℤ × ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  rw [hV, h3] at h
  push_cast at h
  omega

end PickInt

end Chapter13

/-! ════════════════ Part: Pick ════════════════ -/

/-!
# 3. Pick's theorem for lattice triangles

We prove Pick's formula `A(Q) = n_int + n_bd / 2 - 1` for every nondegenerate lattice triangle
`Q = conv {A, B, C}` in the plane `ℝ × ℝ`, where `n_int` is the number of lattice points in the
topological interior of `Q` and `n_bd` the number of lattice points on its frontier, and `A(Q)` is
the Lebesgue measure of `Q`.

The combinatorial heart is `PickInt.pick_count` (`|det| = 2 n_int + n_bd - 2`, proved by splitting
the triangle into smaller lattice triangles down to elementary ones, whose area is `1/2` by the
Lemma of the book).  Here we identify the combinatorially defined interior and boundary with the
topological ones, and use `area = |det| / 2`.
-/


namespace Chapter13

open Plane PickInt MeasureTheory Filter Topology

/-- The three barycentric determinants of `z` with respect to `A B C`. -/
theorem barycentric_sum (A B C z : ℝ × ℝ) :
    cross (B - z) (C - z) + cross (C - z) (A - z) + cross (A - z) (B - z) =
      cross (B - A) (C - A) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

theorem mem_convexHull_iff_barycentric {A B C z : ℝ × ℝ} (hD : cross (B - A) (C - A) ≠ 0) :
    z ∈ convexHull ℝ {A, B, C} ↔
      0 ≤ cross (B - A) (C - A) * cross (B - z) (C - z) ∧
      0 ≤ cross (B - A) (C - A) * cross (C - z) (A - z) ∧
      0 ≤ cross (B - A) (C - A) * cross (A - z) (B - z) := by
  refine ⟨barycentric_nonneg_of_mem, ?_⟩
  rintro ⟨h1, h2, h3⟩
  set D := cross (B - A) (C - A) with hDdef
  have hDD : 0 < D * D := mul_self_pos.2 hD
  have hsum := barycentric_sum A B C z
  have key := mem_convexHull_triple_iff A B C (D * cross (C - z) (A - z) / (D * D))
    (D * cross (A - z) (B - z) / (D * D)) (div_nonneg h2 hDD.le) (div_nonneg h3 hDD.le) (by
      rw [← add_div, div_le_one hDD]
      rw [← hDdef] at hsum
      have : D * cross (B - z) (C - z) =
          D * D - D * cross (C - z) (A - z) - D * cross (A - z) (B - z) := by
        rw [← hsum]; ring
      linarith)
  convert key using 1
  rw [← hDdef] at hsum
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    simp only [hDdef, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    field_simp
    simp only [hDdef, cross, Prod.fst_sub, Prod.snd_sub]
    ring

theorem pos_of_mem_interior {A B C z : ℝ × ℝ} (hD : cross (B - A) (C - A) ≠ 0)
    (hz : z ∈ interior (convexHull ℝ {A, B, C})) :
    0 < cross (B - A) (C - A) * cross (B - z) (C - z) := by
  have hz0 := ((mem_convexHull_iff_barycentric hD).1 (interior_subset hz)).1
  rcases hz0.lt_or_eq with h | h
  · exact h
  exfalso
  have hc : Continuous (fun δ : ℝ => z + δ • (z - A)) := by fun_prop
  have ht : Tendsto (fun δ : ℝ => z + δ • (z - A)) (𝓝[>] 0) (𝓝 z) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  obtain ⟨δ, hδT, hδ⟩ :=
    ((ht.eventually (mem_interior_iff_mem_nhds.1 hz)).and self_mem_nhdsWithin).exists
  have h' := ((mem_convexHull_iff_barycentric hD).1 hδT).1
  have e : cross (B - (z + δ • (z - A))) (C - (z + δ • (z - A))) =
      (1 + δ) * cross (B - z) (C - z) - δ * cross (B - A) (C - A) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  rw [e] at h'
  have hDD : 0 < cross (B - A) (C - A) * cross (B - A) (C - A) := mul_self_pos.2 hD
  have hδ' : (0 : ℝ) < δ := hδ
  nlinarith

theorem convexHull_rot (A B C : ℝ × ℝ) :
    convexHull ℝ ({B, C, A} : Set (ℝ × ℝ)) = convexHull ℝ {A, B, C} := by
  congr 1
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem cross_rot (A B C : ℝ × ℝ) : cross (C - B) (A - B) = cross (B - A) (C - A) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

theorem mem_interior_iff_barycentric {A B C z : ℝ × ℝ} (hD : cross (B - A) (C - A) ≠ 0) :
    z ∈ interior (convexHull ℝ {A, B, C}) ↔
      0 < cross (B - A) (C - A) * cross (B - z) (C - z) ∧
      0 < cross (B - A) (C - A) * cross (C - z) (A - z) ∧
      0 < cross (B - A) (C - A) * cross (A - z) (B - z) := by
  constructor
  · intro hz
    refine ⟨pos_of_mem_interior hD hz, ?_, ?_⟩
    · have hD' : cross (C - B) (A - B) ≠ 0 := by rwa [cross_rot]
      have := pos_of_mem_interior hD' (by rwa [convexHull_rot])
      rwa [cross_rot] at this
    · have hD'' : cross (A - C) (B - C) ≠ 0 := by rwa [cross_rot, cross_rot]
      have := pos_of_mem_interior hD'' (by rwa [convexHull_rot, convexHull_rot])
      rwa [cross_rot, cross_rot] at this
  · intro hz
    have hopen : IsOpen {z : ℝ × ℝ | 0 < cross (B - A) (C - A) * cross (B - z) (C - z) ∧
        0 < cross (B - A) (C - A) * cross (C - z) (A - z) ∧
        0 < cross (B - A) (C - A) * cross (A - z) (B - z)} := by
      have hc : ∀ P Q : ℝ × ℝ, Continuous (fun z : ℝ × ℝ => cross (B - A) (C - A) *
          cross (P - z) (Q - z)) := by
        intro P Q; unfold cross; fun_prop
      exact (isOpen_lt continuous_const (hc B C)).inter
        ((isOpen_lt continuous_const (hc C A)).inter (isOpen_lt continuous_const (hc A B)))
    refine interior_maximal (fun w hw => ?_) hopen hz
    exact (mem_convexHull_iff_barycentric hD).2 ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩

theorem frontier_convexHull_triple (A B C : ℝ × ℝ) :
    frontier (convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))) =
      convexHull ℝ {A, B, C} \ interior (convexHull ℝ {A, B, C}) := by
  have hc : IsCompact (convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))) := by
    apply Set.Finite.isCompact_convexHull
    exact Set.toFinite _
  rw [frontier, hc.isClosed.closure_eq]

theorem toR_mem_interior_iff {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) :
    toR y ∈ interior (convexHull ℝ {toR a, toR b, toR c}) ↔ InTriStrict a b c y := by
  have hDR : cross (toR b - toR a) (toR c - toR a) ≠ 0 := by
    rw [det_toR]; exact_mod_cast hD
  rw [mem_interior_iff_barycentric hDR, det_toR, bA_toR a b c, bB_toR a b c, bC_toR a b c]
  simp only [← Int.cast_mul, Int.cast_pos, InTriStrict]

theorem toR_mem_iff {a b c y : ℤ × ℤ} (hD : det a b c ≠ 0) :
    toR y ∈ convexHull ℝ {toR a, toR b, toR c} ↔ InTri a b c y := by
  have hDR : cross (toR b - toR a) (toR c - toR a) ≠ 0 := by
    rw [det_toR]; exact_mod_cast hD
  rw [mem_convexHull_iff_barycentric hDR, det_toR, bA_toR a b c, bB_toR a b c, bC_toR a b c]
  simp only [← Int.cast_mul, InTri]
  norm_cast

/-- **Pick's theorem for lattice triangles.**  The area of a nondegenerate lattice triangle `Q`
equals `n_int + n_bd / 2 - 1`, where `n_int` is the number of lattice points in the interior of
`Q` and `n_bd` is the number of lattice points on the boundary of `Q`. -/
theorem pick_triangle {A B C : ℝ × ℝ} (hA : IsLatticePoint A) (hB : IsLatticePoint B)
    (hC : IsLatticePoint C) (hcol : ¬ Collinear ℝ ({A, B, C} : Set (ℝ × ℝ))) :
    volume (convexHull ℝ {A, B, C}) =
      ENNReal.ofReal
        (({p | IsLatticePoint p ∧ p ∈ interior (convexHull ℝ {A, B, C})}.ncard : ℝ) +
          ({p | IsLatticePoint p ∧ p ∈ frontier (convexHull ℝ {A, B, C})}.ncard : ℝ) / 2 - 1) := by
  obtain ⟨a1, a2, rfl⟩ := hA
  obtain ⟨b1, b2, rfl⟩ := hB
  obtain ⟨c1, c2, rfl⟩ := hC
  set a : ℤ × ℤ := (a1, a2)
  set b : ℤ × ℤ := (b1, b2)
  set c : ℤ × ℤ := (c1, c2)
  change volume (convexHull ℝ {toR a, toR b, toR c}) = ENNReal.ofReal
      (({p | IsLatticePoint p ∧ p ∈ interior (convexHull ℝ {toR a, toR b, toR c})}.ncard : ℝ) +
        ({p | IsLatticePoint p ∧ p ∈ frontier (convexHull ℝ {toR a, toR b, toR c})}.ncard : ℝ) / 2
          - 1)
  change ¬ Collinear ℝ ({toR a, toR b, toR c} : Set (ℝ × ℝ)) at hcol
  have hDR := cross_ne_zero_of_not_collinear hcol
  have hD : det a b c ≠ 0 := by rw [det_toR] at hDR; exact_mod_cast hDR
  have hI : {p | IsLatticePoint p ∧ p ∈ interior (convexHull ℝ {toR a, toR b, toR c})} =
      toR '' ↑((box a b c).filter (fun y => InTriStrict a b c y)) := by
    ext p
    simp only [ch13_mem_setOf, Set.mem_image, Finset.coe_filter]
    constructor
    · rintro ⟨⟨m, n, rfl⟩, hp⟩
      have hp' : toR (m, n) ∈ interior (convexHull ℝ {toR a, toR b, toR c}) := hp
      rw [toR_mem_interior_iff hD] at hp'
      exact ⟨(m, n), ⟨mem_box hD ⟨hp'.1.le, hp'.2.1.le, hp'.2.2.le⟩, hp'⟩, rfl⟩
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact ⟨isLatticePoint_toR y, (toR_mem_interior_iff hD).2 hy⟩
  have hF : {p | IsLatticePoint p ∧ p ∈ frontier (convexHull ℝ {toR a, toR b, toR c})} =
      toR '' ↑((box a b c).filter (fun y => InTri a b c y ∧ ¬ InTriStrict a b c y)) := by
    ext p
    simp only [ch13_mem_setOf, Set.mem_image, Finset.coe_filter, frontier_convexHull_triple,
      ch13_mem_sdiff]
    constructor
    · rintro ⟨⟨m, n, rfl⟩, hp, hp2⟩
      have hp' : toR (m, n) ∈ convexHull ℝ {toR a, toR b, toR c} := hp
      have hp2' : toR (m, n) ∉ interior (convexHull ℝ {toR a, toR b, toR c}) := hp2
      rw [toR_mem_iff hD] at hp'
      rw [toR_mem_interior_iff hD] at hp2'
      exact ⟨(m, n), ⟨mem_box hD hp', hp', hp2'⟩, rfl⟩
    · rintro ⟨y, ⟨-, hy, hy2⟩, rfl⟩
      exact ⟨isLatticePoint_toR y, (toR_mem_iff hD).2 hy,
        fun h => hy2 ((toR_mem_interior_iff hD).1 h)⟩
  rw [hI, hF, Set.ncard_image_of_injective _ toR_injective,
    Set.ncard_image_of_injective _ toR_injective, Set.ncard_coe_finset, Set.ncard_coe_finset,
    volume_triangle _ _ _ hDR, det_toR]
  congr 1
  have hp := pick_count hD
  have hp' : ((|det a b c| : ℤ) : ℝ) = 2 * (((box a b c).filter
      (fun y => InTriStrict a b c y)).card : ℝ) + (((box a b c).filter
      (fun y => InTri a b c y ∧ ¬ InTriStrict a b c y)).card : ℝ) - 2 := by
    rw [hp]; push_cast; ring
  rw [Int.cast_abs] at hp'
  rw [hp']
  ring

end Chapter13
