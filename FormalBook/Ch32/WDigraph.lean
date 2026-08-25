/-
Copyright 2026 Egor Morozov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Morozov 
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.DepRewrite

/-!
# Basic facts about weighted directed graphs

This is an auxiliary file for Chapter 32.

## Implementation notes

In mathlib, the API for walks is developed only for undirected unweighted
graphs. In this file we define weighted directed graphs and prove basic facts
about them in a way similar to Mathlib.Combinatorics.SimpleGraph.Basic and
Mathlib.Combinatorics.SimpleGraph.Walk. It also contains few lemmas missing in
mathlib (such as `take_append_of_le_length`). This file should be removed as
soon as relevant framework appear in mathlib.
-/
universe u v

structure WDigraph (V : Type u) (R : Type v) [CommRing R] where
  weight : V → V → Option R

variable {V : Type u}
variable {R : Type v} [CommRing R]
variable (G : WDigraph V R)

namespace WDigraph

def Adj (u v : V) : Prop := (G.weight u v).isSome

inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

namespace Walk

class PathFinite : Prop where
  fin_walks : ∀ (u v : V), Finite (G.Walk u v)

instance {u v : V} [h : PathFinite G] : Finite (G.Walk u v) := h.fin_walks u v

noncomputable instance {u v : V} [PathFinite G] :
  Fintype (G.Walk u v) := Fintype.ofFinite _

variable {G}

protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
  G.Walk u' v' := hu ▸ hv ▸ p

@[simp]
theorem copy_heq_left {u v u'} (p : G.Walk u v) (hu : u = u') :
  p ≍ p.copy hu (Eq.refl v) := by
  subst hu
  rw [heq_eq_eq]
  rfl

@[simp]
theorem copy_heq_right {u v v'} (p : G.Walk u v) (hv : v = v') :
  p ≍ p.copy (Eq.refl u) hv := by
  subst hv
  rw [heq_eq_eq]
  rfl

@[simp]
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl

@[simp]
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu =
  Walk.nil := by
  subst_vars
  rfl

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u')
  (hw : w = w') : (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h)
  (p.copy rfl hw) := by
  subst_vars
  rfl

lemma copy_move {u v u' v'} {p : G.Walk u v} {p' : G.Walk u' v'}
  {hu : u = u'} {hv : v = v'} :
    p.copy hu hv = p' ↔ p = p'.copy hu.symm hv.symm := by
  subst_vars
  simp

@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

def length {u v} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl

@[simp]
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

theorem eq_nil_of_length_eq_zero {u : V} {p : G.Walk u u} (h : p.length = 0) :
  p = nil := by
  cases p <;> simp_all

lemma eq_nil_of_length_eq_zero'_aux {u v : V} {p : G.Walk u v} (h : p.length = 0) :
  u = v := by
  cases p <;> simp_all

lemma eq_nil_of_length_eq_zero' {u v : V} {p : G.Walk u v} (h : p.length = 0) :
  p = nil.copy (Eq.refl u) (eq_nil_of_length_eq_zero'_aux h) := by
  cases p
  · simp
  · simp at h

def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n

@[simp]
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u :=
  by cases w <;> rfl

@[simp]
theorem getVert_nil (u : V) {i : ℕ} : (@nil _ _ _ G u).getVert i = u := rfl

@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl

theorem getVert_of_ge_length {u v} (w : G.Walk u v) {i : ℕ}
  (hi : w.length ≤ i) : w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_ge_length rfl.le

@[simp]
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl

def Intersecting {u₁ v₁ u₂ v₂ : V} (p₁ : G.Walk u₁ v₁)
  (p₂ : G.Walk u₂ v₂) : Prop :=
    ∃ (k₁ k₂ : ℕ), p₁.getVert k₁ = p₂.getVert k₂

def weight {u v : V} : G.Walk u v → R
  | nil => 1
  | @cons _ _ _ _ u v _ h p => p.weight * ((G.weight u v).get h)

@[simp]
theorem nil_weight {u} : (Walk.nil : G.Walk u u).weight = 1 := by rfl

@[simp]
theorem cons_weight {u v w} (p : G.Walk v w) (h : G.Adj u v) :
  (p.cons h).weight = p.weight * ((G.weight u v).get h) := by rfl

def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

@[simp]
theorem copy_weight {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
  (p.copy hu hv).weight = p.weight := by
  subst hu hv
  rw [copy_rfl_rfl]

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w)
  (q : G.Walk w x) : (cons h p).append q = cons h (p.append q) := rfl

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

@[simp]
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p with
  | nil => rw [nil_append]
  | cons _ _ ih => rw [cons_append, ih]

theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl

theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i ≤ p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i with
  | nil => simp_all
  | cons _ _ ih => cases i <;> simp [getVert, ih]

@[simp]
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm, add_assoc]

theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w)
  (r : G.Walk w x) : p.append (q.append r) = (p.append q).append r := by
  induction p with
  | nil => simp only [nil_append]
  | cons _ _ ih => simp only [cons_append, ih]

@[simp]
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars
  rfl

@[simp]
theorem append_copy_copy' {u v v₁ v₂ w u' w'}
  (p : G.Walk u v₁) (q : G.Walk v₂ w) (hu : u = u') (hv₁ : v₁ = v)
  (hv₂ : v₂ = v) (hw : w = w') :
    (p.copy hu hv₁).append (q.copy hv₂ hw) = (p.append (q.copy (Eq.trans hv₂
    hv₁.symm) rfl)).copy hu hw := by
  subst_vars
  rfl

theorem weight_append {u v w} (p : G.Walk u v) (q : G.Walk v w) :
  (p.append q).weight = p.weight * q.weight := by
  induction p with
  | nil => simp
  | cons _ _ h => simp [h q]; ring

def iterLoop {u : V} (p : G.Walk u u) (k : ℕ) : G.Walk u u :=
  match k with
  | 0 => .nil
  | Nat.succ k => (iterLoop p k).append p

theorem iterLoop_length {u : V} (p : G.Walk u u) (k : ℕ) :
  (p.iterLoop k).length = k * p.length := by
  induction k with
  | zero => simp [iterLoop]
  | succ _ h => rw [iterLoop, length_append, h]; linarith

def take {u v : V} (p : G.Walk u v) (k : ℕ) : G.Walk u (p.getVert k) :=
  match p, k with
  | .nil, _ => .nil
  | .cons _ _, 0 => nil.copy rfl (getVert_zero _).symm
  | .cons h q, (k + 1) => .cons h (q.take k)

@[simp]
theorem take_zero {u v : V} (p : G.Walk u v) : p.take 0 =
  nil.copy rfl (getVert_zero _).symm := by
  cases p <;> simp [take]

@[simp]
lemma take_length {u v : V} (p : G.Walk u v) (n : ℕ) :
  (p.take n).length = n ⊓ p.length := by
  induction p generalizing n with
  | nil => simp [take]
  | cons => cases n <;> simp_all [take]

@[simp]
lemma take_getVert {u v : V} (p : G.Walk u v) (n m : ℕ) :
  (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m with
  | nil => simp [take]
  | cons => cases n <;> cases m <;> simp_all [take]

def drop {u v : V} (p : G.Walk u v) (k : ℕ) : G.Walk (p.getVert k) v :=
  match p, k with
  | .nil, _ => .nil
  | .cons e q, 0 => .cons e q
  | .cons _ q, (k + 1) => q.drop k

lemma drop_zero {u v} (p : G.Walk u v) :
  p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [drop]; rfl

@[simp]
lemma drop_length {u v : V} (p : G.Walk u v) (n : ℕ) :
  (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]; rfl

@[simp]
lemma drop_getVert {u v : V} (p : G.Walk u v) (n m : ℕ) :
  (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop, add_right_comm]; rfl

@[simp]
theorem append_take_drop_eq {u v : V} (p : G.Walk u v) (n : ℕ) :
  (p.take n).append (p.drop n) = p := by
  induction n generalizing p u with
  | zero => rw [take_zero, drop_zero, append_copy_copy, append]; rfl
  | succ _ ih => cases p with
    | nil => simp [take, drop]
    | cons _ r => simp [take, drop, ih r]

lemma take_append_of_le_length_aux {u v w : V} {p : G.Walk u v}
  {q : G.Walk v w} {n : ℕ} (h : n ≤ p.length) : p.getVert n =
  (p.append q).getVert n := by
  rw [getVert_append, ite_eq_left h]

theorem take_append_of_le_length {u v w : V} {p : G.Walk u v} (q : G.Walk v w)
  {n : ℕ} (h : n ≤ p.length) : (p.append q).take n =
  (p.take n).copy rfl (take_append_of_le_length_aux h) := by
  induction n generalizing u p with
  | zero => simp [take_zero]
  | succ n ih => cases p with
    | nil => grind [length_nil]
    | cons e r =>
      have hn : n ≤ r.length := by grind [length_cons]
      rw! [cons_append, take, take, ih hn]
      exact (copy_cons e (r.take n) _ _).symm

lemma drop_append_of_ge_length_aux {u v w : V} (p : G.Walk u v)
  (q : G.Walk v w) (n : ℕ) (h : p.length ≤ n) :
  q.getVert (n - p.length) = (p.append q).getVert n := by
  rw [getVert_append]
  rcases eq_or_lt_of_le' h with h | h <;> simp [h]

theorem drop_append_of_ge_length {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  (n : ℕ) (h : p.length ≤ n) : (p.append q).drop n =
  (q.drop (n - p.length)).copy (drop_append_of_ge_length_aux _ _ _ h) rfl := by
  induction p generalizing n with
  | nil => rw! [append, length_nil, Nat.sub_zero]; rfl
  | cons _ r ih =>
    rw [length_cons] at h
    have hn1 : n = n - 1 + 1 := by grind
    have hn2 : r.length ≤ n - 1 := by grind
    rw! [append, hn1, drop, ih _ _ hn2, length_cons, add_comm r.length 1,
         Nat.sub_add_eq, Nat.add_sub_cancel]; rfl

theorem take_of_le_length {u v : V} (p : G.Walk u v) (n : ℕ)
  (h : p.length ≤ n) :
  p.take n = p.copy rfl (getVert_of_ge_length p h).symm := by
  induction p generalizing n with
  | nil => simp [take]
  | cons _ q ih => 
    rw [length_cons] at h
    have hn1 : n = n - 1 + 1 := by grind
    have hn2 : q.length ≤ n - 1 := by grind
    rw! [hn1, take, ih (n - 1) hn2, copy_cons]; rfl

theorem acyclic_of_path_finite {u v : V} [hG : PathFinite G] (p : G.Walk u v)
  (i j : ℕ) (hne : i ≠ j) (hij : i < p.length ∨ j < p.length) :
    p.getVert i ≠ p.getVert j := by
  wlog hlt : i < j generalizing i j
  · push Not at hlt
    symm
    exact this j i hne.symm (Or.symm hij) (lt_of_le_of_ne hlt hne.symm)
  have hi : i < p.length := Or.elim hij id (fun h ↦ lt_trans hlt h)
  by_contra h
  let w := p.getVert i
  let q : G.Walk w w := ((p.drop i).take (j - i)).copy rfl
    (by rw [drop_getVert, Nat.add_sub_cancel' (le_of_lt hlt), ← h])
  have hq : q.length > 0 := by
    rw [length_copy, take_length, drop_length]
    exact Nat.lt_min.mpr ⟨Nat.sub_pos_of_lt hlt, Nat.sub_pos_of_lt hi⟩
  let f (n : ℕ) : G.Walk w w := q.iterLoop n
  have hf : Function.Injective f := by
    intro n m hnm
    replace hnm : (f n).length = (f m).length := by rw [hnm]
    rw [iterLoop_length, iterLoop_length] at hnm
    exact Nat.mul_right_cancel hq hnm
  exact (Infinite.of_injective f hf).not_finite (hG.fin_walks w w)

theorem finite_paths_of_fixed_length [Finite V] (k : ℕ) :
  ∀ (u v : V), Finite { p : G.Walk u v // p.length = k } := by
  induction k with
  | zero =>
    intro u v
    suffices _ : Fintype { p : G.Walk u v // p.length = 0 } from
      Finite.of_fintype _
    by_cases h : u = v
    · let S : Finset { p : G.Walk u v // p.length = 0 } :=
        singleton ⟨(@nil _ _ _ G u).copy (Eq.refl u) h, by simp⟩
      exact {
        elems := S
        complete := by
          rintro ⟨_, hp⟩
          apply Finset.mem_singleton.mpr
          simp [eq_nil_of_length_eq_zero' hp] }
    · exact {
        elems := {}
        complete := by
          rintro ⟨p, hp⟩
          exfalso
          exact h (eq_nil_of_length_eq_zero'_aux hp) }
  | succ k hk =>
    intro u v
    let := hk u v
    let f : { x : (w : V) × { p : G.Walk w v // p.length = k} // G.Adj u x.1 } →
      G.Walk u v := fun x => cons x.prop x.val.2
    let P : G.Walk u v → Prop := fun p => p.length = k + 1
    have hf : ∀ x, P (f x) := by
      intro x
      simp [P, f, x.val.2.prop]
    let f' := Subtype.coind f hf
    have hf' : Function.Surjective f' := by
      rintro ⟨p, hp⟩
      cases p with 
      | nil => simp [P] at hp
      | @cons _ w _ e q =>
        have hq : q.length = k := by
          simp only [length_cons, add_right_cancel_iff, P] at hp
          exact hp
        use ⟨⟨w, ⟨q, hq⟩⟩, e⟩
        simp [f', Subtype.coind, f]
    apply Finite.of_surjective f' hf'

theorem path_finite_of_bounded_length {k : ℕ} [Finite V]
  (h : ∀ (u v : V) (p : G.Walk u v), p.length < k) : PathFinite G := by
  refine { fin_walks := ?_ }
  intro u v
  let length' := Subtype.coind (@length _ _ _ G u v) (p := fun n => n < k)
    (h u v)
  apply (Equiv.finite_iff (f := (Equiv.sigmaFiberEquiv length').symm)).mpr
  suffices _ : ∀ (y : { n // n < k }), Finite { x // length' x = y } from
    Finite.instSigma
  rintro ⟨_, _⟩
  simp only [Subtype.coind, Subtype.mk.injEq, length']
  apply finite_paths_of_fixed_length

end Walk
end WDigraph

