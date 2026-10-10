/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import FormalBook.Chapter_27.Model
public import FormalBook.Chapter_27.Barbier
public import FormalBook.Chapter_27.Circle
public import FormalBook.Chapter_27.Distribution
public import FormalBook.Chapter_27.CountModel

/-!
# Buffon's needle problem

# Source and scope

Chapter 27 of Aigner–Ziegler, *Proofs from THE BOOK*, sixth edition (2018).
The independent uniform position/inclination model is in `Chapter27.Model`;
crossing counts, both probability formulas, all three long-needle exercises,
and the circular needle are treated explicitly.

`BarbierExpectation` isolates the additive-monotone argument. The regular polygon
perimeters, their limiting values, and Barbier's squeeze are formalized separately.
The geometric polygon comparison hypotheses in that abstract squeeze are explicit;
the main probability theorems below do not assume them.
-/

@[expose] public section

namespace Chapter27

/-- **Buffon's needle theorem** for a short needle in the independent uniform
position and inclination model. -/
theorem buffon_needle {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d) (hld : l ≤ d) :
    needleProbability l d = 2 * l / (Real.pi * d) := by
  rw [needleProbability_eq_crossingProbability hl hd, crossingProbability_short hl hd hld]
  field_simp

/-- For short needles, the expected number of crossings is the crossing probability. -/
theorem expectedCrossings_eq_probability {l d : ℝ} (hl : 0 ≤ l) (hd : 0 < d)
    (hld : l ≤ d) : expectedCrossings l d = needleProbability l d := by
  rw [expectedCrossings_eq, buffon_needle hl hd hld]

/-- The long-needle formula from the chapter, including the boundary `l = d`. -/
theorem buffon_long_needle {l d : ℝ} (hd : 0 < d) (hdl : d ≤ l) :
    needleProbability l d = 1 + (2 / Real.pi) *
      ((l / d) * (1 - Real.sqrt (1 - d ^ 2 / l ^ 2)) - Real.arcsin (d / l)) := by
  rw [needleProbability_eq_crossingProbability (hd.le.trans hdl) hd,
    crossingProbability_long hd hdl]

/-- First long-needle exercise: the two formulas agree at the boundary. -/
theorem buffon_boundary {d : ℝ} (hd : 0 < d) : needleProbability d d = 2 / Real.pi := by
  rw [needleProbability_eq_crossingProbability hd.le hd, crossingProbability_boundary hd]

/-- Second exercise: the crossing probability increases strictly with length. -/
theorem needleProbability_strictMono {d : ℝ} (hd : 0 < d) :
    StrictMonoOn (fun l => needleProbability l d) (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [needleProbability_eq_crossingProbability hx hd,
    needleProbability_eq_crossingProbability hy hd]
  exact crossingProbability_strictMono hd hx hy hxy

/-- Third exercise: a very long needle crosses a line with probability tending to one. -/
theorem needleProbability_tendsto_one {d : ℝ} (hd : 0 < d) :
    Filter.Tendsto (fun l => needleProbability l d) Filter.atTop (nhds 1) := by
  apply (crossingProbability_tendsto_one hd).congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with l hl
  exact (needleProbability_eq_crossingProbability hl hd).symm

/-- The genuine crossing expectation supplies Barbier's additive-monotone hypotheses. -/
theorem expectedCrossings_barbier {d : ℝ} (hd : 0 < d) :
    BarbierExpectation (fun l => expectedCrossings l d) where
  add x y _ _ := expectedCrossings_add x y d
  monotone _ _ _ _ h := expectedCrossings_mono hd h

end Chapter27
