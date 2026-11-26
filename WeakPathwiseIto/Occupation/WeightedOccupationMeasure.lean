/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.HasQuadraticVariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The quadratic-variation weighted occupation measure (Lemma 4.2):
`μ^T_ω(A) := tr ∫_0^T 1_A(ω(t)) d[ω]_π(t)`, i.e. the image of `d tr[ω]_π` on `[0, T]`
under `ω`. -/
def weightedOccupationMeasure {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (h : HasQuadraticVariation π ω) : Measure (Rd d) :=
  (h.traceMeasure.restrict (Icc 0 T)).map ω

namespace weightedOccupationMeasure

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

/-- **Subgoal** (Lemma 4.2). `∫ φ dμ^T_ω = ∫_0^T φ(ω(t)) d tr[ω]_π(t)` for continuous `φ`. -/
theorem integral_eq (hω : ContinuousOn ω (Icc 0 T)) (h : HasQuadraticVariation π ω)
    {φ : Rd d → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂weightedOccupationMeasure h = ∫ t in Icc 0 T, φ (ω t) ∂h.traceMeasure := by
  sorry

end weightedOccupationMeasure

end WeakPathwiseIto
