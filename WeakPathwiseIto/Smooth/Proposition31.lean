/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Smooth.PathwiseCovariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Proposition 3.1.** Let `ω ∈ C^0([0,T], ℝ^d) ∩ Q^π` satisfy (6). For `f ∈ C^1_b(ℝ^d, ℝ^d)`
the limit `[f(ω), ω]_π(t)` exists and equals `∫_0^t ⟨∇f(ω(u)), d[ω]_π(u)⟩`. -/
theorem proposition_3_1 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f) :
    ∀ t ∈ Icc 0 T, Tendsto (fun n => pathwiseCovariation.riemannSum (π n) f ω t) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
  sorry

end WeakPathwiseIto
