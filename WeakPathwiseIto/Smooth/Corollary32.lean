/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Smooth.FollmerIntegral
public import WeakPathwiseIto.Smooth.PathwiseCovariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Corollary 3.2.** For `ω ∈ C([0,T], ℝ^d) ∩ Q^π` (with (6)) and `f ∈ C^2_b(ℝ^d, ℝ)`, the
left Riemann sums of `∇f(ω)` converge and
`f(ω(T)) = f(ω(0)) + ∫_0^T ∇f(ω) d^π ω + ½ [∇f(ω), ω]_π(T)`. -/
theorem corollary_3_2 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    Tendsto (fun n => follmerIntegral.riemannSum (π n) (gradient f) ω T) atTop
        (𝓝 (follmerIntegral π (gradient f) ω T)) ∧
      f (ω T) = f (ω 0) + follmerIntegral π (gradient f) ω T +
        1 / 2 * pathwiseCovariation π (gradient f) ω T := by
  sorry

end WeakPathwiseIto
