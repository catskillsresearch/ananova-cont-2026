/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Main.WeakPathwiseIntegral
public import WeakPathwiseIto.Main.WeakCovariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

/-- **Theorem 5.1** (existence of the limits (14) and (15)). -/
theorem theorem_5_1_tendsto (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) :
    ∀ t ∈ Icc 0 T,
      Tendsto (fun m => follmerIntegral π (gradient (A.seq m)) ω t) atTop
          (𝓝 (weakPathwiseIntegral A t)) ∧
        Tendsto (fun m => pathwiseCovariation π (gradient (A.seq m)) ω t) atTop
          (𝓝 (weakCovariation A t)) := by
  sorry

/-- **Theorem 5.1** (independence of the approximating sequence). -/
theorem theorem_5_1_unique (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H H' : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H')
    (A : ApproximatingSequence π ω F H) (A' : ApproximatingSequence π ω F H') :
    ∀ t ∈ Icc 0 T, weakPathwiseIntegral A' t = weakPathwiseIntegral A t ∧
      weakCovariation A' t = weakCovariation A t := by
  sorry

/-- **Theorem 5.1** (pathwise integration and weak change-of-variable formula). Let
`ω ∈ C([0,T]; ℝ^d) ∩ Q_π([0,T]; ℝ^d)` satisfy (6), `F ∈ 𝓦^2_{ω,π}` and `(F_m)` satisfy (12),
(13). Then for all `t ∈ [0, T]`, eq. (17):
`F(ω(t)) - F(ω(0)) = ∫_0^t ∇F(ω(s)) d^π ω(s) + ½ [∇F(ω), ω]_π(t)`. -/
theorem theorem_5_1 (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) :
    ∀ t ∈ Icc 0 T, F (ω t) - F (ω 0) = weakPathwiseIntegral A t + 1 / 2 * weakCovariation A t := by
  sorry

end WeakPathwiseIto
