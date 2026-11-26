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
public import WeakPathwiseIto.Smooth.Proposition31
public import WeakPathwiseIto.Smooth.FollmerItoFormula

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace corollary_3_2

/-- **Subgoal** (Corollary 3.2 proof, "by Proposition 3.1"): for `f ∈ C^2_b`,
`[∇f(ω), ω]_π(T) = ∫_0^T ⟨∇²f(ω(t)), d[ω]_π(t)⟩`. -/
theorem pathwiseCovariation_eq {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    pathwiseCovariation π (gradient f) ω T = hQV.matrixIntegral
      (fun u i j => Rd.coord i (smoothHessian f (ω u) (Rd.basisVec j))) T := by
  have h := proposition_3_1 hω hQV hosc (follmer_ito_formula.contDiffBounded_gradient hf) T
    ⟨(π 0).nonneg, le_rfl⟩
  unfold pathwiseCovariation
  exact h.limUnder_eq

end corollary_3_2

/-- **Corollary 3.2.** For `ω ∈ C([0,T], ℝ^d) ∩ Q^π` (the paper states (6) as a standing assumption of Section 3,
"in the sequel we will fix a sequence of partitions π and assume (6)", so it is a hypothesis here) and `f ∈ C^2_b(ℝ^d, ℝ)`, the
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
