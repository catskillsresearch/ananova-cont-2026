/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.DiscreteOccupationDensity
public import WeakPathwiseIto.Occupation.WeightedOccupationMeasure
public import WeakPathwiseIto.Smooth.PathOscillation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Lemma 4.2.** For `ω ∈ Q_π([0,T], ℝ^d)` satisfying (6), the densities `𝓛^{π_n}_ω` converge
weakly to the weighted occupation measure `μ^T_ω`: for every `φ ∈ C_c(ℝ^d)`,
`∫ φ 𝓛^{π_n}_ω dx → ∫ φ dμ^T_ω`. -/
theorem lemma_4_2 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {φ : Rd d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, φ x * discreteOccupationDensity (π n) ω x) atTop
      (𝓝 (∫ x, φ x ∂weightedOccupationMeasure hQV)) := by
  sorry

end WeakPathwiseIto
