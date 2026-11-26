/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- Modulus of oscillation `osc(φ, δ) := sup {‖φ x - φ y‖ : |x - y| ≤ δ}` (Section 4). -/
def functionOscillation {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    (φ : E → F) (δ : ℝ) : ℝ :=
  ⨆ (p : E × E) (_ : dist p.1 p.2 ≤ δ), ‖φ p.1 - φ p.2‖

namespace functionOscillation

/-- **Subgoal** (Theorem 5.1 proof, Section 4 osc(φ,δ)). `osc(φ, δ) → 0` as `δ → 0` for a continuous compactly supported `φ`. -/
theorem tendsto_zero {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] {φ : E → F}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (functionOscillation φ) (𝓝[>] 0) (𝓝 0) := by
  sorry

end functionOscillation

end WeakPathwiseIto
