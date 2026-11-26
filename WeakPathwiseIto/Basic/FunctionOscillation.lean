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
  have hu := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hφ)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hu (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
  have hx0 : 0 < x := hx
  rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hxδ
  have hle : functionOscillation φ x ≤ ε / 2 := by
    refine Real.iSup_le (fun p => Real.iSup_le (fun hp => ?_) (by positivity)) (by positivity)
    have := hδε (lt_of_le_of_lt hp hxδ)
    rw [dist_eq_norm] at this
    exact this.le
  have h0 : 0 ≤ functionOscillation φ x :=
    Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end functionOscillation

end WeakPathwiseIto
