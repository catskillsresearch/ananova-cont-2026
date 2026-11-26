/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The oscillation of `ω` along `π_n` (eq. (6)):
`osc(ω, π_n) := max_i sup_{t ∈ [t_i, t_{i+1}]} |ω(t) - ω(t_i)|`. -/
def pathOscillation {T : ℝ} {d : ℕ} (ω : ℝ → Rd d) (π : Partition T) : ℝ :=
  ⨆ i : Fin π.m, ⨆ (s : ℝ) (_ : s ∈ Icc (π.left i) (π.right i)), ‖ω s - ω (π.left i)‖

namespace pathOscillation

variable {T : ℝ} {d : ℕ}

/-- Condition (6): `osc(ω, π_n) → 0`. -/
def Vanishes (ω : ℝ → Rd d) (π : ℕ → Partition T) : Prop :=
  Tendsto (fun n => pathOscillation ω (π n)) atTop (𝓝 0)

/-- **Subgoal** (Eq. (6)). Section 3: if `|π_n| → 0` and `ω` is continuous, condition (6) holds. -/
theorem vanishes_of_mesh {ω : ℝ → Rd d} {π : ℕ → Partition T}
    (hω : ContinuousOn ω (Icc 0 T)) (hπ : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    Vanishes ω π := by
  sorry

end pathOscillation

end WeakPathwiseIto
