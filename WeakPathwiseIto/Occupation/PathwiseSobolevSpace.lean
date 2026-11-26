/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Occupation.ApproximatingSequence

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The pathwise Sobolev space `𝓦^2_{ω,π}` (Definition 4.3, eq. (9)): functions
`F ∈ W^{2,1}(ℝ^d)` admitting an approximating sequence satisfying (8). -/
def PathwiseSobolevSpace {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (ω : ℝ → Rd d) : Set (Rd d → ℝ) :=
  {F | MemW 2 1 F ∧ ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H ∧
    Nonempty (ApproximatingSequence π ω F H)}

namespace PathwiseSobolevSpace

variable {T : ℝ} {d : ℕ}

/-- **Subgoal** (Definition 4.3). Section 4.2: `C^2_b(ℝ^d) ∩ W^{2,1}(ℝ^d) ⊂ 𝓦^2_{ω,π}`. -/
theorem contDiffBounded_subset (π : ℕ → Partition T) (ω : ℝ → Rd d) :
    {F : Rd d → ℝ | ContDiffBounded 2 F ∧ MemW 2 1 F} ⊆ PathwiseSobolevSpace π ω := by
  sorry

end PathwiseSobolevSpace

end WeakPathwiseIto
