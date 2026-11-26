/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition
public import WeakPathwiseIto.Occupation.OccupationConstant
public import WeakPathwiseIto.Occupation.IncrementBall

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace discreteOccupationDensity

variable {d : ℕ}

open scoped Classical in
/-- The single-increment density `𝓛^{n,i}_ω(x) = c_d (|x - a|^{2-d} + |x - b|^{2-d}) 1_{Q}(x)`
for an increment from `a` to `b`, set to `0` when `a = b` (eq. (7)). -/
def piece (a b : Rd d) (x : Rd d) : ℝ :=
  if a = b then 0 else
    (incrementBall a b).indicator
      (fun x => occupationConstant d * (‖x - a‖ ^ (2 - (d : ℝ)) + ‖x - b‖ ^ (2 - (d : ℝ)))) x

end discreteOccupationDensity

/-- The discrete weighted occupation density `𝓛^{π_n}_ω := ∑_i 𝓛^{n,i}_ω` (eq. (7)). -/
def discreteOccupationDensity {T : ℝ} {d : ℕ} (π : Partition T) (ω : ℝ → Rd d) (x : Rd d) : ℝ :=
  ∑ i : Fin π.m, discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x

namespace discreteOccupationDensity

variable {T : ℝ} {d : ℕ}

/-- **Subgoal** (Eq. (7)). -/
theorem piece_nonneg (a b x : Rd d) : 0 ≤ piece a b x := by
  sorry

/-- **Subgoal** (Eq. (7)). By homogeneity, `∫ 𝓛^{n,i}_ω = |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem integral_piece (a b : Rd d) : ∫ x, piece a b x = ‖b - a‖ ^ 2 := by
  sorry

/-- **Subgoal** (Eq. (7)). -/
theorem integrable_piece (a b : Rd d) : Integrable (piece a b) := by
  sorry

/-- **Subgoal** (Eq. (7)). `∫ 𝓛^{π_n}_ω = ∑_i |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem integral_eq (π : Partition T) (ω : ℝ → Rd d) :
    ∫ x, discreteOccupationDensity π ω x = ∑ i : Fin π.m, ‖ω (π.right i) - ω (π.left i)‖ ^ 2 := by
  sorry

end discreteOccupationDensity

end WeakPathwiseIto
