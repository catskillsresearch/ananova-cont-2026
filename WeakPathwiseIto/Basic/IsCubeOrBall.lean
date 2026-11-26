/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace IsCubeOrBall

variable {d : ℕ}

/-- The open axis-parallel cube `{y : |y^i - c^i| < r ∀ i}` of centre `c` and half-side `r`. -/
def openCube (c : Rd d) (r : ℝ) : Set (Rd d) := {y | ∀ i, |Rd.coord i (y - c)| < r}

/-- The closed axis-parallel cube `{y : |y^i - c^i| ≤ r ∀ i}` of centre `c` and half-side `r`. -/
def closedCube (c : Rd d) (r : ℝ) : Set (Rd d) := {y | ∀ i, |Rd.coord i (y - c)| ≤ r}

end IsCubeOrBall

/-- `Q ⊂ ℝ^d` is "either a cube or a ball" (Section 2.1, before Theorem 2.1): an open or closed
Euclidean ball, or an open or closed axis-parallel cube, of positive radius (half-side). -/
def IsCubeOrBall {d : ℕ} (Q : Set (Rd d)) : Prop :=
  ∃ (c : Rd d) (r : ℝ), 0 < r ∧
    (Q = Metric.ball c r ∨ Q = Metric.closedBall c r ∨
      Q = IsCubeOrBall.openCube c r ∨ Q = IsCubeOrBall.closedCube c r)

end WeakPathwiseIto
