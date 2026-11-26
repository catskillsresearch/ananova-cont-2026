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

/-- The ball `Q^n_i := {x : |x - (a + b)/2| ≤ |b - a| / 2}` spanned by an increment from
`a = ω(t_i)` to `b = ω(t_{i+1})` (eq. (7)). -/
def incrementBall {d : ℕ} (a b : Rd d) : Set (Rd d) :=
  Metric.closedBall (midpoint ℝ a b) (dist a b / 2)

end WeakPathwiseIto
