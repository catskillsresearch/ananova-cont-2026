/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

open scoped Classical in
/-- The discrete quadratic variation of eq. (5):
`∑_{t_{i+1} ≤ t} (x(t_{i+1}) - x(t_i))²` along a partition `π_n`. -/
def discreteQuadraticVariation {T : ℝ} (π : Partition T) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => π.right i ≤ t), (x (π.right i) - x (π.left i)) ^ 2

end WeakPathwiseIto
