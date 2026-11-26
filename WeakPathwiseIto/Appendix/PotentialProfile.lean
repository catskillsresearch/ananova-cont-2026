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

/-- The kernel profile `ν` of eq. (33): `ν(r) = 1` for `d = 1`, `1 + log⁺(1/r)` for `d = 2`,
and `r^{2-d}` for `d ≥ 3`. -/
def potentialProfile (d : ℕ) (r : ℝ) : ℝ :=
  if d = 1 then 1 else if d = 2 then 1 + max 0 (Real.log (1 / r)) else r ^ (2 - (d : ℝ))

end WeakPathwiseIto
