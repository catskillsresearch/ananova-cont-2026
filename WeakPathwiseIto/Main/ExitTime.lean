/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace CanonicalWienerSpace

variable {d : ℕ} {T : ℝ}

/-- The exit time `τ_R := inf{t ≥ 0 : |B(t)| ≥ R}` of the canonical process from the ball `B_R`
(proof of Proposition 5.3), with values in `[0, ∞]` and `inf ∅ = ∞`. Since `Ω = C([0, T], ℝ^d)`
(Section 2.2), `B(t)` is a coordinate of `ω` only for `t ∈ [0, T]`; for `R > 0` the times
`t > T` (where `B(t) = 0`) never enter the set, so `τ_R = ∞` exactly when the path stays in
`B_R` on `[0, T]` (the paper's "`τ_R > T`"). -/
def exitTime (R : ℝ) (ω : CanonicalWienerSpace d T) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : R ≤ ‖B (t : ℝ) ω‖), (t : ℝ≥0∞)

end CanonicalWienerSpace

end WeakPathwiseIto
