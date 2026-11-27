/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The non-anticipative Riemann sum of the proof of Proposition 5.3 along a partition
`π = {t_0 < ⋯ < t_m}` of `[0, T]`, for a vector field `g` (the paper takes `g = ∇F_m`):
`S(t) := ∑_{i=0}^{m-1} g(B(t_i)) · (B(t_{i+1} ∧ t) - B(t_i ∧ t))` (the paper's `S_n^m(t)` for
`π = π_n`, `g = ∇F_m`). -/
def itoRiemannSum {d : ℕ} {T : ℝ} (π : Partition T) (g : Rd d → Rd d) (t : ℝ)
    (ω : CanonicalWienerSpace d T) : ℝ :=
  ∑ i : Fin π.m, ⟪g (CanonicalWienerSpace.path ω (π.left i)),
    CanonicalWienerSpace.path ω (min (π.right i) t) -
      CanonicalWienerSpace.path ω (min (π.left i) t)⟫

end WeakPathwiseIto
