/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.PathwiseCovariation
public import WeakPathwiseIto.Occupation.ApproximatingSequence

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The covariation of a weak gradient (eq. (15)):
`[∇F(ω), ω]_π(t) := lim_m [∇F_m(ω), ω]_π(t)` along an approximating sequence. -/
def weakCovariation {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d} {F : Rd d → ℝ}
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (A : ApproximatingSequence π ω F H) (t : ℝ) : ℝ :=
  limUnder atTop fun m => pathwiseCovariation π (gradient (A.seq m)) ω t

end WeakPathwiseIto
