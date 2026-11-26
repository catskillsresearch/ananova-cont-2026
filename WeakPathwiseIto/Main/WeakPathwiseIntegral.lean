/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.FollmerIntegral
public import WeakPathwiseIto.Occupation.ApproximatingSequence

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The pathwise integral of a weak gradient (eq. (16)):
`∫_0^t ∇F(ω(s)) d^π ω(s) := lim_m ∫_0^t ∇F_m(ω(s)) d^π ω(s)` along an approximating sequence. -/
def weakPathwiseIntegral {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d} {F : Rd d → ℝ}
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (A : ApproximatingSequence π ω F H) (t : ℝ) : ℝ :=
  limUnder atTop fun m => follmerIntegral π (gradient (A.seq m)) ω t

end WeakPathwiseIto
