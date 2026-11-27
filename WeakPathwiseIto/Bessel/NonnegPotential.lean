/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselKernel

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace BesselSpace

/-- The Bessel potential `g_α ⋆ h ∈ [0, ∞]` of a nonnegative function `h` (Definition 2.7),
as an extended-real (lower Lebesgue) integral, so that it takes the value `∞` where the
integral diverges; with the convention `g_0 ⋆ h = h`. -/
def nonnegPotential (d : ℕ) (α : ℝ) (h : Rd d → ℝ) : Rd d → ℝ≥0∞ :=
  if α = 0 then fun x => ENNReal.ofReal (h x) else
    fun x => ∫⁻ y, ENNReal.ofReal (besselKernel d α (x - y)) * ENNReal.ofReal (h y)

end BesselSpace

end WeakPathwiseIto
