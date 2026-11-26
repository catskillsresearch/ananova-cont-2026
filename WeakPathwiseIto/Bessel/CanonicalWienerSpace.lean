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

/-- The canonical Wiener space `(Ω, B, ℙ_x)` (Section 2.2): paths `ω : ℝ_{≥0} → ℝ^d` with
coordinate process `B(t)(ω) = ω(t)`, and for each `x` a probability `ℙ_x` under which `B` is a
continuous `d`-dimensional Brownian motion started at `x` (independent standard real Brownian
coordinates). -/
structure CanonicalWienerSpace (d : ℕ) where
  /-- The law `ℙ_x` of Brownian motion started at `x`. -/
  P : Rd d → Measure (ℝ≥0 → Rd d)
  isProbability : ∀ x, IsProbabilityMeasure (P x)
  start : ∀ x, ∀ᵐ ω ∂(P x), ω 0 = x
  continuous : ∀ x, ∀ᵐ ω ∂(P x), Continuous ω
  coord_brownian : ∀ x (i : Fin d),
    ProbabilityTheory.IsBrownianReal (fun t ω => Rd.coord i (ω t - x)) (P x)
  coord_indep : ∀ x, ProbabilityTheory.iIndepFun
    (fun (i : Fin d) (ω : ℝ≥0 → Rd d) (t : ℝ≥0) => Rd.coord i (ω t)) (P x)

namespace CanonicalWienerSpace

variable {d : ℕ}

/-- A Brownian path viewed as a path `ℝ → ℝ^d` (constant on `(-∞, 0]`), to which the
pathwise theory along partitions of `[0, T]` applies. -/
def pathOn (ω : ℝ≥0 → Rd d) : ℝ → Rd d := fun t => ω t.toNNReal

/-- The canonical Wiener space exists. -/
theorem nonempty (d : ℕ) : Nonempty (CanonicalWienerSpace d) := by
  sorry

end CanonicalWienerSpace

end WeakPathwiseIto
