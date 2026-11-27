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

namespace IsItoIntegral

variable {d : ℕ} {T : ℝ}

set_option warn.classDefReducibility false in
/-- The natural `σ`-algebra `𝓕_u = σ(B(v) : 0 ≤ v ≤ u)` of the canonical process on `Ω`. -/
def naturalSigma (d : ℕ) (T u : ℝ) : MeasurableSpace (CanonicalWienerSpace d T) :=
  MeasurableSpace.comap (fun ω (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ u}) => ω v) inferInstance

/-- Value at time `u` of the elementary predictable integrand
`∑_j ξ_j 1_{(s_j, s_{j+1}]}(u)`. -/
def elementaryValue {k : ℕ} (s : Fin (k + 1) → ℝ) (ξ : Fin k → CanonicalWienerSpace d T → Rd d)
    (u : ℝ) (ω : CanonicalWienerSpace d T) : Rd d :=
  ∑ j : Fin k, (Ioc (s j.castSucc) (s j.succ)).indicator (fun _ => ξ j ω) u

/-- Elementary stochastic integral `∑_j ⟨ξ_j, B(s_{j+1}) - B(s_j)⟩`. -/
def elementaryIntegral {k : ℕ} (s : Fin (k + 1) → ℝ)
    (ξ : Fin k → CanonicalWienerSpace d T → Rd d) (ω : CanonicalWienerSpace d T) : ℝ :=
  ∑ j : Fin k, ⟪ξ j ω, CanonicalWienerSpace.path ω (s j.succ) -
    CanonicalWienerSpace.path ω (s j.castSucc)⟫

end IsItoIntegral

end WeakPathwiseIto
