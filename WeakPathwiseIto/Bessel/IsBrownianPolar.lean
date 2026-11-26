/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Bessel.BesselCapacity

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- A polar set for Brownian motion (Definition 2.8):
`ℙ_x(B(t) ∈ E for some t > 0) = 0` for all `x ∈ ℝ^d`. -/
def IsBrownianPolar {d : ℕ} (W : CanonicalWienerSpace d) (S : Set (Rd d)) : Prop :=
  ∀ x, W.P x {ω | ∃ t : ℝ≥0, 0 < t ∧ ω t ∈ S} = 0

namespace IsBrownianPolar

variable {d : ℕ} (W : CanonicalWienerSpace d)

/-- [Fuk93, p. 25]: `E` is polar iff `E` is `(1, 2)`-polar. -/
theorem iff_isNull (S : Set (Rd d)) : IsBrownianPolar W S ↔ besselCapacity.IsNull d 1 2 S := by
  sorry

/-- A countable union of polar sets is polar. -/
theorem iUnion {S : ℕ → Set (Rd d)} (h : ∀ n, IsBrownianPolar W (S n)) :
    IsBrownianPolar W (⋃ n, S n) := by
  sorry

end IsBrownianPolar

end WeakPathwiseIto
