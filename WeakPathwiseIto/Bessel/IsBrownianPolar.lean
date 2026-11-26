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

/-- A polar set for Brownian motion (Definition 2.8), on the canonical space
`Ω = C([0, T], ℝ^d)`: `ℙ_x(B(t) ∈ E for some t > 0) = 0` for all `x ∈ ℝ^d`. -/
def IsBrownianPolar (d : ℕ) (T : ℝ) (S : Set (Rd d)) : Prop :=
  ∀ x, CanonicalWienerSpace.P (T := T) x {ω | ∃ t : Icc (0 : ℝ) T, 0 < (t : ℝ) ∧ ω t ∈ S} = 0

namespace IsBrownianPolar

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Definition 2.8, [Fuk93, p. 25]). [Fuk93, p. 25]: `E` is polar iff `E` is `(1, 2)`-polar. -/
theorem iff_isNull (hT : 0 < T) (S : Set (Rd d)) :
    IsBrownianPolar d T S ↔ besselCapacity.IsNull d 1 2 S := by
  sorry

/-- **Subgoal** (Definition 2.8, countable unions). A countable union of polar sets is polar. -/
theorem iUnion {S : ℕ → Set (Rd d)} (h : ∀ n, IsBrownianPolar d T (S n)) :
    IsBrownianPolar d T (⋃ n, S n) := by
  sorry

end IsBrownianPolar

end WeakPathwiseIto
