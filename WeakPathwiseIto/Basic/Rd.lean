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

/-- The Euclidean space `ℝ^d` in which all paths and functions of the paper take values. -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

namespace Rd

variable {d : ℕ}

/-- The standard basis vector `e_i` of `ℝ^d`. -/
def basisVec (i : Fin d) : Rd d := EuclideanSpace.single i 1

/-- The `i`-th coordinate `v^i = ⟨v, e_i⟩` of a vector `v ∈ ℝ^d`. -/
def coord (i : Fin d) (v : Rd d) : ℝ := ⟪v, basisVec i⟫

end Rd

end WeakPathwiseIto
