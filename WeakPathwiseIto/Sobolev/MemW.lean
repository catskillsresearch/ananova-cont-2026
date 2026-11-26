/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakDerivative

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Sobolev space `W^{k,p}(ℝ^d)` (Section 2.1): `f ∈ L^p` and every weak derivative
`D^α f`, `|α| ≤ k`, exists and lies in `L^p`. -/
def MemW {d : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : Rd d → ℝ) : Prop :=
  MemLp f p ∧ ∀ α : Fin d → ℕ, IsWeakDerivative.order α ≤ k →
    ∃ g : Rd d → ℝ, IsWeakDerivative α f g ∧ MemLp g p

end WeakPathwiseIto
