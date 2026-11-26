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

/-- The local Sobolev space `W^{k,p}_loc(ℝ^d)`: `f` and its weak derivatives of order `≤ k`
are `L^p` on every compact set. -/
def MemWLoc {d : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : Rd d → ℝ) : Prop :=
  (∀ K : Set (Rd d), IsCompact K → MemLp f p (volume.restrict K)) ∧
    ∀ α : Fin d → ℕ, IsWeakDerivative.order α ≤ k →
      ∃ g : Rd d → ℝ, IsWeakDerivative α f g ∧
        ∀ K : Set (Rd d), IsCompact K → MemLp g p (volume.restrict K)

end WeakPathwiseIto
