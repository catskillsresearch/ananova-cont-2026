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

namespace MemW

/-- The finite set of multi-indices `α ∈ ℕ^d` with `|α| ≤ k`. -/
def multiIndices (d k : ℕ) : Finset (Fin d → ℕ) :=
  ((Finset.univ : Finset (Fin d → Fin (k + 1))).image fun α i => (α i : ℕ)).filter
    fun α => IsWeakDerivative.order α ≤ k

/-- The Sobolev norm `‖f‖_{W^{k,p}} := ∑_{|α| ≤ k} ‖D^α f‖_{L^p}` (Theorem 2.6), `D^0 f = f`.
Weak derivatives are unique a.e., so the infimum over versions is the norm of any version. -/
def norm {d : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : Rd d → ℝ) : ℝ≥0∞ :=
  ∑ α ∈ multiIndices d k, ⨅ (g : Rd d → ℝ) (_ : IsWeakDerivative α f g), eLpNorm g p volume

end MemW

end WeakPathwiseIto
