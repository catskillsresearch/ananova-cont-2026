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

/-- `C^k_b`: `f` is `k` times continuously differentiable and all its derivatives of order
`≤ k` are bounded (the spaces `C^1_b`, `C^2_b` of the paper). -/
def ContDiffBounded {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (f : E → F) : Prop :=
  ContDiff ℝ k f ∧ ∀ i ≤ k, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C

end WeakPathwiseIto
