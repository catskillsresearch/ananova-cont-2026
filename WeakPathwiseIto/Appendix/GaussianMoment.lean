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

/-- The Gaussian moment `c_{q,d} := 𝔼|Z|^{2q}`, `Z ∼ N(0, I_d)` (Lemma A.1). -/
def gaussianMoment (d : ℕ) (q : ℝ) : ℝ :=
  ∫ z, ‖z‖ ^ (2 * q) ∂(ProbabilityTheory.stdGaussian (Rd d))

end WeakPathwiseIto
