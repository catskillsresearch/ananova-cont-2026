/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselCapacity
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsLebesguePoint

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.9** ([BH93, Cor. 4]). For `k ∈ ℕ` and `1 < p < ∞`, the set of non-Lebesgue
points of any `F ∈ W^{k,p}(ℝ^d)` is `(k, p)`-polar. -/
theorem theorem_2_9 (d k : ℕ) {p : ℝ} (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW k (ENNReal.ofReal p) F) :
    besselCapacity.IsNull d k (ENNReal.ofReal p) {x | ¬ IsLebesguePoint F x} := by
  sorry

end WeakPathwiseIto
