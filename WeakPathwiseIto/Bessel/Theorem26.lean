/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselSpace
public import WeakPathwiseIto.Sobolev.MemW

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.6** ([Ste70]). For `k ≥ 1` and `1 < p < ∞`, `𝓛^p_k(ℝ^d) = W^{k,p}(ℝ^d)`. -/
theorem theorem_2_6 (d : ℕ) {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp : 1 < p) (F : Rd d → ℝ) :
    F ∈ BesselSpace d k (ENNReal.ofReal p) ↔ MemW k (ENNReal.ofReal p) F := by
  sorry

end WeakPathwiseIto
