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

/-- **Theorem 2.6** ([Ste70]). For `k ≥ 1` and `1 < p < ∞`, `𝓛^p_k(ℝ^d) = W^{k,p}(ℝ^d)`:
`F ∈ 𝓛^p_k` iff `F ∈ W^{k,p}`, and the norms `‖·‖_{𝓛^p_k}` and `‖·‖_{W^{k,p}}` are equivalent. -/
theorem theorem_2_6 (d : ℕ) {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp : 1 < p) :
    (∀ F : Rd d → ℝ, F ∈ BesselSpace d k (ENNReal.ofReal p) ↔ MemW k (ENNReal.ofReal p) F) ∧
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧ ∀ F : Rd d → ℝ, MemW k (ENNReal.ofReal p) F →
      BesselSpace.norm (k : ℝ) (ENNReal.ofReal p) F ≤ C₁ * MemW.norm k (ENNReal.ofReal p) F ∧
      MemW.norm k (ENNReal.ofReal p) F ≤ C₂ * BesselSpace.norm (k : ℝ) (ENNReal.ofReal p) F := by
  sorry

end WeakPathwiseIto
