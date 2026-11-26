/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Appendix.PotentialProfile

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Lemma B.1.** For `h ∈ L^1(ℝ^d)` there is a polar set `E` such that
`∫ |h(x)| ν(|x - x₀|) dx < ∞` for every `x₀ ∉ E`. -/
theorem lemma_B_1 {d : ℕ} (T : ℝ) {h : Rd d → ℝ} (hh : Integrable h) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
      ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) < ⊤ := by
  sorry

end WeakPathwiseIto
