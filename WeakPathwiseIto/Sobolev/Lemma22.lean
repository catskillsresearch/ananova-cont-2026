/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Lemma 2.2.** For `α > 0` there is `C_{α,d}` such that for every ball `Q`, every
`f ∈ L^1(Q)` and every `x ∈ Q`,
`∫_Q |f(y)| / |x - y|^{d-α} dy ≤ C_{α,d} (diam Q)^α M_{diam Q} f(x)`. -/
theorem lemma_2_2 (d : ℕ) {α : ℝ} (hα : 0 < α) : ∃ C : ℝ≥0, 0 < C ∧
    ∀ (c : Rd d) (ρ : ℝ) (f : Rd d → ℝ), IntegrableOn f (Metric.ball c ρ) →
      ∀ x ∈ Metric.ball c ρ,
        ∫⁻ y in Metric.ball c ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
          C * Metric.ediam (Metric.ball c ρ) ^ α *
            localMaximalFunction (Metric.ediam (Metric.ball c ρ)) f x := by
  sorry

end WeakPathwiseIto
