/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Occupation.NormalizedQuadraticDensity
public import WeakPathwiseIto.Appendix.GaussianMoment

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

/-- **Lemma A.1.** If `∑_n |π_n| < ∞` and `q > 1`, then
`‖ρ_{n,B}‖^q_{L^q([0,T])} → c_{q,d} T`, `ℙ_x`-almost surely. -/
theorem lemma_A_1 (W : CanonicalWienerSpace d) {π : ℕ → Partition T}
    (hπ : Summable fun n => (π n).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(W.P x), Tendsto
      (fun n => ∫ t in Icc 0 T, |normalizedQuadraticDensity (π n) (CanonicalWienerSpace.pathOn ω) t| ^ q)
      atTop (𝓝 (gaussianMoment d q * T)) := by
  sorry

/-- **Lemma A.1** (consequence): `sup_n ‖ρ_{n,B}‖_{L^q([0,T])} < ∞`, `ℙ_x`-almost surely. -/
theorem lemma_A_1_bounded (W : CanonicalWienerSpace d) {π : ℕ → Partition T}
    (hπ : Summable fun n => (π n).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(W.P x), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) (CanonicalWienerSpace.pathOn ω))
        (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K := by
  sorry

end WeakPathwiseIto
