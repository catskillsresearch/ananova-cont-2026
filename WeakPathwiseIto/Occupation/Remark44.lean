/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Smooth.HasQuadraticVariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Remark 4.4.** If `𝓛^{π_n}_ω ⇀ ℓ^{ω,π}_T` weakly in `L^r(ℝ^d)`, `r ∈ (1, ∞)`, then
`{F ∈ W^{2,1} ∩ C : ∇²F ∈ L^{r'}} ⊆ 𝓦^2_{ω,π}`, `r' = r/(r-1)`. -/
theorem remark_4_4 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω) {r : ℝ} (hr : 1 < r)
    {ℓ : Rd d → ℝ} (hℓ : MemLp ℓ (ENNReal.ofReal r)) (hℓ0 : 0 ≤ ℓ)
    (hweak : ∀ g : Rd d → ℝ, MemLp g (ENNReal.ofReal (r / (r - 1))) →
      Tendsto (fun n => ∫ x, g x * discreteOccupationDensity (π n) ω x) atTop
        (𝓝 (∫ x, g x * ℓ x)))
    {F : Rd d → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hHr : MemLp H (ENNReal.ofReal (r / (r - 1)))) :
    F ∈ PathwiseSobolevSpace π ω := by
  sorry

end WeakPathwiseIto
