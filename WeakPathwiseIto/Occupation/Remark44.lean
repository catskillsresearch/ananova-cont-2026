/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Basic.WeakLpTendsto

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

/-- **Remark 4.4** (density of the occupation measure). Let `ω ∈ C([0,T]; ℝ^d) ∩ Q_π` with (6)
and `𝓛^{π_n}_ω ⇀ ℓ^{ω,π}_T` in `L^r(ℝ^d)`, `r ∈ (1, ∞]` (weak-* for `r = ∞`), `ℓ ≥ 0`. Then
`ℓ` is the density of the quadratic-variation occupation measure:
`∫ φ ℓ dx = ∫_0^T φ(ω(t)) d tr[ω]_π(t)` for `φ ∈ C_c(ℝ^d)`. -/
theorem remark_4_4_density (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {φ : Rd d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x * ℓ x = ∫ t in Icc 0 T, φ (ω t) ∂hQV.traceMeasure := by
  sorry

/-- **Remark 4.4** (explicit seminorm). Under the hypotheses of `remark_4_4_density`, for every
`h ∈ L^{r'}(ℝ^d)`, `‖h‖_{W^0_{ω,π}} = ∫ |h(x)| ℓ^{ω,π}_T(x) dx = ‖h‖_{L^1(μ^π_{ω,T})}`. -/
theorem remark_4_4_seminorm (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {E : Type*} [NormedAddCommGroup E] {h : Rd d → E} (hh : MemLp h r.conjExponent) :
    occupationSeminorm π ω h = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (ℓ x) := by
  sorry

/-- **Remark 4.4** (inclusion). Under the hypotheses of `remark_4_4_density`,
`{F ∈ W^{2,1}(ℝ^d) ∩ C(ℝ^d) : ∇²F ∈ L^{r'}(ℝ^d)} ⊆ 𝓦^2_{ω,π}`, `r' = r/(r-1)`. -/
theorem remark_4_4 (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {F : Rd d → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hHr : MemLp H r.conjExponent) :
    F ∈ PathwiseSobolevSpace π ω := by
  sorry

end WeakPathwiseIto
