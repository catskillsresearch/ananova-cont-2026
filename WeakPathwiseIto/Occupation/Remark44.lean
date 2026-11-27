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
public import WeakPathwiseIto.Occupation.Lemma42

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
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (_hr : 1 < r) {ℓ : Rd d → ℝ} (_hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {φ : Rd d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x * ℓ x = ∫ t in Icc 0 T, φ (ω t) ∂hQV.traceMeasure := by
  have h1 := hweak.2.2 φ (hφ.memLp_of_hasCompactSupport hφc)
  have h2 := lemma_4_2 hω hQV hosc hφ hφc
  rw [weightedOccupationMeasure.integral_eq hω hQV hφ] at h2
  exact tendsto_nhds_unique h1 h2

/-- **Subgoal** (Remark 4.4, Hölder): for `1 < r`, `g ∈ L^{r'}` and `f ∈ L^r`, `g f` is
integrable. -/
theorem remark_4_4.integrable_mul_conj {r : ℝ≥0∞} (hr : 1 < r) {f g : Rd d → ℝ} (hf : MemLp f r)
    (hg : MemLp g r.conjExponent) : Integrable (fun x => g x * f x) := by
  have := ENNReal.HolderConjugate.conjExponent hr.le
  exact hg.integrable_mul hf

/-- **Subgoal** (Remark 4.4, lower vs. Bochner integral): for nonnegative `f, g` with `g f`
integrable, `∫⁻ g f = ∫ g f`. -/
theorem remark_4_4.lintegral_ofReal_mul_eq {f g : Rd d → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hi : Integrable (fun x => g x * f x)) :
    ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x, g x * f x) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => mul_nonneg (hg x) (hf x))]
  exact lintegral_congr fun x => (ENNReal.ofReal_mul (hg x)).symm

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
