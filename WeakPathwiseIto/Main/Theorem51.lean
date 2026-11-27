/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Main.WeakPathwiseIntegral
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Main.Theorem51Steps

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

/-- **Theorem 5.1** (existence of the limits (14) and (15)). -/
theorem theorem_5_1_tendsto (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) :
    ∀ t ∈ Icc 0 T,
      Tendsto (fun m => follmerIntegral π (gradient (A.seq m)) ω t) atTop
          (𝓝 (weakPathwiseIntegral A t)) ∧
        Tendsto (fun m => pathwiseCovariation π (gradient (A.seq m)) ω t) atTop
          (𝓝 (weakCovariation A t)) := by
  intro t ht
  have hI := theorem_5_1.tendsto_integral hω hQV hosc hH A ht
  refine ⟨?_, theorem_5_1.tendsto_covariation hω hQV hosc hH A ht⟩
  rw [weakPathwiseIntegral, hI.limUnder_eq]
  exact hI

/-- **Theorem 5.1** (independence of the approximating sequence). -/
theorem theorem_5_1_unique (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H H' : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H')
    (A : ApproximatingSequence π ω F H) (A' : ApproximatingSequence π ω F H') :
    ∀ t ∈ Icc 0 T, weakPathwiseIntegral A' t = weakPathwiseIntegral A t ∧
      weakCovariation A' t = weakCovariation A t := by
  intro t ht
  obtain ⟨hH'm, hH'H⟩ := theorem_5_1.isWeakHessian_ae hH' hH
  obtain ⟨C, hC⟩ := theorem_5_1.abs_covariation_sub_le hω hQV hosc
  have hu := theorem_5_1.tendsto_covariation hω hQV hosc hH A ht
  have hv := theorem_5_1.tendsto_covariation hω hQV hosc hH' A' ht
  set s : ℕ → ℝ≥0∞ := fun m =>
    occupationSeminorm π ω (fun x => smoothHessian (A.seq m) x - H x) with hs
  set s' : ℕ → ℝ≥0∞ := fun m =>
    occupationSeminorm π ω (fun x => smoothHessian (A'.seq m) x - H' x) with hs'
  have hr : Tendsto (fun m => (s m).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp A.tendsto_hessian
    rw [ENNReal.toReal_zero] at this
    exact this
  have hr' : Tendsto (fun m => (s' m).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp A'.tendsto_hessian
    rw [ENNReal.toReal_zero] at this
    exact this
  have hfin : ∀ᶠ m in atTop, s m ≠ ⊤ :=
    (A.tendsto_hessian.eventually (gt_mem_nhds zero_lt_one)).mono fun m h => ne_top_of_lt h
  have hfin' : ∀ᶠ m in atTop, s' m ≠ ⊤ :=
    (A'.tendsto_hessian.eventually (gt_mem_nhds zero_lt_one)).mono fun m h => ne_top_of_lt h
  have hdiff : Tendsto (fun m => pathwiseCovariation π (gradient (A'.seq m)) ω t -
      pathwiseCovariation π (gradient (A.seq m)) ω t) atTop (𝓝 0) := by
    have hbd : Tendsto (fun m => (C : ℝ) * ((s' m).toReal + (s m).toReal)) atTop (𝓝 0) := by
      simpa using (hr'.add hr).const_mul (C : ℝ)
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [hfin, hfin', eventually_ge_atTop 1] with m hsm hsm' hm
    have h := hC (A'.seq m) (A.seq m) H' H (A'.smooth m hm) (A.smooth m hm) hH'm hH'H t ht
    have hne : (C : ℝ≥0∞) * (s' m + s m) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hsm', hsm⟩)
    have := (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hsm' hsm, ENNReal.coe_toReal] at this
    rw [Real.norm_eq_abs]
    exact this
  have hcov : weakCovariation A' t = weakCovariation A t := by
    have h2 := hv.sub hu
    have := tendsto_nhds_unique h2 hdiff
    linarith
  refine ⟨?_, hcov⟩
  have hI := theorem_5_1.tendsto_integral hω hQV hosc hH A ht
  have hI' := theorem_5_1.tendsto_integral hω hQV hosc hH' A' ht
  rw [weakPathwiseIntegral, weakPathwiseIntegral, hI.limUnder_eq, hI'.limUnder_eq, hcov]

/-- **Theorem 5.1** (pathwise integration and weak change-of-variable formula). Let
`ω ∈ C([0,T]; ℝ^d) ∩ Q_π([0,T]; ℝ^d)` satisfy (6), `F ∈ 𝓦^2_{ω,π}` and `(F_m)` satisfy (12),
(13). Then for all `t ∈ [0, T]`, eq. (17):
`F(ω(t)) - F(ω(0)) = ∫_0^t ∇F(ω(s)) d^π ω(s) + ½ [∇F(ω), ω]_π(t)`. -/
theorem theorem_5_1 (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) :
    ∀ t ∈ Icc 0 T, F (ω t) - F (ω 0) = weakPathwiseIntegral A t + 1 / 2 * weakCovariation A t := by
  sorry

end WeakPathwiseIto
