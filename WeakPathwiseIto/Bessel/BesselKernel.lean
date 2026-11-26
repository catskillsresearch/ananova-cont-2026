/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Bessel kernel `g_α` on `ℝ^d` (Definition 2.4), given by the subordination formula
`g_α(x) = ((4π)^{α/2} Γ(α/2))⁻¹ ∫_0^∞ e^{-π|x|²/δ} e^{-δ/(4π)} δ^{(α-d)/2} dδ/δ`
[Ste70, Ch. V §3]; its defining property `ĝ_α(ξ) = (1 + 4π²|ξ|²)^{-α/2}` is
`besselKernel.fourier_eq`. -/
def besselKernel (d : ℕ) (α : ℝ) (x : Rd d) : ℝ :=
  ((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ *
    ∫ δ in Ioi (0 : ℝ), Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) * Real.exp (-δ / (4 * Real.pi)) *
      δ ^ ((α - d) / 2) / δ

namespace besselKernel

variable {d : ℕ} {α : ℝ}

/-- **Subgoal** (Definition 2.4). Definition 2.4: the Fourier transform `ĝ_α(ξ) = ∫ g_α(x) e^{-2πi x·ξ} dx` equals
`(1 + 4π²|ξ|²)^{-α/2}`. -/
theorem fourier_eq (hα : 0 < α) (ξ : Rd d) :
    ∫ x, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) * (besselKernel d α x : ℂ) =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(α / 2)) : ℝ) : ℂ) := by
  sorry

/-- **Subgoal** (Definition 2.4). -/
theorem nonneg (hα : 0 < α) (x : Rd d) : 0 ≤ besselKernel d α x := by
  unfold besselKernel
  refine mul_nonneg (inv_nonneg.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.Gamma_pos_of_pos (by linarith))).le) ?_
  refine setIntegral_nonneg measurableSet_Ioi fun δ hδ => ?_
  have hδ' : 0 < δ := hδ
  exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (Real.rpow_nonneg hδ'.le _)) hδ'.le

/-- **Subgoal** (Definition 2.4, integrability step 1: Gaussian slice): for `δ > 0`,
`∫_{ℝ^d} e^{-π|x|²/δ} dx = δ^{d/2}`. -/
theorem integral_exp_slice {δ : ℝ} (hδ : 0 < δ) :
    ∫ x : Rd d, Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) = δ ^ ((d : ℝ) / 2) := by
  have h : (fun x : Rd d => Real.exp (-Real.pi * ‖x‖ ^ 2 / δ)) =
      fun x => Real.exp (-(Real.pi / δ) * ‖x‖ ^ 2) := by
    funext x; congr 1; ring
  rw [h, GaussianFourier.integral_rexp_neg_mul_sq_norm (div_pos Real.pi_pos hδ),
    finrank_euclideanSpace_fin, div_div_cancel₀ Real.pi_ne_zero]

/-- **Subgoal** (Definition 2.4, integrability step 2: Gamma-type profile): for `α > 0`,
`δ ↦ δ^{α/2 - 1} e^{-δ/(4π)}` is integrable on `(0, ∞)`. -/
theorem integrableOn_profile (hα : 0 < α) :
    IntegrableOn (fun δ : ℝ => δ ^ (α / 2 - 1) * Real.exp (-(1 / (4 * Real.pi)) * δ ^ (1 : ℝ)))
      (Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (by positivity)

/-- **Subgoal** (Definition 2.4, integrability step 3: Tonelli): the subordination integrand
`(x, δ) ↦ e^{-π|x|²/δ} e^{-δ/(4π)} δ^{(α-d)/2} / δ` is integrable on `ℝ^d × (0, ∞)`. -/
theorem integrable_uncurry (hα : 0 < α) :
    Integrable (fun p : Rd d × ℝ => Real.exp (-Real.pi * ‖p.1‖ ^ 2 / p.2) *
        Real.exp (-p.2 / (4 * Real.pi)) * p.2 ^ ((α - d) / 2) / p.2)
      ((volume : Measure (Rd d)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : Measurable fun p : Rd d × ℝ => Real.exp (-Real.pi * ‖p.1‖ ^ 2 / p.2) *
      Real.exp (-p.2 / (4 * Real.pi)) * p.2 ^ ((α - d) / 2) / p.2 := by
    fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have hg : Integrable (fun x : Rd d => Real.exp (-Real.pi * ‖x‖ ^ 2 / δ)) := by
      refine Integrable.of_integral_ne_zero ?_
      rw [integral_exp_slice hδ']
      exact (Real.rpow_pos_of_pos hδ' _).ne'
    exact ((hg.mul_const _).mul_const _).div_const _
  · refine IntegrableOn.congr_fun (integrableOn_profile hα) (fun δ hδ => ?_) measurableSet_Ioi
    have hδ' : (0 : ℝ) < δ := hδ
    have h1 : ∀ x : Rd d, ‖Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) * Real.exp (-δ / (4 * Real.pi)) *
        δ ^ ((α - d) / 2) / δ‖ = Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) *
          (Real.exp (-δ / (4 * Real.pi)) * δ ^ ((α - d) / 2) / δ) := fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (Real.exp_pos _).le) (Real.rpow_nonneg hδ'.le _)) hδ'.le)]
      ring
    simp only [h1]
    rw [integral_mul_const, integral_exp_slice hδ', Real.rpow_one,
      show -(1 / (4 * Real.pi)) * δ = -δ / (4 * Real.pi) by ring,
      show α / 2 - 1 = ((d : ℝ) / 2 + (α - d) / 2) - 1 by ring, Real.rpow_sub_one hδ'.ne',
      Real.rpow_add hδ']
    ring

/-- **Subgoal** (Definition 2.4). -/
theorem integrable (hα : 0 < α) : Integrable (besselKernel d α) := by
  unfold besselKernel
  exact ((integrable_uncurry hα).integral_prod_left).const_mul _

/-- **Subgoal** (Definition 2.4). Behaviour at the origin for `0 < α < d`: `g_α(x) ~ 1 / (γ(α) |x|^{d-α})`. -/
theorem asymptotic_origin (hα : 0 < α) (hαd : α < d) : ∃ γ : ℝ, 0 < γ ∧
    Tendsto (fun x : Rd d => ‖x‖ ^ ((d : ℝ) - α) * besselKernel d α x) (𝓝[≠] 0)
      (𝓝 γ⁻¹) := by
  sorry

end besselKernel

end WeakPathwiseIto
