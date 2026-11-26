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

/-- **Subgoal** (Definition 2.4, Fourier transform step 1: Gaussian Fourier transform): for
`δ > 0`, `∫ e^{-2πi x·ξ} e^{-π|x|²/δ} dx = δ^{d/2} e^{-πδ|ξ|²}`. -/
theorem fourier_slice {δ : ℝ} (hδ : 0 < δ) (ξ : Rd d) :
    ∫ x : Rd d, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
        (Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) : ℂ) =
      ((δ ^ ((d : ℝ) / 2) * Real.exp (-Real.pi * δ * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hb : 0 < ((Real.pi / δ : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact div_pos Real.pi_pos hδ
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := Rd d) hb
    (-2 * Real.pi * Complex.I) ξ
  have hint : ∀ x : Rd d, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
      (Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) : ℂ) =
      Complex.exp (-((Real.pi / δ : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 +
        (-2 * Real.pi * Complex.I) * (⟪ξ, x⟫ : ℂ)) := fun x => by
    rw [Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hint]
  rw [h, finrank_euclideanSpace_fin, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_cpow hδ.le]
  congr 1
  · congr 1
    · push_cast; field_simp
    · push_cast; ring
  · congr 1
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring

/-- **Subgoal** (Definition 2.4, Fourier transform step 2: Fubini): the Fourier transform of
`g_α` is the subordination integral of the Fourier transforms of the Gaussian slices. -/
theorem fourier_fubini (hα : 0 < α) (ξ : Rd d) :
    ∫ x, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) * (besselKernel d α x : ℂ) =
      ((((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ : ℝ) : ℂ) *
        ∫ δ in Ioi (0 : ℝ), ((Real.exp (-δ / (4 * Real.pi)) * δ ^ ((α - d) / 2) / δ : ℝ) : ℂ) *
          ∫ x : Rd d, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) *
            (Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) : ℂ) := by
  sorry

/-- **Subgoal** (Definition 2.4, Fourier transform step 3: Gamma integral):
`∫_0^∞ e^{-δ/(4π)} δ^{(α-d)/2} δ^{-1} δ^{d/2} e^{-πδ|ξ|²} dδ = (4π)^{α/2} Γ(α/2) (1 + 4π²|ξ|²)^{-α/2}`. -/
theorem integral_profile_exp (hα : 0 < α) (ξ : Rd d) :
    ∫ δ in Ioi (0 : ℝ), Real.exp (-δ / (4 * Real.pi)) * δ ^ ((α - d) / 2) / δ *
        (δ ^ ((d : ℝ) / 2) * Real.exp (-Real.pi * δ * ‖ξ‖ ^ 2)) =
      (4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2) *
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(α / 2)) := by
  sorry

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

/-- **Subgoal** (Definition 2.4, behaviour at the origin, step 1: substitution `δ = a/u`): for
`a > 0`, `∫_0^∞ g(δ) dδ = ∫_0^∞ g(a/u) a/u² du`. -/
theorem integral_comp_div (g : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), a / u ^ 2 * g (a / u) = ∫ δ in Ioi (0 : ℝ), g δ := by
  have h1 := integral_comp_rpow_Ioi (fun y => a * g (a * y)) (p := -1) (by norm_num)
  have h2 : ∫ y in Ioi (0 : ℝ), a * g (a * y) = ∫ δ in Ioi (0 : ℝ), g δ := by
    rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 ha, mul_zero, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ ha.ne', one_mul]
  rw [← h2, ← h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  simp only [smul_eq_mul]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg_one, Real.rpow_neg hu'.le, abs_neg, abs_one,
    one_mul, Real.rpow_two, div_eq_mul_inv a u]
  ring

/-- **Subgoal** (Definition 2.4, behaviour at the origin, step 2: rescaled kernel): for `x ≠ 0`,
with `δ = π|x|²/u`,
`|x|^{d-α} g_α(x) = ((4π)^{α/2} Γ(α/2))⁻¹ π^{(α-d)/2} ∫_0^∞ e^{-u} e^{-|x|²/(4u)} u^{(d-α)/2-1} du`. -/
theorem mul_eq_integral {x : Rd d} (hx : x ≠ 0) :
    ‖x‖ ^ ((d : ℝ) - α) * besselKernel d α x =
      ((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ * Real.pi ^ ((α - d) / 2) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
          u ^ (((d : ℝ) - α) / 2 - 1) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set a : ℝ := Real.pi * ‖x‖ ^ 2 with ha_def
  have ha : 0 < a := by positivity
  have h := integral_comp_div (fun δ => Real.exp (-Real.pi * ‖x‖ ^ 2 / δ) *
    Real.exp (-δ / (4 * Real.pi)) * δ ^ ((α - d) / 2) / δ) ha
  have key : ∀ u ∈ Ioi (0 : ℝ), a / u ^ 2 * (Real.exp (-Real.pi * ‖x‖ ^ 2 / (a / u)) *
      Real.exp (-(a / u) / (4 * Real.pi)) * (a / u) ^ ((α - d) / 2) / (a / u)) =
      a ^ ((α - d) / 2) * (Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
        u ^ (((d : ℝ) - α) / 2 - 1)) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    have e1 : -Real.pi * ‖x‖ ^ 2 / (a / u) = -u := by
      rw [ha_def]; field_simp
    have e2 : -(a / u) / (4 * Real.pi) = -‖x‖ ^ 2 / (4 * u) := by
      rw [ha_def]; field_simp
    have hus : 0 < u ^ ((α - d) / 2) := Real.rpow_pos_of_pos hu' _
    rw [e1, e2, Real.div_rpow ha.le hu'.le, show ((d : ℝ) - α) / 2 - 1 = -((α - d) / 2) - 1 by ring,
      Real.rpow_sub_one hu'.ne', Real.rpow_neg hu'.le]
    field_simp
  have hscal : ‖x‖ ^ ((d : ℝ) - α) * a ^ ((α - d) / 2) = Real.pi ^ ((α - d) / 2) := by
    rw [ha_def, Real.mul_rpow Real.pi_pos.le (sq_nonneg _), ← Real.rpow_natCast ‖x‖ 2,
      ← Real.rpow_mul hxn.le, mul_left_comm, ← Real.rpow_add hxn,
      show ((d : ℝ) - α) + ((2 : ℕ) : ℝ) * ((α - d) / 2) = 0 by push_cast; ring,
      Real.rpow_zero, mul_one]
  unfold besselKernel
  rw [← h, setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul, ← hscal]
  ring

/-- **Subgoal** (Definition 2.4, behaviour at the origin, step 3: dominated convergence): for
`α < d`, as `x → 0`, `∫_0^∞ e^{-u} e^{-|x|²/(4u)} u^{(d-α)/2-1} du → Γ((d-α)/2)`. -/
theorem tendsto_integral (hαd : α < d) :
    Tendsto (fun x : Rd d => ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
        u ^ (((d : ℝ) - α) / 2 - 1)) (𝓝[≠] 0) (𝓝 (Real.Gamma (((d : ℝ) - α) / 2))) := by
  have hs : 0 < ((d : ℝ) - α) / 2 := by linarith
  rw [Real.Gamma_eq_integral hs]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (-u) * u ^ (((d : ℝ) - α) / 2 - 1)) ?_ ?_ (Real.GammaIntegral_convergent hs) ?_
  · refine Eventually.of_forall fun x => ?_
    have : Measurable fun u : ℝ => Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
        u ^ (((d : ℝ) - α) / 2 - 1) := by fun_prop
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : (0 : ℝ) < u := hu
    have h1 : Real.exp (-‖x‖ ^ 2 / (4 * u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖x‖])
        (by positivity))
    rw [Real.norm_of_nonneg (by positivity)]
    have h2 : 0 ≤ Real.exp (-u) * u ^ (((d : ℝ) - α) / 2 - 1) := by positivity
    calc Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) * u ^ (((d : ℝ) - α) / 2 - 1)
        = Real.exp (-‖x‖ ^ 2 / (4 * u)) * (Real.exp (-u) * u ^ (((d : ℝ) - α) / 2 - 1)) := by ring
      _ ≤ 1 * (Real.exp (-u) * u ^ (((d : ℝ) - α) / 2 - 1)) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hc : Continuous fun x : Rd d => Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
        u ^ (((d : ℝ) - α) / 2 - 1) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Subgoal** (Definition 2.4). Behaviour at the origin for `0 < α < d`: `g_α(x) ~ 1 / (γ(α) |x|^{d-α})`. -/
theorem asymptotic_origin (hα : 0 < α) (hαd : α < d) : ∃ γ : ℝ, 0 < γ ∧
    Tendsto (fun x : Rd d => ‖x‖ ^ ((d : ℝ) - α) * besselKernel d α x) (𝓝[≠] 0)
      (𝓝 γ⁻¹) := by
  have hpos : 0 < ((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ * Real.pi ^ ((α - d) / 2) *
      Real.Gamma (((d : ℝ) - α) / 2) :=
    mul_pos (mul_pos (inv_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith)))) (Real.rpow_pos_of_pos Real.pi_pos _))
      (Real.Gamma_pos_of_pos (by linarith))
  refine ⟨(((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ * Real.pi ^ ((α - d) / 2) *
    Real.Gamma (((d : ℝ) - α) / 2))⁻¹, inv_pos.2 hpos, ?_⟩
  rw [inv_inv, mul_assoc]
  have hev : (fun x : Rd d => ((4 * Real.pi) ^ (α / 2) * Real.Gamma (α / 2))⁻¹ *
      Real.pi ^ ((α - d) / 2) * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.exp (-‖x‖ ^ 2 / (4 * u)) *
        u ^ (((d : ℝ) - α) / 2 - 1)) =ᶠ[𝓝[≠] 0]
      fun x => ‖x‖ ^ ((d : ℝ) - α) * besselKernel d α x :=
    eventually_mem_nhdsWithin.mono fun x hx => (mul_eq_integral hx).symm
  rw [← mul_assoc]
  exact ((tendsto_integral hαd).const_mul _).congr' hev

end besselKernel

end WeakPathwiseIto
