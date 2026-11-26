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

/-- Definition 2.4: the Fourier transform `ĝ_α(ξ) = ∫ g_α(x) e^{-2πi x·ξ} dx` equals
`(1 + 4π²|ξ|²)^{-α/2}`. -/
theorem fourier_eq (hα : 0 < α) (ξ : Rd d) :
    ∫ x, Complex.exp (-(2 * Real.pi * ⟪x, ξ⟫ : ℝ) * Complex.I) * (besselKernel d α x : ℂ) =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(α / 2)) : ℝ) : ℂ) := by
  sorry

theorem nonneg (hα : 0 < α) (x : Rd d) : 0 ≤ besselKernel d α x := by
  sorry

theorem integrable (hα : 0 < α) : Integrable (besselKernel d α) := by
  sorry

/-- Behaviour at the origin for `0 < α < d`: `g_α(x) ~ 1 / (γ(α) |x|^{d-α})`. -/
theorem asymptotic_origin (hα : 0 < α) (hαd : α < d) : ∃ γ : ℝ, 0 < γ ∧
    Tendsto (fun x : Rd d => ‖x‖ ^ ((d : ℝ) - α) * besselKernel d α x) (𝓝[≠] 0)
      (𝓝 γ⁻¹) := by
  sorry

end besselKernel

end WeakPathwiseIto
