/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselKernel
public import WeakPathwiseIto.Bessel.Young

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace BesselSpace

/-- The Bessel potential `g_α ⋆ f`, with the convention `g_0 ⋆ f = f`. -/
def potential (d : ℕ) (α : ℝ) (f : Rd d → ℝ) : Rd d → ℝ :=
  if α = 0 then f else fun x => ∫ y, besselKernel d α (x - y) * f y

end BesselSpace

/-- The Bessel space `𝓛^p_α(ℝ^d) := {g_α ⋆ f : f ∈ L^p(ℝ^d)}` (Definition 2.5), with
functions identified up to a.e. equality. -/
def BesselSpace (d : ℕ) (α : ℝ) (p : ℝ≥0∞) : Set (Rd d → ℝ) :=
  {F | ∃ f : Rd d → ℝ, MemLp f p ∧ F =ᵐ[volume] BesselSpace.potential d α f}

namespace BesselSpace

variable {d : ℕ}

/-- The norm `‖F‖_{𝓛^p_α} := ‖f‖_{L^p}` where `F = g_α ⋆ f` (Definition 2.5). -/
def norm (α : ℝ) (p : ℝ≥0∞) (F : Rd d → ℝ) : ℝ≥0∞ :=
  ⨅ (f : Rd d → ℝ) (_ : MemLp f p) (_ : F =ᵐ[volume] potential d α f), eLpNorm f p volume

/-- **Subgoal** (Definition 2.5, Young: pointwise bound
`|g_α ⋆ f(x)| ≤ ∫ |g_α(x - y)| |f(y)| dy`, valid even where the integral diverges). -/
theorem enorm_potential_le {α : ℝ} (hα : α ≠ 0) (f : Rd d → ℝ) (x : Rd d) :
    ‖potential d α f x‖ₑ ≤ ∫⁻ y, ‖besselKernel d α (x - y)‖ₑ * ‖f y‖ₑ := by
  simp only [potential, if_neg hα]
  exact (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun y => enorm_mul _ _)

/-- **Subgoal** (Definition 2.5, Young: `g_α ⋆ f` is a.e. strongly measurable). -/
theorem aestronglyMeasurable_potential {α : ℝ} (hα : 0 < α) {f : Rd d → ℝ}
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (potential d α f) := by
  have h : potential d α f =
      MeasureTheory.convolution f (besselKernel d α) (ContinuousLinearMap.mul ℝ ℝ).flip volume := by
    funext x
    simp only [potential, if_neg hα.ne', convolution_def, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply']
  rw [h]
  exact hf.convolution _ (besselKernel.integrable hα).aestronglyMeasurable

/-- **Subgoal** (Definition 2.5, Young's inequality). Young's inequality: `‖g_α ⋆ f‖_p ≤ ‖g_α‖_1 ‖f‖_p`. -/
theorem eLpNorm_potential_le {α : ℝ} (hα : 0 < α) {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Rd d → ℝ}
    (hf : MemLp f p) :
    eLpNorm (potential d α f) p volume ≤ eLpNorm (besselKernel d α) 1 volume * eLpNorm f p volume := by
  sorry

end BesselSpace

end WeakPathwiseIto
