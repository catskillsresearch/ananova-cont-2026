/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselKernel

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

/-- **Subgoal** (Definition 2.5, Young's inequality). Young's inequality: `‖g_α ⋆ f‖_p ≤ ‖g_α‖_1 ‖f‖_p`. -/
theorem eLpNorm_potential_le {α : ℝ} (hα : 0 < α) {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Rd d → ℝ}
    (hf : MemLp f p) :
    eLpNorm (potential d α f) p volume ≤ eLpNorm (besselKernel d α) 1 volume * eLpNorm f p volume := by
  sorry

end BesselSpace

end WeakPathwiseIto
