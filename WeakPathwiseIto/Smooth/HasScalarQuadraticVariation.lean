/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.DiscreteQuadraticVariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- A real path `x` has finite quadratic variation along `π = (π_n)` (eq. (5), [Föl81]):
for every `t ∈ [0, T]` the discrete quadratic variations converge to `[x]_π(t)`, and
`t ↦ [x]_π(t)` is continuous and increasing on `[0, T]`. -/
structure HasScalarQuadraticVariation {T : ℝ} (π : ℕ → Partition T) (x : ℝ → ℝ) where
  /-- The quadratic variation `[x]_π` (only its values on `[0, T]` matter). -/
  qv : ℝ → ℝ
  tendsto : ∀ t ∈ Icc 0 T,
    Tendsto (fun n => discreteQuadraticVariation (π n) x t) atTop (𝓝 (qv t))
  continuousOn : ContinuousOn qv (Icc 0 T)
  monotoneOn : MonotoneOn qv (Icc 0 T)

namespace HasScalarQuadraticVariation

variable {T : ℝ} {π : ℕ → Partition T} {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x)

/-- **Subgoal** (Eq. (5) Stieltjes measure): `[x]_π` extended constantly outside `[0, T]`,
`t ↦ [x]_π(max 0 (min t T))`, a monotone function on `ℝ` carrying the measure `d[x]_π`. -/
def qvExt (t : ℝ) : ℝ := h.qv (max 0 (min t T))

/-- **Subgoal** (Eq. (5) Stieltjes measure): the extension `qvExt` is monotone. -/
theorem qvExt_monotone : Monotone h.qvExt := by
  have hT : 0 ≤ T := (π 0).nonneg
  intro a b hab
  exact h.monotoneOn ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩ (max_le_max le_rfl (min_le_min hab le_rfl))

/-- The Stieltjes measure `d[x]_π`. -/
def stieltjesMeasure : Measure ℝ := h.qvExt_monotone.stieltjesFunction.measure

/-- The Riemann–Stieltjes integral `∫_0^t g(u) d[x]_π(u)`. -/
def integral (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in Ioc 0 t, g u ∂h.stieltjesMeasure

end HasScalarQuadraticVariation

end WeakPathwiseIto
