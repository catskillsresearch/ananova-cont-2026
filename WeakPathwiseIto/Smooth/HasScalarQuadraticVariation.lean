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
the discrete quadratic variations converge for every `t ∈ [0, T]` to `[x]_π(t)`, and
`t ↦ [x]_π(t)` is continuous and increasing. (The witness `qv` is taken globally continuous
and monotone; this is equivalent, extending constantly outside `[0, T]`.) -/
structure HasScalarQuadraticVariation {T : ℝ} (π : ℕ → Partition T) (x : ℝ → ℝ) where
  /-- The quadratic variation `[x]_π`. -/
  qv : ℝ → ℝ
  tendsto : ∀ t ∈ Icc 0 T,
    Tendsto (fun n => discreteQuadraticVariation (π n) x t) atTop (𝓝 (qv t))
  continuous : Continuous qv
  monotone : Monotone qv

namespace HasScalarQuadraticVariation

variable {T : ℝ} {π : ℕ → Partition T} {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x)

/-- The Stieltjes measure `d[x]_π`. -/
def stieltjesMeasure : Measure ℝ := h.monotone.stieltjesFunction.measure

/-- The Riemann–Stieltjes integral `∫_0^t g(u) d[x]_π(u)`. -/
def integral (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in Ioc 0 t, g u ∂h.stieltjesMeasure

end HasScalarQuadraticVariation

end WeakPathwiseIto
