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

/-- `x` is a Lebesgue point of `f`: `⨍_{B(x,r)} |f(y) - c| dy → 0` as `r → 0` for some `c`. -/
def IsLebesguePoint {d : ℕ} (f : Rd d → ℝ) (x : Rd d) : Prop :=
  ∃ c : ℝ, Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0)

end WeakPathwiseIto
