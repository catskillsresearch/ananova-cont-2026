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

/-- The truncated Hardy–Littlewood maximal function
`M_R f(x) := sup_{r < R} ⨍_{B(x,r)} |f(y)| dy` (Section 2.1). -/
def localMaximalFunction {d : ℕ} {F : Type*} [NormedAddCommGroup F] (R : ℝ≥0∞)
    (f : Rd d → F) (x : Rd d) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r) (_ : ENNReal.ofReal r < R), laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ)

namespace localMaximalFunction

/-- The full maximal function `M f := M_∞ f`. -/
def full {d : ℕ} {F : Type*} [NormedAddCommGroup F] (f : Rd d → F) (x : Rd d) : ℝ≥0∞ :=
  localMaximalFunction ⊤ f x

end localMaximalFunction

end WeakPathwiseIto
