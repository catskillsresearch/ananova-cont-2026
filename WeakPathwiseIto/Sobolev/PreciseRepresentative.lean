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

/-- The natural (precise) representative of eq. (3):
`g̃(x) := limsup_{r → 0} ⨍_{B(x,r)} g(y) dy`. -/
def preciseRepresentative {d : ℕ} (g : Rd d → ℝ) (x : Rd d) : ℝ :=
  limsup (fun r : ℝ => ⨍ y in Metric.ball x r, g y) (𝓝[>] 0)

namespace preciseRepresentative

variable {d : ℕ}

/-- The limsup defining `g̃(x)` is finite (`|g̃(x)| < +∞` in the paper). -/
def IsFinite (g : Rd d → ℝ) (x : Rd d) : Prop :=
  IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (fun r : ℝ => ⨍ y in Metric.ball x r, g y) ∧
    IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (fun r : ℝ => ⨍ y in Metric.ball x r, g y)

/-- Coordinatewise precise representative of a vector field `G : ℝ^d → ℝ^d`. -/
def vec (G : Rd d → Rd d) (x : Rd d) : Rd d :=
  ∑ i, preciseRepresentative (fun y => Rd.coord i (G y)) x • Rd.basisVec i

/-- Every coordinate of `G̃(x)` is finite. -/
def VecIsFinite (G : Rd d → Rd d) (x : Rd d) : Prop :=
  ∀ i, IsFinite (fun y => Rd.coord i (G y)) x

end preciseRepresentative

end WeakPathwiseIto
