/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The normalised discrete quadratic-variation density of eq. (28) (also used for (11)):
`ρ_{n,ω}(t) := ∑_i |ω(t_{i+1}) - ω(t_i)|² / (t_{i+1} - t_i) · 1_{[t_i, t_{i+1})}(t)`. -/
def normalizedQuadraticDensity {T : ℝ} {d : ℕ} (π : Partition T) (ω : ℝ → Rd d) (t : ℝ) : ℝ :=
  ∑ i : Fin π.m, (Ico (π.left i) (π.right i)).indicator
    (fun _ => ‖ω (π.right i) - ω (π.left i)‖ ^ 2 / (π.right i - π.left i)) t

end WeakPathwiseIto
