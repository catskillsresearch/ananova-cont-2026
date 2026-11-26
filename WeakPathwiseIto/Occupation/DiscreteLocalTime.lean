/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The discrete local time of a real path `x` along a partition `π` of `[0, T]`, at level `u`
(Davis–Obłój–Siorpaes [DOS18], as used in Remark 4.5): each increment from `a = x(t_i)` to
`b = x(t_{i+1})` contributes `2 |b - u| 1_{[a ∧ b, a ∨ b)}(u)`. -/
def discreteLocalTime {T : ℝ} (π : Partition T) (x : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ i : Fin π.m,
    (Ico (min (x (π.left i)) (x (π.right i))) (max (x (π.left i)) (x (π.right i)))).indicator
      (fun u => 2 * |x (π.right i) - u|) u

namespace discreteLocalTime

/-- The reversed path `←x(t) := x(T - t)` (Remarks 4.1 and 4.5). -/
def reversePath (T : ℝ) (x : ℝ → ℝ) : ℝ → ℝ := fun t => x (T - t)

/-- `λ^{n,-}_T`: the discrete local time of the reversed path `←x` along the reversed
partition `←π` (Remark 4.5). -/
def reversed {T : ℝ} (π : Partition T) (x : ℝ → ℝ) (u : ℝ) : ℝ :=
  discreteLocalTime π.reverse (reversePath T x) u

end discreteLocalTime

end WeakPathwiseIto
