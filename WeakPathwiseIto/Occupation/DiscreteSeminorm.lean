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

/-- The discrete seminorm of Section 4.2 (and `‖h‖_{n,1,B}` of Lemma B.2 for `p = 1`):
`‖h‖_{n,p,ω} := (∑_i (|h(ω(t_i))|^p + |h(ω(t_{i+1}))|^p) |t_{i+1} - t_i|)^{1/p}`, for a
nonnegative extended-real `h` (apply to `‖h‖ₑ` for real `h`). -/
def discreteSeminorm {T : ℝ} {d : ℕ} (π : Partition T) (p : ℝ) (h : Rd d → ℝ≥0∞)
    (ω : ℝ → Rd d) : ℝ≥0∞ :=
  (∑ i : Fin π.m, (h (ω (π.left i)) ^ p + h (ω (π.right i)) ^ p) *
    ENNReal.ofReal (π.right i - π.left i)) ^ (1 / p)

end WeakPathwiseIto
