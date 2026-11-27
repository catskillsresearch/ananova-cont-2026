/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open Set

namespace WeakPathwiseIto

namespace Partition

/-- The left grid point of the proof of Proposition 5.3: for a partition
`π = {t_0 < ⋯ < t_m}` of `[0, T]`, `η(s) := t_i` for `s ∈ [t_i, t_{i+1})` (the paper's `η_n` for
`π = π_n`), and `η(s) := 0` off `[0, T)`. -/
def eta {T : ℝ} (π : Partition T) (s : ℝ) : ℝ :=
  ∑ i : Fin π.m, (Ico (π.left i) (π.right i)).indicator (fun _ => π.left i) s

end Partition

end WeakPathwiseIto
