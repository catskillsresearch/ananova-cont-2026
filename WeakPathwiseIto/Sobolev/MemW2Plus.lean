/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.MemW2PlusS

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- `W^{2+,p}(ℝ^d) := ⋃_{s ∈ (0,1)} W^{2+s,p}(ℝ^d)` (Section 2.1). -/
def MemW2Plus {d : ℕ} (p : ℝ) (f : Rd d → ℝ) : Prop :=
  ∃ s ∈ Ioo (0 : ℝ) 1, MemW2PlusS s p f

end WeakPathwiseIto
