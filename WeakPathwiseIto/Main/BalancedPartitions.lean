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

/-- **Assumption 1** (balanced partitions), eq. (26): `M₁ := sup_{n ≥ 1} |π_n| / |π_n|_ < ∞`. -/
def BalancedPartitions {T : ℝ} (π : ℕ → Partition T) : Prop :=
  ∃ M₁ : ℝ, ∀ n, 1 ≤ n → (π n).mesh / (π n).minGap ≤ M₁

end WeakPathwiseIto
