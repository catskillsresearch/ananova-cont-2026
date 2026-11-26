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

/-- **Assumption 2**, eq. (27): there is `M₂ > 1` with `M₂ ≤ |π_n| / |π_{n+1}|` for all `n`. -/
def GeometricMeshDecay {T : ℝ} (π : ℕ → Partition T) : Prop :=
  ∃ M₂ : ℝ, 1 < M₂ ∧ ∀ n, M₂ ≤ (π n).mesh / (π (n + 1)).mesh

namespace GeometricMeshDecay

variable {T : ℝ} {π : ℕ → Partition T}

/-- Eq. (30): `∑_n |π_n| < ∞`. -/
theorem summable_mesh (hT : 0 < T) (h : GeometricMeshDecay π) : Summable fun n => (π n).mesh := by
  sorry

/-- Eq. (31): `1/|π_1| + ⋯ + 1/|π_n| ≤ M₃ / |π_n|`. -/
theorem sum_inv_mesh_le (hT : 0 < T) (h : GeometricMeshDecay π) : ∃ M₃ : ℝ, ∀ n,
    ∑ k ∈ Finset.range (n + 1), 1 / (π k).mesh ≤ M₃ / (π n).mesh := by
  sorry

end GeometricMeshDecay

end WeakPathwiseIto
