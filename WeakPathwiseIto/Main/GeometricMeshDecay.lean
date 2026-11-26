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

/-- **Assumption 2**, eq. (27): there is `M₂ > 1` with `M₂ ≤ |π_n| / |π_{n+1}|` for all `n ≥ 1`. -/
def GeometricMeshDecay {T : ℝ} (π : ℕ → Partition T) : Prop :=
  ∃ M₂ : ℝ, 1 < M₂ ∧ ∀ n, 1 ≤ n → M₂ ≤ (π n).mesh / (π (n + 1)).mesh

namespace GeometricMeshDecay

variable {T : ℝ} {π : ℕ → Partition T}

/-- **Subgoal** (Assumption 2, eqs. (30)–(31)): for `n ≥ 1`, `0 < |π_{n+1}|` and
`M₂ |π_{n+1}| ≤ |π_n|`. -/
theorem mesh_succ {M₂ : ℝ} (hM : 1 < M₂) (h : ∀ n, 1 ≤ n → M₂ ≤ (π n).mesh / (π (n + 1)).mesh)
    {n : ℕ} (hn : 1 ≤ n) : 0 < (π (n + 1)).mesh ∧ M₂ * (π (n + 1)).mesh ≤ (π n).mesh := by
  have h0 := (π (n + 1)).mesh_nonneg
  have hpos : 0 < (π (n + 1)).mesh := by
    rcases h0.lt_or_eq with h0 | h0
    · exact h0
    · have := h n hn
      rw [← h0, div_zero] at this
      linarith
  exact ⟨hpos, (le_div_iff₀ hpos).1 (h n hn)⟩

/-- **Subgoal** (Assumption 2, eq. (30)). Eq. (30): `∑_{n ≥ 1} |π_n| < ∞`. -/
theorem summable_mesh (hT : 0 < T) (h : GeometricMeshDecay π) : Summable fun n => (π (n + 1)).mesh := by
  sorry

/-- **Subgoal** (Assumption 2, eq. (31)). Eq. (31): `1/|π_1| + ⋯ + 1/|π_n| ≤ M₃ / |π_n|`. -/
theorem sum_inv_mesh_le (hT : 0 < T) (h : GeometricMeshDecay π) : ∃ M₃ : ℝ, ∀ n, 1 ≤ n →
    ∑ k ∈ Finset.Icc 1 n, 1 / (π k).mesh ≤ M₃ / (π n).mesh := by
  sorry

end GeometricMeshDecay

end WeakPathwiseIto
