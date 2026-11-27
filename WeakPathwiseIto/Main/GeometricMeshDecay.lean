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
theorem summable_mesh (_hT : 0 < T) (h : GeometricMeshDecay π) : Summable fun n => (π (n + 1)).mesh := by
  obtain ⟨M₂, hM, hM'⟩ := h
  have hM0 : 0 < M₂ := by linarith
  have key : ∀ n, (π (n + 1)).mesh ≤ (π 1).mesh * M₂⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      obtain ⟨_, hle⟩ := mesh_succ hM hM' (n := k + 1) (by omega)
      calc (π (k + 1 + 1)).mesh ≤ (π (k + 1)).mesh * M₂⁻¹ := by
            rw [le_mul_inv_iff₀ hM0]; linarith [mul_comm M₂ (π (k + 1 + 1)).mesh]
        _ ≤ (π 1).mesh * M₂⁻¹ ^ k * M₂⁻¹ := by gcongr
        _ = (π 1).mesh * M₂⁻¹ ^ (k + 1) := by ring
  refine Summable.of_nonneg_of_le (fun n => (π (n + 1)).mesh_nonneg) key ?_
  exact (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hM)).mul_left _

/-- **Subgoal** (Assumption 2, eq. (31)). Eq. (31): `1/|π_1| + ⋯ + 1/|π_n| ≤ M₃ / |π_n|`. -/
theorem sum_inv_mesh_le (_hT : 0 < T) (h : GeometricMeshDecay π) : ∃ M₃ : ℝ, ∀ n, 1 ≤ n →
    ∑ k ∈ Finset.Icc 1 n, 1 / (π k).mesh ≤ M₃ / (π n).mesh := by
  obtain ⟨M₂, hM, hM'⟩ := h
  have hM1 : 0 < M₂ - 1 := by linarith
  have hM0 : 0 < M₂ := by linarith
  refine ⟨M₂ / (M₂ - 1), fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have : (1 : ℝ) ≤ M₂ / (M₂ - 1) := by rw [le_div_iff₀ hM1]; linarith
    exact div_le_div_of_nonneg_right this (π 1).mesh_nonneg
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    obtain ⟨hp, hle⟩ := mesh_succ hM hM' hk
    have hne : (π (k + 1)).mesh ≠ 0 := hp.ne'
    calc _ ≤ M₂ / (M₂ - 1) / (π k).mesh + 1 / (π (k + 1)).mesh := by linarith
      _ ≤ M₂ / (M₂ - 1) / (M₂ * (π (k + 1)).mesh) + 1 / (π (k + 1)).mesh :=
          by
          have := div_le_div_of_nonneg_left (div_nonneg hM0.le hM1.le) (mul_pos hM0 hp) hle
          linarith
      _ = M₂ / (M₂ - 1) / (π (k + 1)).mesh := by
          field_simp
          ring

end GeometricMeshDecay

end WeakPathwiseIto
