/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- A partition `π = {0 = t_0 < t_1 < ⋯ < t_m = T}` of `[0, T]` (Section 3). -/
structure Partition (T : ℝ) where
  /-- Number `m = m(n)` of subintervals. -/
  m : ℕ
  /-- The partition points `t_0, …, t_m`. -/
  t : Fin (m + 1) → ℝ
  strictMono : StrictMono t
  t_zero : t 0 = 0
  t_last : t (Fin.last m) = T

namespace Partition

variable {T : ℝ} (π : Partition T)

/-- Left endpoint `t_i` of the `i`-th subinterval. -/
def left (i : Fin π.m) : ℝ := π.t i.castSucc

/-- Right endpoint `t_{i+1}` of the `i`-th subinterval. -/
def right (i : Fin π.m) : ℝ := π.t i.succ

/-- **Subgoal** (Section 3 partitions). -/
theorem left_lt_right (i : Fin π.m) : π.left i < π.right i :=
  π.strictMono (by rw [Fin.lt_def]; simp)

/-- **Subgoal** (Section 3 partitions): partition points lie in `[0, T]`. -/
theorem t_mem (j : Fin (π.m + 1)) : π.t j ∈ Icc 0 T := by
  have h1 := π.strictMono.monotone (Fin.zero_le j)
  have h2 := π.strictMono.monotone (Fin.le_last j)
  rw [π.t_zero] at h1
  rw [π.t_last] at h2
  exact ⟨h1, h2⟩

/-- Mesh `|π| := max_i (t_{i+1} - t_i)` (Assumption 1). -/
def mesh : ℝ := ⨆ i : Fin π.m, (π.right i - π.left i)

/-- Smallest gap `|π|_ := min_i (t_{i+1} - t_i)` (Assumption 1). -/
def minGap : ℝ := ⨅ i : Fin π.m, (π.right i - π.left i)

/-- **Subgoal** (Assumption 1 mesh): the mesh is nonnegative. -/
theorem mesh_nonneg : 0 ≤ π.mesh := Real.iSup_nonneg fun i => (sub_pos.2 (π.left_lt_right i)).le

/-- **Subgoal** (Assumption 1 mesh): every gap is at most the mesh. -/
theorem gap_le_mesh (i : Fin π.m) : π.right i - π.left i ≤ π.mesh :=
  le_ciSup (f := fun i => π.right i - π.left i) (Set.finite_range _).bddAbove i

/-- **Subgoal** (Section 3 partitions): the horizon of a partition of `[0, T]` is nonnegative. -/
theorem nonneg (π : Partition T) : 0 ≤ T := by
  have h := π.strictMono.monotone (Fin.zero_le (Fin.last π.m))
  rwa [π.t_zero, π.t_last] at h

/-- The time-reversed partition `←π := {T - t_i : t_i ∈ π}` (Remarks 4.1 and 4.5), indexed
increasingly: `←t_j = T - t_{m-j}`. -/
def reverse : Partition T where
  m := π.m
  t := fun j => T - π.t (Fin.rev j)
  strictMono := fun a b hab => by
    have : π.t (Fin.rev b) < π.t (Fin.rev a) := π.strictMono (Fin.rev_lt_rev.mpr hab)
    linarith
  t_zero := by simp [π.t_last]
  t_last := by simp [π.t_zero]

end Partition

end WeakPathwiseIto
