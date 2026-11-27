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

/-- **Subgoal** (Lemma B.2 proof, eq. (35), ratio step): for `t_i > 0`,
`t_{i+1} ≤ (1 + |π| / |π|_) t_i`, since `t_{i+1} - t_i ≤ |π|` and `t_i ≥ t_i - t_{i-1} ≥ |π|_`. -/
theorem right_le_mul_left (i : Fin π.m) (hi : 0 < π.left i) :
    π.right i ≤ (1 + π.mesh / π.minGap) * π.left i := by
  have : Nonempty (Fin π.m) := ⟨i⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, i.val = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    have h : i.castSucc = 0 := Fin.ext (by simp [h0])
    simp [left, h, π.t_zero] at hi
  let j : Fin π.m := ⟨k, by omega⟩
  have hj : π.right j = π.left i := by
    simp only [right, left]
    congr 1
    ext
    simp [j, hk]
  have hmin_le : π.minGap ≤ π.right j - π.left j :=
    ciInf_le (f := fun i => π.right i - π.left i) (Set.finite_range _).bddBelow j
  have hminpos : 0 < π.minGap := by
    obtain ⟨l, hl⟩ := exists_eq_ciInf_of_finite (f := fun i => π.right i - π.left i)
    rw [minGap, ← hl]
    exact sub_pos.2 (π.left_lt_right l)
  have hleft : π.minGap ≤ π.left i := by
    have : 0 ≤ π.left j := (π.t_mem j.castSucc).1
    linarith
  have hgap := π.gap_le_mesh i
  have h1 : π.mesh = π.mesh / π.minGap * π.minGap := by field_simp
  have h2 := mul_le_mul_of_nonneg_left hleft (div_nonneg π.mesh_nonneg hminpos.le)
  linarith

/-- **Subgoal** (Lemma A.1 proof, step 3: `∑_i Δ_i^n = T`): the gaps of a partition of `[0, T]`
sum to `T`. -/
theorem sum_gap : ∑ i : Fin π.m, (π.right i - π.left i) = T := by
  set g : ℕ → ℝ := fun k => if h : k ≤ π.m then π.t ⟨k, by omega⟩ else T with hg
  have h1 : ∑ i : Fin π.m, (π.right i - π.left i) = ∑ i : Fin π.m, (g (i + 1) - g i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (i : ℕ) + 1 ≤ π.m := i.isLt
    have h2 : (i : ℕ) ≤ π.m := i.isLt.le
    simp only [hg, dite_eq_left h1, dite_eq_left h2, right, left]
    rfl
  rw [h1, Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k), Finset.sum_range_sub]
  simp only [hg, dite_eq_left le_rfl, dite_eq_left (Nat.zero_le _)]
  rw [show (⟨π.m, by omega⟩ : Fin (π.m + 1)) = Fin.last π.m from rfl, π.t_last,
    show (⟨0, by omega⟩ : Fin (π.m + 1)) = 0 from rfl, π.t_zero, sub_zero]

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
