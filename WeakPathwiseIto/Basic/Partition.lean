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

theorem left_lt_right (i : Fin π.m) : π.left i < π.right i :=
  π.strictMono (by rw [Fin.lt_def]; simp)

/-- Mesh `|π| := max_i (t_{i+1} - t_i)` (Assumption 1). -/
def mesh : ℝ := ⨆ i : Fin π.m, (π.right i - π.left i)

/-- Smallest gap `|π|_ := min_i (t_{i+1} - t_i)` (Assumption 1). -/
def minGap : ℝ := ⨅ i : Fin π.m, (π.right i - π.left i)

end Partition

end WeakPathwiseIto
