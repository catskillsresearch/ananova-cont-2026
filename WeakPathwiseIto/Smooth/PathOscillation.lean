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

/-- The oscillation of `ω` along `π_n` (eq. (6)):
`osc(ω, π_n) := max_i sup_{t ∈ [t_i, t_{i+1}]} |ω(t) - ω(t_i)|`. -/
def pathOscillation {T : ℝ} {d : ℕ} (ω : ℝ → Rd d) (π : Partition T) : ℝ :=
  ⨆ i : Fin π.m, ⨆ (s : ℝ) (_ : s ∈ Icc (π.left i) (π.right i)), ‖ω s - ω (π.left i)‖

namespace pathOscillation

variable {T : ℝ} {d : ℕ}

/-- Condition (6): `osc(ω, π_n) → 0`. -/
def Vanishes (ω : ℝ → Rd d) (π : ℕ → Partition T) : Prop :=
  Tendsto (fun n => pathOscillation ω (π n)) atTop (𝓝 0)

/-- **Subgoal** (Eq. (6)). Section 3: if `|π_n| → 0` and `ω` is continuous, condition (6) holds. -/
theorem vanishes_of_mesh {ω : ℝ → Rd d} {π : ℕ → Partition T}
    (hω : ContinuousOn ω (Icc 0 T)) (hπ : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    Vanishes ω π := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hω
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Vanishes, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hπ δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hmesh : (π n).mesh < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hle : pathOscillation ω (π n) ≤ ε / 2 := by
    refine Real.iSup_le (fun i => Real.iSup_le (fun s => Real.iSup_le (fun hs => ?_)
      (by positivity)) (by positivity)) (by positivity)
    have hl := (π n).t_mem i.castSucc
    have hr := (π n).t_mem i.succ
    have hs1 : (π n).left i ≤ s := hs.1
    have hs2 : s ≤ (π n).right i := hs.2
    have hl' : (π n).left i ∈ Icc 0 T := hl
    have hr' : (π n).right i ∈ Icc 0 T := hr
    have hsT : s ∈ Icc 0 T := ⟨hl'.1.trans hs1, hs2.trans hr'.2⟩
    have hgap := (π n).gap_le_mesh i
    have := hδε s hsT ((π n).left i) hl' (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [dist_eq_norm] at this
    exact this.le
  have h0 : 0 ≤ pathOscillation ω (π n) :=
    Real.iSup_nonneg fun i => Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end pathOscillation

end WeakPathwiseIto
