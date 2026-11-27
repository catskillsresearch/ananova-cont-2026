/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The truncated Hardy–Littlewood maximal function
`M_R f(x) := sup_{r < R} ⨍_{B(x,r)} |f(y)| dy` (Section 2.1). -/
def localMaximalFunction {d : ℕ} {F : Type*} [NormedAddCommGroup F] (R : ℝ≥0∞)
    (f : Rd d → F) (x : Rd d) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r) (_ : ENNReal.ofReal r < R), laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ)

namespace localMaximalFunction

/-- The full maximal function `M f := M_∞ f`. -/
def full {d : ℕ} {F : Type*} [NormedAddCommGroup F] (f : Rd d → F) (x : Rd d) : ℝ≥0∞ :=
  localMaximalFunction ⊤ f x

variable {d : ℕ}

/-- **Subgoal** (`M_1`, `M_1 f` is Borel: `x ↦ c ν(B(x, r))` is lower semicontinuous for a
measure `ν`, since `B(x, r - δ) ⊆ B(x', r)` for `x'` near `x` and `ν(B(x, r - δ)) → ν(B(x, r))`). -/
theorem lowerSemicontinuous_mul_measure_ball (ν : Measure (Rd d)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    LowerSemicontinuous fun x => c * ν (Metric.ball x r) := by
  intro x y hy
  set s : ℕ → Set (Rd d) := fun n => Metric.ball x (r - r / ((n : ℝ) + 2)) with hs
  have hmono : Monotone s := by
    intro m n hmn
    refine Metric.ball_subset_ball ?_
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have : r / ((n : ℝ) + 2) ≤ r / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le hm (by linarith [show (m : ℝ) ≤ n from by exact_mod_cast hmn])
    linarith
  have hU : (⋃ n, s n) = Metric.ball x r := by
    ext z
    simp only [mem_iUnion, hs, Metric.mem_ball]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < r / ((n : ℝ) + 2) := by positivity
      linarith
    · intro hz
      have hpos : 0 < r - dist z x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist z x))
      refine ⟨n, ?_⟩
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have : r / ((n : ℝ) + 2) < r - dist z x := by
        rw [div_lt_iff₀ h2]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
  have ht : Tendsto (fun n => c * ν (s n)) atTop (𝓝 (c * ν (Metric.ball x r))) := by
    rw [← hU]
    exact ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop hmono) (Or.inr hc)
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hy)).exists
  have hδ : 0 < r / ((n : ℝ) + 2) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with x' hx'
  refine lt_of_lt_of_le hn (mul_le_mul_right (measure_mono fun z hz => ?_) c)
  simp only [hs, Metric.mem_ball] at hz hx' ⊢
  linarith [dist_triangle z x x', dist_comm x x']

/-- **Subgoal** (`M_1`, `M_1 f` is Borel: a supremum of lower semicontinuous ball averages). -/
theorem measurable (f : Rd d → ℝ) :
    Measurable (localMaximalFunction 1 f) := by
  unfold localMaximalFunction
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_iSup fun r =>
    lowerSemicontinuous_iSup fun hr => lowerSemicontinuous_iSup fun _ => ?_)
  have h : ∀ x, laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ) =
      (volume (Metric.ball (0 : Rd d) r))⁻¹ *
        (volume.withDensity fun y => ‖f y‖ₑ) (Metric.ball x r) := by
    intro x
    rw [laverage_eq, withDensity_apply _ Metric.isOpen_ball.measurableSet,
      Measure.restrict_apply_univ, Measure.addHaar_ball_center, ENNReal.div_eq_inv_mul]
  simp_rw [h]
  exact lowerSemicontinuous_mul_measure_ball _ hr _ (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume _ hr).ne')

/-- **Subgoal** (`M_1`, sublinearity: `|f| ≤ |g| + |h|` gives
`M_1 f ≤ M_1 g + M_1 h`). -/
theorem le_add {f g h : Rd d → ℝ} (hg : Measurable g)
    (hfgh : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ + ‖h y‖ₑ) (x : Rd d) :
    localMaximalFunction 1 f x ≤ localMaximalFunction 1 g x + localMaximalFunction 1 h x := by
  have hmem : ∀ (φ : Rd d → ℝ) (r : ℝ), 0 < r → ENNReal.ofReal r < 1 →
      laverage (volume.restrict (Metric.ball x r)) (fun y => ‖φ y‖ₑ) ≤
        localMaximalFunction 1 φ x := fun φ r hr hr1 => by
    unfold localMaximalFunction
    apply le_iSup_of_le r; apply le_iSup_of_le hr; apply le_iSup_of_le hr1; exact le_rfl
  conv_lhs => unfold localMaximalFunction
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hr1 => ?_
  calc laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ)
      ≤ laverage (volume.restrict (Metric.ball x r)) (fun y => ‖g y‖ₑ + ‖h y‖ₑ) :=
        laverage_mono_ae (ae_of_all _ hfgh)
    _ = laverage (volume.restrict (Metric.ball x r)) (fun y => ‖g y‖ₑ) +
          laverage (volume.restrict (Metric.ball x r)) (fun y => ‖h y‖ₑ) := by
        simp only [laverage_eq]
        rw [lintegral_add_left hg.enorm, ENNReal.add_div]
    _ ≤ _ := add_le_add (hmem g r hr hr1) (hmem h r hr hr1)

/-- **Subgoal** (`M_1`, `M_1 f` depends only on the a.e. class of `f`). -/
theorem congr_ae {f g : Rd d → ℝ} (h : f =ᵐ[volume] g) :
    localMaximalFunction 1 f = localMaximalFunction 1 g := by
  funext x
  unfold localMaximalFunction
  congr 1; funext r; congr 1; funext _; congr 1; funext _
  exact laverage_congr (ae_restrict_of_ae (h.mono fun y hy => by simp only [hy]))

end localMaximalFunction

end WeakPathwiseIto
