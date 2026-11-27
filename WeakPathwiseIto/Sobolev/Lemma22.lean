/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.IsCubeOrBall
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace lemma_2_2

variable {d : ℕ}

/-- **Subgoal** (Lemma 2.2 proof, maximal function on a closed ball): for `0 < ρ` with
`ρ ≤ R`, `∫_{B̄(a,ρ)} |f| ≤ |B(a,ρ)| M_R f(a)`. -/
theorem lintegral_closedBall_le (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ) {R : ℝ≥0∞}
    (hρR : ENNReal.ofReal ρ ≤ R) :
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ ≤ volume (Metric.ball a ρ) * localMaximalFunction R f a := by
  set ν := volume.withDensity (fun x => ‖f x‖ₑ) with hνdef
  have hν : ∀ s, MeasurableSet s → ∫⁻ x in s, ‖f x‖ₑ = ν s := fun s hs =>
    (withDensity_apply _ hs).symm
  rw [hν _ Metric.isClosed_closedBall.measurableSet]
  have hsph : ν (Metric.sphere a ρ) = 0 := by
    rw [← hν _ Metric.isClosed_sphere.measurableSet]
    apply setLIntegral_measure_zero
    rcases subsingleton_or_nontrivial (Rd d) with h | h
    · have : Metric.sphere a ρ = ∅ := by
        ext x
        simp [Subsingleton.elim x a, hρ.ne, hρ.ne']
      rw [this, measure_empty]
    · exact Measure.addHaar_sphere volume a ρ
  have hcb : ν (Metric.closedBall a ρ) ≤ ν (Metric.ball a ρ) := by
    rw [← Metric.ball_union_sphere]
    exact (measure_union_le _ _).trans (by rw [hsph, add_zero])
  refine hcb.trans ?_
  have hU : Metric.ball a ρ = ⋃ n : ℕ, Metric.ball a (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ => Metric.ball a (ρ - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
    Metric.ball_subset_ball (by
      have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      have := one_div_le_one_div_of_le (by positivity) this
      linarith)
  conv_lhs => rw [hU]
  rw [hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  by_cases hr : ρ - 1 / ((n : ℝ) + 1) ≤ 0
  · rw [Metric.ball_eq_empty.2 hr, measure_empty]; exact bot_le
  push Not at hr
  rw [← hν _ Metric.isOpen_ball.measurableSet]
  have : Fact (volume (Metric.ball a (ρ - 1 / ((n : ℝ) + 1))) < ⊤) := ⟨measure_ball_lt_top⟩
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hlt : ENNReal.ofReal (ρ - 1 / ((n : ℝ) + 1)) < R :=
    ((ENNReal.ofReal_lt_ofReal_iff hρ).2 (by linarith)).trans_le hρR
  have hM : laverage (volume.restrict (Metric.ball a (ρ - 1 / ((n : ℝ) + 1)))) (fun y => ‖f y‖ₑ) ≤
      localMaximalFunction R f a := by
    unfold localMaximalFunction
    exact le_iSup_of_le (ρ - 1 / ((n : ℝ) + 1)) (le_iSup_of_le hr (le_iSup_of_le hlt le_rfl))
  rw [← measure_mul_laverage, Measure.restrict_apply_univ]
  exact mul_le_mul' (measure_mono (Metric.ball_subset_ball (by linarith))) hM

/-- **Subgoal** (Lemma 2.2 proof, `Q ⊂ B̄(x, diam Q)`): for `d ≥ 1`, a cube or ball has finite
positive diameter and lies in the closed ball of radius `diam Q` about each of its points. -/
theorem subset_closedBall (hd : 0 < d) {Q : Set (Rd d)} (hQ : IsCubeOrBall Q) {x : Rd d}
    (hx : x ∈ Q) : Metric.ediam Q ≠ ⊤ ∧ 0 < (Metric.ediam Q).toReal ∧
      Q ⊆ Metric.closedBall x (Metric.ediam Q).toReal := by
  sorry

/-- **Subgoal** (Lemma 2.2 proof, `α < d`, one dyadic shell): on
`{ρ/2^{k+1} < |y - x| ≤ ρ/2^k}`, `∫ |f| |x - y|^{α-d} ≤ 2^{d-α} ρ^α 2^{-kα} |B(0,1)| M_ρ f(x)`. -/
theorem lintegral_shell_le {α : ℝ} (hα : 0 < α) (hαd : α < d) (f : Rd d → ℝ) (x : Rd d)
    {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∫⁻ y in {y | ρ / 2 ^ (k + 1) < dist y x ∧ dist y x ≤ ρ / 2 ^ k},
        ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k) *
        volume (Metric.ball (0 : Rd d) 1) * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  sorry

/-- **Subgoal** (Lemma 2.2 proof, `α < d`): summing the dyadic shells,
`∫_{B̄(x,ρ)} |f| |x - y|^{α-d} ≤ C ρ^α M_ρ f(x)`. -/
theorem lintegral_closedBall_kernel_le_of_lt {α : ℝ} (hα : 0 < α) (hαd : α < d) :
    ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (x : Rd d) {ρ : ℝ}, 0 < ρ →
      ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
        C * ENNReal.ofReal ρ ^ α * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  sorry

/-- **Subgoal** (Lemma 2.2 proof, `d ≤ α`): the kernel is at most `ρ^{α-d}` on `B̄(x,ρ)`, so
`∫_{B̄(x,ρ)} |f| |x - y|^{α-d} ≤ |B(0,1)| ρ^α M_ρ f(x)`. -/
theorem lintegral_closedBall_kernel_le_of_ge {α : ℝ} (hα : 0 < α) (hαd : (d : ℝ) ≤ α) :
    ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (x : Rd d) {ρ : ℝ}, 0 < ρ →
      ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
        C * ENNReal.ofReal ρ ^ α * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  sorry

end lemma_2_2

/-- **Lemma 2.2** ([BH93, Lemma 3]). For `α > 0` there is `C_{α,d}` such that for every cube or ball `Q`, every
`f ∈ L^1(Q)` and every `x ∈ Q`,
`∫_Q |f(y)| / |x - y|^{d-α} dy ≤ C_{α,d} (diam Q)^α M_{diam Q} f(x)`. -/
theorem lemma_2_2 (d : ℕ) {α : ℝ} (hα : 0 < α) : ∃ C : ℝ≥0, 0 < C ∧
    ∀ (Q : Set (Rd d)) (f : Rd d → ℝ), IsCubeOrBall Q → IntegrableOn f Q →
      ∀ x ∈ Q,
        ∫⁻ y in Q, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
          C * Metric.ediam Q ^ α *
            localMaximalFunction (Metric.ediam Q) f x := by
  sorry

end WeakPathwiseIto
