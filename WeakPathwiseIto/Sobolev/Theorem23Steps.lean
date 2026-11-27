/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.Theorem21
public import WeakPathwiseIto.Sobolev.Lemma22

/-! # Steps of the proof of Theorem 2.3 ([BH93, Thm 3])

Following [BH93, Thm 3]: take `Q` the closed ball with diameter `[x, y]`, so `diam Q ≤ |x - y|`,
apply Theorem 2.1 on `Q` and bound the local Riesz potentials by Lemma 2.2 ([BH93, Lemma 3]).
Theorem 2.1 needs `x, y` to be Lebesgue points; when the relevant maximal functions are finite
this holds (Poincaré on balls makes the ball averages Cauchy), and when one is infinite the
right-hand side is `∞`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_2_3

variable {d : ℕ}

/-- **Subgoal** (Theorem 2.3 proof: the ball with diameter `[x, y]`). -/
theorem closedBall_midpoint {x y : Rd d} (hxy : x ≠ y) :
    IsCubeOrBall (Metric.closedBall (midpoint ℝ x y) (dist x y / 2)) ∧
      x ∈ Metric.closedBall (midpoint ℝ x y) (dist x y / 2) ∧
      y ∈ Metric.closedBall (midpoint ℝ x y) (dist x y / 2) ∧
      Metric.ediam (Metric.closedBall (midpoint ℝ x y) (dist x y / 2)) ≤ edist x y := by
  have hr : 0 < dist x y / 2 := by have := dist_pos.2 hxy; positivity
  have hx : x ∈ Metric.closedBall (midpoint ℝ x y) (dist x y / 2) := by
    rw [Metric.mem_closedBall, dist_left_midpoint (𝕜 := ℝ)]
    simp; linarith
  have hy : y ∈ Metric.closedBall (midpoint ℝ x y) (dist x y / 2) := by
    rw [Metric.mem_closedBall, dist_right_midpoint (𝕜 := ℝ)]
    simp; linarith
  refine ⟨⟨_, _, hr, Or.inr (Or.inl rfl)⟩, hx, hy, Metric.ediam_le fun a ha b hb => ?_⟩
  rw [edist_dist, edist_dist]
  refine ENNReal.ofReal_le_ofReal ((dist_triangle a (midpoint ℝ x y) b).trans ?_)
  have h1 := Metric.mem_closedBall.1 ha
  have h2 := Metric.mem_closedBall.1 hb
  rw [dist_comm] at h2
  linarith

/-- **Subgoal** (Theorem 2.3 proof: Lemma 2.2 for vector- or operator-valued integrands, with
the maximal radius enlarged to any `R ≥ diam Q`). -/
theorem lintegral_kernel_le_maximal {F : Type*} [NormedAddCommGroup F] {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ≥0, ∀ (Q : Set (Rd d)) (g : Rd d → F), IsCubeOrBall Q → Integrable g →
      ∀ x ∈ Q, ∀ R : ℝ≥0∞, Metric.ediam Q ≤ R →
        ∫⁻ z in Q, ‖g z‖ₑ / edist x z ^ ((d : ℝ) - α) ≤
          C * R ^ α * localMaximalFunction R g x := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof, Poincaré on balls, step 1: the Riesz potential `I¹` on a
ball `B` of radius `r` is bounded on `L¹(B)` with constant `C r`). -/
theorem lintegral_ball_potential_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (c : Rd d) (r : ℝ), 0 < r →
    ∀ g : Rd d → ℝ, AEStronglyMeasurable g →
      ∫⁻ y in Metric.ball c r, ∫⁻ z in Metric.ball c r, ‖g z‖ₑ / edist y z ^ ((d : ℝ) - 1) ≤
        C * ENNReal.ofReal r * ∫⁻ z in Metric.ball c r, ‖g z‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof, Poincaré on balls:
`∫_B |f - f_B| ≤ C r ∫_B |∇f|`). -/
theorem lintegral_abs_sub_average_ball_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ)
    (G : Rd d → Rd d), MemW 1 1 f → IsWeakGradient f G → ∀ (c : Rd d) (r : ℝ), 0 < r →
      ∫⁻ y in Metric.ball c r, ENNReal.ofReal |f y - ⨍ z in Metric.ball c r, f z| ≤
        C * ENNReal.ofReal r * ∫⁻ z in Metric.ball c r, ‖G z‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof: averages over comparable concentric balls are close,
`|f_{B(x,s)} - f_{B(x,r)}| ≤ C r ⨍_{B(x,r)} |∇f|` for `r/2 ≤ s ≤ r`). -/
theorem abs_average_sub_average_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ)
    (G : Rd d → Rd d), MemW 1 1 f → IsWeakGradient f G → ∀ (x : Rd d) (r s : ℝ), 0 < s →
      s ≤ r → r ≤ 2 * s →
        ENNReal.ofReal |(⨍ y in Metric.ball x s, f y) - ⨍ y in Metric.ball x r, f y| ≤
          C * ENNReal.ofReal r *
            laverage (volume.restrict (Metric.ball x r)) (fun y => ‖G y‖ₑ) := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof: telescoping over dyadic radii,
`|f_{B(x,s)} - f_{B(x,r)}| ≤ C r M_R|∇f|(x)` for `0 < s ≤ r`, `r < R`). -/
theorem abs_average_sub_average_le_maximal (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ)
    (G : Rd d → Rd d), MemW 1 1 f → IsWeakGradient f G → ∀ (x : Rd d) (R : ℝ≥0∞) (r s : ℝ),
      0 < s → s ≤ r → ENNReal.ofReal r < R →
        ENNReal.ofReal |(⨍ y in Metric.ball x s, f y) - ⨍ y in Metric.ball x r, f y| ≤
          C * ENNReal.ofReal r * localMaximalFunction R G x := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof: if `M_R|∇f|(x) < ∞` then `x` is a Lebesgue point of `f`). -/
theorem isLebesguePoint_of_maximal_lt_top (hd : 0 < d) {f : Rd d → ℝ} {G : Rd d → Rd d}
    (hf : MemW 1 1 f) (hG : IsWeakGradient f G) {x : Rd d} {R : ℝ≥0∞} (hR : 0 < R)
    (hM : localMaximalFunction R G x < ⊤) : IsLebesguePoint f x := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof: at a common Lebesgue point of the coordinates of a locally
integrable `G`, some local maximal function of `G` is finite). -/
theorem maximal_lt_top_of_isLebesguePoint {G : Rd d → Rd d}
    (hG : ∀ i, LocallyIntegrable fun z => Rd.coord i (G z)) {x : Rd d}
    (hx : ∀ i, IsLebesguePoint (fun z => Rd.coord i (G z)) x) :
    ∃ R : ℝ≥0∞, 0 < R ∧ localMaximalFunction R G x < ⊤ := by
  sorry

/-- **Subgoal** (Theorem 2.3 proof: the gradient of `∂_i f` is dominated by the Hessian). -/
theorem maximal_coord_hessian_le {H : Rd d → (Rd d →L[ℝ] Rd d)} (i : Fin d) (R : ℝ≥0∞)
    (x : Rd d) :
    localMaximalFunction R (fun z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • Rd.basisVec j) x ≤
      localMaximalFunction R H x := by
  sorry

end theorem_2_3

end WeakPathwiseIto
