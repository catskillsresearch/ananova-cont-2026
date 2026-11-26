/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Partition
public import WeakPathwiseIto.Occupation.OccupationConstant
public import WeakPathwiseIto.Occupation.IncrementBall

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace discreteOccupationDensity

variable {d : ℕ}

open scoped Classical in
/-- The single-increment density `𝓛^{n,i}_ω(x) = c_d (|x - a|^{2-d} + |x - b|^{2-d}) 1_{Q}(x)`
for an increment from `a` to `b`, set to `0` when `a = b` (eq. (7)). -/
def piece (a b : Rd d) (x : Rd d) : ℝ :=
  if a = b then 0 else
    (incrementBall a b).indicator
      (fun x => occupationConstant d * (‖x - a‖ ^ (2 - (d : ℝ)) + ‖x - b‖ ^ (2 - (d : ℝ)))) x

end discreteOccupationDensity

/-- The discrete weighted occupation density `𝓛^{π_n}_ω := ∑_i 𝓛^{n,i}_ω` (eq. (7)). -/
def discreteOccupationDensity {T : ℝ} {d : ℕ} (π : Partition T) (ω : ℝ → Rd d) (x : Rd d) : ℝ :=
  ∑ i : Fin π.m, discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x

namespace discreteOccupationDensity

variable {T : ℝ} {d : ℕ}

/-- **Subgoal** (Eq. (7)). -/
theorem piece_nonneg (a b x : Rd d) : 0 ≤ piece a b x := by
  unfold piece
  split_ifs
  · exact le_rfl
  · refine Set.indicator_nonneg (fun x _ => mul_nonneg ?_ ?_) x
    · exact div_nonneg (by norm_num) ENNReal.toReal_nonneg
    · exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- **Subgoal** (Eq. (7), `integral_piece` step a: affine change of variables on a ball): for
`λ > 0` and a linear isometry `L`, `∫_{B̄(m, λ/2)} g = λ^d ∫_{B̄(0,1/2)} g(m + λ L z) dz`. -/
theorem integral_closedBall_affine (m : Rd d) {l : ℝ} (hl : 0 < l) (L : Rd d ≃ₗᵢ[ℝ] Rd d)
    (g : Rd d → ℝ) :
    ∫ x in Metric.closedBall m (l / 2), g x =
      l ^ d * ∫ z in Metric.closedBall (0 : Rd d) (1 / 2), g (m + l • L z) := by
  sorry

/-- **Subgoal** (Eq. (7), `integral_piece` step b: rotating `e_1` to a unit vector): for
`d > 0` and `|u| = 1` there is a linear isometry `L` of `ℝ^d` with `L e_1 = u`. -/
theorem exists_isometry_basisVec (hd : 0 < d) {u : Rd d} (hu : ‖u‖ = 1) :
    ∃ L : Rd d ≃ₗᵢ[ℝ] Rd d, L (Rd.basisVec ⟨0, hd⟩) = u := by
  sorry

/-- **Subgoal** (Eq. (7), `integral_piece` step c: closed vs open ball): for `d > 0`, the set
integrals of any function over `B̄(0,r)` and `B(0,r)` agree (the sphere is Lebesgue-null). -/
theorem setIntegral_closedBall_eq_ball (hd : 0 < d) (r : ℝ) (g : Rd d → ℝ) :
    ∫ x in Metric.closedBall (0 : Rd d) r, g x = ∫ x in Metric.ball (0 : Rd d) r, g x := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine setIntegral_congr_set ?_
  have h0 : volume (Metric.sphere (0 : Rd d) r) = 0 := Measure.addHaar_sphere _ _ _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  simp only [Metric.mem_sphere, Metric.mem_closedBall, Metric.mem_ball, eq_iff_iff] at hx ⊢
  exact ⟨fun h => lt_of_le_of_ne h hx, le_of_lt⟩

/-- **Subgoal** (Eq. (7)). By homogeneity, `∫ 𝓛^{n,i}_ω = |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem integral_piece (a b : Rd d) : ∫ x, piece a b x = ‖b - a‖ ^ 2 := by
  sorry

/-- **Subgoal** (Eq. (7)). -/
theorem integrable_piece (a b : Rd d) : Integrable (piece a b) := by
  unfold piece
  split_ifs
  · exact integrable_zero _ _ _
  · have hmeas : MeasurableSet (incrementBall a b) := Metric.isClosed_closedBall.measurableSet
    rw [integrable_indicator_iff hmeas]
    set R : ℝ := ‖midpoint ℝ a b‖ + dist a b / 2 + 1 with hR
    have hsub : incrementBall a b ⊆ Metric.ball 0 R := fun x hx => by
      rw [incrementBall, Metric.mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      calc ‖x‖ = ‖(x - midpoint ℝ a b) + midpoint ℝ a b‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - midpoint ℝ a b‖ + ‖midpoint ℝ a b‖ := norm_add_le _ _
        _ < R := by rw [hR]; linarith
    have h : IntegrableOn (fun x : Rd d => occupationConstant d *
        (‖x - a‖ ^ (2 - (d : ℝ)) + ‖x - b‖ ^ (2 - (d : ℝ)))) (Metric.ball 0 R) :=
      Integrable.const_mul ((occupationConstant.integrableOn_term a R).add
        (occupationConstant.integrableOn_term b R)) _
    exact h.mono_set hsub

/-- **Subgoal** (Eq. (7)). `∫ 𝓛^{π_n}_ω = ∑_i |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem integral_eq (π : Partition T) (ω : ℝ → Rd d) :
    ∫ x, discreteOccupationDensity π ω x = ∑ i : Fin π.m, ‖ω (π.right i) - ω (π.left i)‖ ^ 2 := by
  sorry

end discreteOccupationDensity

end WeakPathwiseIto
