/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The normalising constant `c_d := 2 / |B(0,1)|` of eq. (7). -/
def occupationConstant (d : ℕ) : ℝ := 2 / (volume (Metric.ball (0 : Rd d) 1)).toReal

namespace occupationConstant

/-- **Subgoal** (Eq. (7) c_d, step 1: ball scaling): `|B(0,1/2)| = 2^{-d} |B(0,1)|`. -/
theorem volume_ball_half {d : ℕ} (hd : 0 < d) :
    (volume (Metric.ball (0 : Rd d) (1 / 2))).toReal =
      (1 / 2 : ℝ) ^ d * (volume (Metric.ball (0 : Rd d) 1)).toReal := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [Measure.addHaar_ball volume (0 : Rd d) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **Subgoal** (Eq. (7) c_d, step 2: reflection `x ↦ -x`): the two terms of eq. (7) have the
same integral over `B(0,1/2)`. -/
theorem integral_reflect {d : ℕ} (hd : 0 < d) :
    ∫ x in Metric.ball (0 : Rd d) (1 / 2), ‖x + (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) =
      ∫ x in Metric.ball (0 : Rd d) (1 / 2), ‖x - (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) := by
  set v : Rd d := (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩
  have hm : MeasurePreserving (fun x : Rd d => -x) volume volume :=
    (LinearIsometryEquiv.neg ℝ (E := Rd d)).measurePreserving
  have h := hm.setIntegral_preimage_emb (Homeomorph.neg (Rd d)).measurableEmbedding
    (fun y => ‖y - v‖ ^ (2 - (d : ℝ))) (Metric.ball 0 (1 / 2))
  have hs : (fun x : Rd d => -x) ⁻¹' Metric.ball 0 (1 / 2) = Metric.ball 0 (1 / 2) := by
    ext x; simp
  rw [← h, hs]
  refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
  rw [show -x - v = -(x + v) by abel, norm_neg]

/-- **Subgoal** (Eq. (7) c_d, step 3: local integrability): `x ↦ |x - y|^{2-d}` is integrable on
a ball. -/
theorem integrableOn_term {d : ℕ} (y : Rd d) (R : ℝ) :
    IntegrableOn (fun x : Rd d => ‖x - y‖ ^ (2 - (d : ℝ))) (Metric.ball 0 R) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : ∀ x : Rd 0, x - y = 0 := fun x => Subsingleton.elim _ _
    convert (integrableOn_zero : IntegrableOn (fun _ : Rd 0 => (0 : ℝ)) (Metric.ball 0 R) volume) using 1
    funext x
    rw [h0, norm_zero, Nat.cast_zero, sub_zero, Real.zero_rpow two_ne_zero]
  have hfin : Module.finrank ℝ (Rd d) = d := finrank_euclideanSpace_fin
  have hg : IntegrableOn (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (Metric.ball 0 (R + ‖y‖)) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := (d : ℝ) - 2) (by rw [hfin]; exact hd)
      (by rw [hfin]; linarith) (Eventually.of_forall fun z => ?_)
      (measurable_norm.pow_const _).aestronglyMeasurable
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul, neg_sub]
  have hm := measurePreserving_sub_right (volume : Measure (Rd d)) y
  have h := (hm.integrableOn_comp_preimage (measurableEmbedding_subRight y)).2 hg
  refine h.mono_set fun x hx => ?_
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_preimage] at hx ⊢
  calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ < R + ‖y‖ := by linarith

/-- **Subgoal** (Eq. (7) c_d, Newton step 1: sphere mean): the average of `ω ↦ |rω - y|^{2-d}`
over the unit sphere `S^{d-1}` (for the surface measure `volume.toSphere`). -/
def sphereMean (d : ℕ) (r : ℝ) (y : Rd d) : ℝ :=
  ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ *
    ∫ ω, ‖r • (ω : Rd d) - y‖ ^ (2 - (d : ℝ)) ∂(volume : Measure (Rd d)).toSphere

/-- **Subgoal** (Eq. (7) c_d, Newton step 2: polar coordinates on a ball): for `f` integrable on
`B(0,R)`, `∫_{B(0,R)} f = ∫_0^R r^{d-1} ∫_{S^{d-1}} f(rω) dσ(ω) dr`. -/
theorem integral_ball_polar {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) {f : Rd d → ℝ}
    (hf : IntegrableOn f (Metric.ball 0 R)) :
    ∫ x in Metric.ball (0 : Rd d) R, f x =
      ∫ r in Ioo 0 R, r ^ (d - 1) *
        ∫ ω, f (r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 3: rotation invariance): the surface measure on
`S^{d-1}` is invariant under linear isometries. -/
theorem integral_toSphere_isometry {d : ℕ} (L : Rd d ≃ₗᵢ[ℝ] Rd d) (g : Rd d → ℝ) :
    ∫ ω, g (L (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere =
      ∫ ω, g (ω : Rd d) ∂(volume : Measure (Rd d)).toSphere := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 4: the sphere mean is radial): `sphereMean d r y` only
depends on `|y|`. -/
theorem sphereMean_radial {d : ℕ} (r : ℝ) {y y' : Rd d} (h : ‖y‖ = ‖y'‖) :
    sphereMean d r y = sphereMean d r y' := by
  sorry

open Laplacian in
/-- **Subgoal** (Eq. (7) c_d, Newton step 5: the Newton kernel is harmonic): for `d ≥ 3` and
`z ≠ 0`, `Δ |z|^{2-d} = 0`. -/
theorem laplacian_newtonKernel {d : ℕ} (hd : 3 ≤ d) {z : Rd d} (hz : z ≠ 0) :
    Δ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) z = 0 := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 6: the sphere mean is harmonic off the sphere): for
`d ≥ 3`, `r > 0` and `|y| ≠ r`, `sphereMean d r` is harmonic at `y`. -/
theorem harmonicAt_sphereMean {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) {y : Rd d}
    (hy : ‖y‖ ≠ r) : InnerProductSpace.HarmonicAt (sphereMean d r) y := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 7: radial harmonic functions): for `d ≥ 3`, a radial
function harmonic on `{|y| > r}` is `a + b |y|^{2-d}` there. -/
theorem radial_harmonic_eq {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 ≤ r) {u : Rd d → ℝ}
    (hu : ∀ y : Rd d, r < ‖y‖ → InnerProductSpace.HarmonicAt u y)
    (hrad : ∀ y y' : Rd d, ‖y‖ = ‖y'‖ → u y = u y') :
    ∃ a b : ℝ, ∀ y : Rd d, r < ‖y‖ → u y = a + b * ‖y‖ ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 8: behaviour at infinity): for `d ≥ 3` and `r > 0`,
`|y|^{d-2} sphereMean d r y → 1` as `|y| → ∞`. -/
theorem tendsto_sphereMean {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun y : Rd d => ‖y‖ ^ ((d : ℝ) - 2) * sphereMean d r y) (cocompact (Rd d))
      (𝓝 1) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 9: Newton's shell theorem outside the sphere): for
`d ≥ 3`, `0 < r < |y|`, `sphereMean d r y = |y|^{2-d}`. -/
theorem sphereMean_outside {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) {y : Rd d}
    (hy : r < ‖y‖) : sphereMean d r y = ‖y‖ ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 10: integrating over shells): Newton's theorem for a
ball, `d ≥ 3`. -/
theorem newton_ball_of_three_le {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hR : 0 < R) {y : Rd d}
    (hy : ‖y‖ = R) :
    ∫ x in Metric.ball (0 : Rd d) R, ‖x - y‖ ^ (2 - (d : ℝ)) =
      (volume (Metric.ball (0 : Rd d) R)).toReal * R ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 11: `d = 1`): Newton's theorem for an interval. -/
theorem newton_ball_dim_one {R : ℝ} (hR : 0 < R) {y : Rd 1} (hy : ‖y‖ = R) :
    ∫ x in Metric.ball (0 : Rd 1) R, ‖x - y‖ ^ (2 - ((1 : ℕ) : ℝ)) =
      (volume (Metric.ball (0 : Rd 1) R)).toReal * R ^ (2 - ((1 : ℕ) : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 12: `d = 2`): the kernel is `1`. -/
theorem newton_ball_dim_two {R : ℝ} {y : Rd 2} :
    ∫ x in Metric.ball (0 : Rd 2) R, ‖x - y‖ ^ (2 - ((2 : ℕ) : ℝ)) =
      (volume (Metric.ball (0 : Rd 2) R)).toReal * R ^ (2 - ((2 : ℕ) : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, step 4 = Newton step 13: Newton's theorem for a ball): for `|y| = R > 0`,
`∫_{B(0,R)} |x - y|^{2-d} dx = |B(0,R)| R^{2-d}` (mean value property of the Newton kernel). -/
theorem newton_ball {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) {y : Rd d} (hy : ‖y‖ = R) :
    ∫ x in Metric.ball (0 : Rd d) R, ‖x - y‖ ^ (2 - (d : ℝ)) =
      (volume (Metric.ball (0 : Rd d) R)).toReal * R ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d). Eq. (7): `c_d = [∫_{B(0,1/2)} (|x - e_1/2|^{2-d} + |x + e_1/2|^{2-d}) dx]⁻¹`. -/
theorem eq_inv_integral {d : ℕ} (hd : 0 < d) :
    occupationConstant d = (∫ x in Metric.ball (0 : Rd d) (1 / 2),
      (‖x - (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) +
        ‖x + (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ))))⁻¹ := by
  sorry

end occupationConstant

end WeakPathwiseIto
