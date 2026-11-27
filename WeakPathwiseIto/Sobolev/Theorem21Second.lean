/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.Theorem21First
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace

/-! # Steps of the proof of Theorem 2.1, second estimate ([BH93, Thm 2], `m = 2`)

Following [BH93, §2]: with the averaged Taylor polynomial
`T_Q f (w) = ⨍_{z ∈ Q} (f z + ⟪∇f z, w - z⟫)`, the bound [BH93, (5)] for `m = 2`
(`|f x - T_Q f x| ≤ C ∫_Q |∇²f| / |x - z|^{d-2}`) is proved for `C²` functions by Taylor's
formula along segments and a homothety change of variables, extended a.e. to `W^{2,1}` by
mollification, and passed to Lebesgue points by averaging over `Q ∩ B(x,r)`
([BH93, Lemma 2]).  The splitting [BH93, (8)] then reduces the estimate to this bound at `x`
and `y` plus the first estimate applied to the coordinates `∂_i f`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_2_1_second

variable {d : ℕ}

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²`, step 1: homothety with
quadratic weight): the substitution `z = x + s (y - x)` on a convex `Q ∋ x`. -/
theorem lintegral_comp_homothety_sq_le {Q : Set (Rd d)} (hQ : Convex ℝ Q)
    (hQm : MeasurableSet Q) {x : Rd d} (hx : x ∈ Q) {D : ℝ} (hD : ∀ z ∈ Q, dist z x ≤ D)
    {g : Rd d → ℝ≥0∞} (hg : Measurable g) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2 ≤
      ENNReal.ofReal (s ^ (-(d : ℝ) - 2)) *
        ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z := by
  have hs0 : 0 < s := hs.1
  set H : Rd d → ℝ≥0∞ :=
    Q.indicator ({z | dist z x ≤ s * D}.indicator fun z => g z * ‖z - x‖ₑ ^ 2) with hH
  have hinv : ENNReal.ofReal (s⁻¹ ^ 2) * ENNReal.ofReal s ^ 2 = 1 := by
    rw [← ENNReal.ofReal_pow hs0.le, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hs0.le) 2),
      ← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, ENNReal.ofReal_one]
  have step1 : ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2 ≤
      ∫⁻ y, ENNReal.ofReal (s⁻¹ ^ 2) * H (x + s • (y - x)) := by
    refine (lintegral_mono_ae ((ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy => ?_))).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hzQ : x + s • (y - x) ∈ Q := hQ.add_smul_sub_mem hx hy ⟨hs0.le, hs.2⟩
    have hzd : dist (x + s • (y - x)) x ≤ s * D := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hD y hy) hs0.le
    have hval : H (x + s • (y - x)) =
        g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ) ^ 2 := by
      rw [hH, indicator_of_mem hzQ, indicator_of_mem (show _ ∈ {z | dist z x ≤ s * D} from hzd),
        add_sub_cancel_left, enorm_smul, Real.enorm_of_nonneg hs0.le]
    rw [hval]
    refine le_of_eq ?_
    calc g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2
        = (ENNReal.ofReal (s⁻¹ ^ 2) * ENNReal.ofReal s ^ 2) * (g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal (s⁻¹ ^ 2) * (g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ) ^ 2) := by
          ring
  have step4 : ∫⁻ w, H (x + s • w) =
      ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ u, H (x + u) := by
    have := lintegral_map_equiv (fun u => H (x + u)) (MeasurableEquiv.smul₀ s hs0.ne') (μ := volume)
    have hmap : Measure.map (MeasurableEquiv.smul₀ s hs0.ne' : Rd d ≃ᵐ Rd d) volume =
        ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) • volume :=
      Measure.map_addHaar_smul volume hs0.ne'
    rw [hmap, lintegral_smul_measure] at this
    exact this.symm
  calc ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2
      ≤ ∫⁻ y, ENNReal.ofReal (s⁻¹ ^ 2) * H (x + s • (y - x)) := step1
    _ = ENNReal.ofReal (s⁻¹ ^ 2) * ∫⁻ w, H (x + s • w) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun w => H (x + s • w)) x]
    _ = ENNReal.ofReal (s⁻¹ ^ 2) *
          (ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ z, H z) := by
        rw [step4, lintegral_add_left_eq_self H x]
    _ = ENNReal.ofReal (s ^ (-(d : ℝ) - 2)) *
          ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z := by
        rw [hH, lintegral_indicator hQm, ← mul_assoc,
          ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hs0.le) 2)]
        congr 2
        rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 (pow_pos hs0 d)),
          Real.rpow_sub hs0, Real.rpow_neg hs0.le, Real.rpow_natCast,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²`, step 2: Taylor's formula
with integral remainder along the segment from `z` to `x`, reparametrised from `x`). -/
theorem abs_taylor_le {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x z : Rd d) :
    ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫| ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t *
        ‖fderiv ℝ (fderiv ℝ f) (x + t • (z - x))‖ₑ * ‖z - x‖ₑ ^ 2 := by
  set v := z - x
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD2 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable one_ne_zero
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv one_ne_zero
  have hl : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  -- φ' and φ''
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t :=
    fun t => (hD1 (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hφ' : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
    intro t
    have h := (hD2 (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
    exact h.clm_apply (hasDerivAt_const t v) |>.congr_deriv (by simp)
  set F : ℝ → ℝ := fun t => t * fderiv ℝ f (x + t • v) v - f (x + t • v) with hF
  have hFd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt F (t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
    intro t _
    have h := (((hasDerivAt_id t).mul (hφ' t)).sub (hφ t))
    refine h.congr_deriv ?_
    simp only [id]; ring
  have hcont : Continuous fun t : ℝ => t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
    have h1 : Continuous fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) :=
      hc2.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact continuous_id.mul ((h1.clm_apply continuous_const).clm_apply continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFd (hcont.intervalIntegrable 0 1)
  have hgrad : ⟪gradient f z, x - z⟫ = fderiv ℝ f z (x - z) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hxz : x - z = -v := by simp [v]
  have hkey : f x - f z - ⟪gradient f z, x - z⟫ =
      ∫ t in (0 : ℝ)..1, t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
    rw [hftc, hgrad, hxz, map_neg]
    simp only [hF, one_smul, zero_smul, add_zero, one_mul, zero_mul, zero_sub, v,
      add_sub_cancel]
    ring
  rw [hkey, ← Real.enorm_eq_ofReal_abs, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans
    (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_)
  have ht0 : 0 ≤ t := ht.1.le
  rw [enorm_mul, Real.enorm_of_nonneg ht0, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have h1 := (fderiv ℝ (fderiv ℝ f) (x + t • v) v).le_opNorm v
  have h2 := (fderiv ℝ (fderiv ℝ f) (x + t • v)).le_opNorm v
  calc ‖fderiv ℝ (fderiv ℝ f) (x + t • v) v v‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • v) v‖ * ‖v‖ := h1
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • v)‖ * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = _ := by ring

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²` on a convex `Q`). -/
theorem poincare2_of_contDiff (hd : 0 < d) {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f)
    {Q : Set (Rd d)} (hQ : Convex ℝ Q) (hQm : MeasurableSet Q) (hQb : Bornology.IsBounded Q)
    (hQ0 : volume Q ≠ 0) {x : Rd d} (hx : x ∈ Q) :
    ENNReal.ofReal |f x - ⨍ z in Q, (f z + ⟪gradient f z, x - z⟫)| ≤
      Metric.ediam Q ^ (d : ℝ) / (d * volume Q) *
        ∫⁻ z in Q, ‖fderiv ℝ (fderiv ℝ f) z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the coordinates `∂_i f` of the weak
gradient have weak gradient `(∂_j ∂_i f)_j` read off the weak Hessian). -/
theorem isWeakGradient_coord {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) (i : Fin d) :
    IsWeakGradient (fun z => Rd.coord i (G z))
      (fun z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • Rd.basisVec j) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the Hessian entries are integrable). -/
theorem coord_hessian_integrable {f : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hf : MemW 2 1 f) (hH : IsWeakHessian f H) (i j : Fin d) :
    Integrable fun z => Rd.coord i (H z (Rd.basisVec j)) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: `∂_i f ∈ W^{1,1}`). -/
theorem memW_coord {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hf : MemW 2 1 f) (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) (i : Fin d) :
    MemW 1 1 (fun z => Rd.coord i (G z)) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the mollification of a `W^{2,1}`
function is `C²`, with second derivatives the mollified weak Hessian entries). -/
theorem hessian_convolution {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) {ψ : Rd d → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiff ℝ 2 (fun x => ∫ y, f y * ψ (x - y)) ∧
      ∀ w i j, fderiv ℝ (fderiv ℝ (fun x => ∫ y, f y * ψ (x - y))) w (Rd.basisVec i)
          (Rd.basisVec j) = ∫ y, Rd.coord j (H y (Rd.basisVec i)) * ψ (w - y) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: a bilinear form is bounded by the sum of
its entries in the standard basis). -/
theorem norm_le_sum_entries (A : Rd d →L[ℝ] Rd d →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A (Rd.basisVec i) (Rd.basisVec j)| := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the local Riesz potential of order `2`
is bounded on `L¹(Q)`). -/
theorem lintegral_potential2_le (hd : 0 < d) {Q : Set (Rd d)} (hQb : Bornology.IsBounded Q)
    (hQm : MeasurableSet Q) :
    ∃ C : ℝ≥0, ∀ h : Rd d → ℝ, AEStronglyMeasurable h →
      ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2) ≤ C * ∫⁻ z in Q, ‖h z‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `m = 2` almost everywhere on `Q`
for `W^{2,1}` functions, by mollification). -/
theorem poincare2_ae (hd : 0 < d) : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)), MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H →
      ∀ Q : Set (Rd d), IsCubeOrBall Q →
        ∀ᵐ y ∂volume, y ∈ Q → ENNReal.ofReal |f y - ⨍ z in Q, (f z + ⟪G z, y - z⟫)| ≤
          K * ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Lemma 2] with `α = 2`, in the
unified form `⨍_{B(x,r)} |y - z|^{2-d} ≤ C (r + |x - z|)^{2-d}`). -/
theorem lintegral_ball_kernel2_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (x z : Rd d) {r : ℝ}, 0 < r →
    ∫⁻ y in Metric.ball x r, 1 / edist y z ^ ((d : ℝ) - 2) ≤
      C * volume (Metric.ball x r) / (ENNReal.ofReal r + edist x z) ^ ((d : ℝ) - 2) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Thm 1, (5)] with `m = 2` at a
Lebesgue point). -/
theorem abs_sub_taylorAverage_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)) (Q : Set (Rd d)) (x : Rd d) (c : ℝ), MemW 2 1 f →
      IsWeakGradient f G → IsWeakHessian f H → IsCubeOrBall Q → x ∈ Q →
        Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0) →
          ENNReal.ofReal |c - ⨍ z in Q, (f z + ⟪G z, x - z⟫)| ≤
            C * ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
  sorry

end theorem_2_1_second

end WeakPathwiseIto
