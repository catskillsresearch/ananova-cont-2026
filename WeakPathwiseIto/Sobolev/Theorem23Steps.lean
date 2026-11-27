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
  obtain ⟨C0, -, hC0⟩ := lemma_2_2 d hα
  refine ⟨C0, fun Q g hQ hg x hx R hR => ?_⟩
  have h := hC0 Q (fun z => ‖g z‖) hQ hg.norm.integrableOn x hx
  have hM : localMaximalFunction (Metric.ediam Q) (fun z => ‖g z‖) x ≤
      localMaximalFunction R g x := by
    unfold localMaximalFunction
    refine iSup_mono fun r => iSup_mono fun _ => iSup_le fun h => ?_
    refine le_trans (le_of_eq ?_) (le_iSup (fun _ : ENNReal.ofReal r < R =>
      laverage (volume.restrict (Metric.ball x r)) (fun y => ‖g y‖ₑ)) (h.trans_le hR))
    simp only [enorm_norm]
  simp only [enorm_norm] at h
  refine h.trans (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hR hα.le)) hM)

/-- **Subgoal** (Theorem 2.3 proof, Poincaré on balls, step 1: the Riesz potential `I¹` on a
ball `B` of radius `r` is bounded on `L¹(B)` with constant `C r`). -/
theorem lintegral_ball_potential_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (c : Rd d) (r : ℝ), 0 < r →
    ∀ g : Rd d → ℝ, AEStronglyMeasurable g →
      ∫⁻ y in Metric.ball c r, ∫⁻ z in Metric.ball c r, ‖g z‖ₑ / edist y z ^ ((d : ℝ) - 1) ≤
        C * ENNReal.ofReal r * ∫⁻ z in Metric.ball c r, ‖g z‖ₑ := by
  obtain ⟨C0, -, hC0⟩ := lemma_2_2 d (α := 1) one_pos
  refine ⟨C0 * 4, fun c r hr h hh => ?_⟩
  set B := Metric.ball c r with hB
  set C : ℝ≥0∞ := ((C0 * 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r with hCdef
  have hD : 0 < 2 * r := by positivity
  -- the kernel integral is uniformly bounded on `B`
  have hK : ∀ z ∈ B, ∫⁻ y in B, 1 / edist y z ^ ((d : ℝ) - 1) ≤ C := by
    intro z hz
    have hsub : B ⊆ Metric.closedBall z (2 * r) := fun y hy => by
      rw [Metric.mem_closedBall]
      have := dist_triangle y c z
      have h1 : dist y c < r := hy
      have h2 : dist c z < r := by rw [dist_comm]; exact hz
      linarith
    have hball : IsCubeOrBall (Metric.closedBall z (2 * r)) := ⟨z, 2 * r, hD, Or.inr (Or.inl rfl)⟩
    have hlem := hC0 (Metric.closedBall z (2 * r)) (fun _ => (1 : ℝ)) hball
      (integrableOn_const measure_closedBall_lt_top.ne) z (Metric.mem_closedBall_self hD.le)
    have hM : localMaximalFunction (Metric.ediam (Metric.closedBall z (2 * r)))
        (fun _ : Rd d => (1 : ℝ)) z ≤ 1 := by
      refine iSup_le fun r => iSup_le fun _ => iSup_le fun _ => ?_
      rw [laverage_eq]
      simp only [enorm_one, lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact ENNReal.div_self_le_one
    have hdiam : Metric.ediam (Metric.closedBall z (2 * r)) ≤ ENNReal.ofReal (2 * (2 * r)) := by
      rw [← ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top]
      exact ENNReal.ofReal_le_ofReal (Metric.diam_closedBall hD.le)
    calc ∫⁻ y in B, 1 / edist y z ^ ((d : ℝ) - 1)
        ≤ ∫⁻ y in Metric.closedBall z (2 * r), 1 / edist y z ^ ((d : ℝ) - 1) := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.closedBall z (2 * r),
            ‖(fun _ : Rd d => (1 : ℝ)) y‖ₑ / edist z y ^ ((d : ℝ) - 1) := by
          simp only [enorm_one, edist_comm]
      _ ≤ C0 * Metric.ediam (Metric.closedBall z (2 * r)) ^ (1 : ℝ) *
            localMaximalFunction (Metric.ediam (Metric.closedBall z (2 * r))) (fun _ => (1 : ℝ)) z :=
          hlem
      _ ≤ C0 * ENNReal.ofReal (2 * (2 * r)) * 1 := by
          rw [ENNReal.rpow_one]; gcongr
      _ = C := by
          rw [mul_one, hCdef, show 2 * (2 * r) = 4 * r by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.coe_mul, mul_assoc]
          norm_num
  have hm : AEMeasurable (Function.uncurry fun (y z : Rd d) => ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1))
      ((volume.restrict B).prod (volume.restrict B)) := by
    have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖h p.2‖ₑ)
        ((volume.restrict B).prod (volume.restrict B)) :=
      hh.restrict.aemeasurable.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable fun p : Rd d × Rd d => edist p.1 p.2 ^ ((d : ℝ) - 1) :=
      (continuous_edist.measurable).pow_const _
    exact h1.div h2.aemeasurable
  calc ∫⁻ y in B, ∫⁻ z in B, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1)
      = ∫⁻ z in B, ∫⁻ y in B, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1) := lintegral_lintegral_swap hm
    _ = ∫⁻ z in B, ‖h z‖ₑ * ∫⁻ y in B, 1 / edist y z ^ ((d : ℝ) - 1) := by
        refine lintegral_congr fun z => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun y => ?_
        rw [div_eq_mul_inv, one_div]
    _ ≤ ∫⁻ z in B, ‖h z‖ₑ * C := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2
          (Eventually.of_forall fun z hz => ?_))
        exact mul_le_mul' le_rfl (hK z hz)
    _ = C * ∫⁻ z in B, ‖h z‖ₑ := by
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
          mul_comm]

/-- **Subgoal** (Theorem 2.3 proof, Poincaré on balls:
`∫_B |f - f_B| ≤ C r ∫_B |∇f|`). -/
theorem lintegral_abs_sub_average_ball_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ)
    (G : Rd d → Rd d), MemW 1 1 f → IsWeakGradient f G → ∀ (c : Rd d) (r : ℝ), 0 < r →
      ∫⁻ y in Metric.ball c r, ENNReal.ofReal |f y - ⨍ z in Metric.ball c r, f z| ≤
        C * ENNReal.ofReal r * ∫⁻ z in Metric.ball c r, ‖G z‖ₑ := by
  obtain ⟨K, hK⟩ := theorem_2_1_first.poincare_ae hd
  obtain ⟨C, hC⟩ := lintegral_ball_potential_le hd
  refine ⟨K * C, fun f G hf hG c r hr => ?_⟩
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) := theorem_2_1_first.coord_integrable hf hG
  have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGm : AEStronglyMeasurable G volume := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext hexpG
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGi i).aestronglyMeasurable.smul_const _
  have hball : IsCubeOrBall (Metric.ball c r) := ⟨c, r, hr, Or.inl rfl⟩
  have hpt := hK f G hf hG _ hball
  have hpot := hC c r hr (fun z => ‖G z‖) hGm.norm
  simp only [enorm_norm] at hpot
  calc ∫⁻ y in Metric.ball c r, ENNReal.ofReal |f y - ⨍ z in Metric.ball c r, f z|
      ≤ ∫⁻ y in Metric.ball c r, K * ∫⁻ z in Metric.ball c r, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 hpt)
    _ = K * ∫⁻ y in Metric.ball c r, ∫⁻ z in Metric.ball c r, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ K * (C * ENNReal.ofReal r * ∫⁻ z in Metric.ball c r, ‖G z‖ₑ) := mul_le_mul' le_rfl hpot
    _ = _ := by push_cast; ring

/-- **Subgoal** (Theorem 2.3 proof: averages over comparable concentric balls are close,
`|f_{B(x,s)} - f_{B(x,r)}| ≤ C r ⨍_{B(x,r)} |∇f|` for `r/2 ≤ s ≤ r`). -/
theorem abs_average_sub_average_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ)
    (G : Rd d → Rd d), MemW 1 1 f → IsWeakGradient f G → ∀ (x : Rd d) (r s : ℝ), 0 < s →
      s ≤ r → r ≤ 2 * s →
        ENNReal.ofReal |(⨍ y in Metric.ball x s, f y) - ⨍ y in Metric.ball x r, f y| ≤
          C * ENNReal.ofReal r *
            laverage (volume.restrict (Metric.ball x r)) (fun y => ‖G y‖ₑ) := by
  obtain ⟨C, hC⟩ := lintegral_abs_sub_average_ball_le hd
  refine ⟨2 ^ d * C, fun f G hf hG x r s hs hsr hrs => ?_⟩
  have hr : 0 < r := hs.trans_le hsr
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  set Bs := Metric.ball x s with hBs
  set Br := Metric.ball x r with hBr
  set a : ℝ := ⨍ y in Br, f y with ha
  have hVs0 : volume Bs ≠ 0 := (Metric.measure_ball_pos volume x hs).ne'
  have hVst : volume Bs ≠ ⊤ := measure_ball_lt_top.ne
  have hVr0 : volume Br ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVrt : volume Br ≠ ⊤ := measure_ball_lt_top.ne
  have hi : IntegrableOn f Bs := hfi.integrableOn
  -- Step A: average bound on the small ball
  have stepA : ENNReal.ofReal |(⨍ y in Bs, f y) - a| ≤
      (volume Bs)⁻¹ * ∫⁻ y in Bs, ENNReal.ofReal |f y - a| := by
    have hreal : volume.real Bs ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hVs0, hVst⟩
    have hint : IntegrableOn (fun y => f y - a) Bs := hi.sub (integrableOn_const hVst)
    have e : (⨍ y in Bs, f y) - a = (volume.real Bs)⁻¹ * ∫ y in Bs, (f y - a) := by
      rw [setAverage_eq, smul_eq_mul, integral_sub hi (integrableOn_const hVst), setIntegral_const,
        smul_eq_mul]
      field_simp
    rw [e, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg]
    calc ENNReal.ofReal ((volume.real Bs)⁻¹ * |∫ y in Bs, (f y - a)|)
        ≤ ENNReal.ofReal ((volume.real Bs)⁻¹ * ∫ y in Bs, |f y - a|) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
            (inv_nonneg.2 measureReal_nonneg))
      _ = (volume Bs)⁻¹ * ∫⁻ y in Bs, ENNReal.ofReal |f y - a| := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg),
            ofReal_integral_eq_lintegral_ofReal hint.abs (Eventually.of_forall fun _ => abs_nonneg _),
            measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hVs0 hVst),
            ENNReal.ofReal_toReal hVst]
  -- volume comparison
  have hvol : volume Br ≤ 2 ^ d * volume Bs := by
    rw [hBr, hBs, Measure.addHaar_ball_of_pos volume x hr, Measure.addHaar_ball_of_pos volume x hs,
      finrank_euclideanSpace_fin, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    rw [show (2 : ℝ≥0∞) ^ d = ENNReal.ofReal (2 ^ d) by rw [ENNReal.ofReal_pow (by norm_num)]; simp,
      ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le hrs d)
  have hinv : (volume Bs)⁻¹ ≤ 2 ^ d * (volume Br)⁻¹ := by
    have h2 : (2 : ℝ≥0∞) ^ d ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2t : (2 : ℝ≥0∞) ^ d ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    calc (volume Bs)⁻¹ = 2 ^ d * (2 ^ d * volume Bs)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl h2) (Or.inl h2t), ← mul_assoc,
            ENNReal.mul_inv_cancel h2 h2t, one_mul]
      _ ≤ 2 ^ d * (volume Br)⁻¹ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 hvol)
  have hlav : laverage (volume.restrict Br) (fun y => ‖G y‖ₑ) = (volume Br)⁻¹ * ∫⁻ y in Br, ‖G y‖ₑ := by
    rw [laverage_eq, Measure.restrict_apply_univ, ENNReal.div_eq_inv_mul]
  calc ENNReal.ofReal |(⨍ y in Bs, f y) - a|
      ≤ (volume Bs)⁻¹ * ∫⁻ y in Bs, ENNReal.ofReal |f y - a| := stepA
    _ ≤ (2 ^ d * (volume Br)⁻¹) * ∫⁻ y in Br, ENNReal.ofReal |f y - a| :=
        mul_le_mul' hinv (lintegral_mono_set (Metric.ball_subset_ball hsr))
    _ ≤ (2 ^ d * (volume Br)⁻¹) * (C * ENNReal.ofReal r * ∫⁻ z in Br, ‖G z‖ₑ) :=
        mul_le_mul' le_rfl (hC f G hf hG x r hr)
    _ = _ := by rw [hlav]; push_cast; ring

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
