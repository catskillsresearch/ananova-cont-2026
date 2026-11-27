/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Occupation.Lemma42
public import WeakPathwiseIto.Smooth.Proposition31
public import WeakPathwiseIto.Smooth.FollmerItoFormula

/-! # Eq. (18) of Theorem 5.1, for `C²_b` functions -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

namespace theorem_5_1

namespace eq_18

/-! ### Eq. (18), proved directly for `C²_b` functions

The paper derives (18) from the second estimate of Theorem 2.1 applied per increment; that step
does not hold as written (see WeakPathwiseIto.md, "Theorem 5.1: proof of (18)"). We prove (18)
for `H ∈ C²_b` directly: on each increment `∇²H` is nearly constant (uniform continuity near the
compact set `ω([0,T])` and (6)), while `∫ 𝓛^{n,i}_ω = |δω|²`. -/

/-- **Subgoal** (Theorem 5.1 proof, (18), mean value step): if `‖∇²H‖ ≤ M` on the increment ball
`Q` of `a, b`, then `|(∇H(b) - ∇H(a)) · (b - a)| ≤ M |b - a|²`. -/
theorem abs_inner_increment_le {H : Rd d → ℝ} (hH : ContDiff ℝ 2 H) {a b : Rd d} {M : ℝ}
    (hM : ∀ z ∈ incrementBall a b, ‖smoothHessian H z‖ ≤ M) :
    |⟪gradient H b - gradient H a, b - a⟫| ≤ M * ‖b - a‖ ^ 2 := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient H = L ∘ fderiv ℝ H := rfl
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (m := 1) (by norm_num)
  have hgd : Differentiable ℝ (gradient H) := by
    rw [hg]; exact (L.contDiff.comp hD).differentiable one_ne_zero
  have ha : a ∈ incrementBall a b := by
    rw [incrementBall, Metric.mem_closedBall, dist_comm, dist_midpoint_left (𝕜 := ℝ)]
    simp
    linarith [dist_nonneg (x := a) (y := b)]
  have hb : b ∈ incrementBall a b := by
    rw [incrementBall, Metric.mem_closedBall, dist_comm, dist_midpoint_right (𝕜 := ℝ)]
    simp
    linarith [dist_nonneg (x := a) (y := b)]
  have hlip : ‖gradient H b - gradient H a‖ ≤ M * ‖b - a‖ :=
    (convex_closedBall _ _).norm_image_sub_le_of_norm_fderiv_le (fun z _ => hgd z) hM ha hb
  calc |⟪gradient H b - gradient H a, b - a⟫| ≤ ‖gradient H b - gradient H a‖ * ‖b - a‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (M * ‖b - a‖) * ‖b - a‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
    _ = M * ‖b - a‖ ^ 2 := by ring

/-- **Subgoal** (Theorem 5.1 proof, (18), lower bound by the occupation density): if
`m ≤ ‖G‖` on the increment ball `Q` of `a, b`, then `m |b - a|² ≤ ∫ |G| 𝓛^{n,i}_ω`. -/
theorem le_lintegral_piece {G : Rd d → (Rd d →L[ℝ] Rd d)} {a b : Rd d} {m : ℝ}
    (hm : ∀ z ∈ incrementBall a b, m ≤ ‖G z‖) :
    ENNReal.ofReal (m * ‖b - a‖ ^ 2) ≤
      ∫⁻ x, ‖G x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) := by
  rcases le_or_gt m 0 with hm0 | hm0
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hm0 (sq_nonneg _))]
    exact zero_le
  have hpt : ∀ x, ENNReal.ofReal m * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      ‖G x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) := fun x => by
    by_cases hx : x ∈ incrementBall a b
    · refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hm x hx)
    · have : discreteOccupationDensity.piece a b x = 0 := by
        unfold discreteOccupationDensity.piece
        split_ifs
        · rfl
        · exact indicator_of_notMem hx _
      rw [this, ENNReal.ofReal_zero, mul_zero, mul_zero]
  have hint : ∫⁻ x, ENNReal.ofReal (discreteOccupationDensity.piece a b x) =
      ENNReal.ofReal (‖b - a‖ ^ 2) := by
    rw [← discreteOccupationDensity.integral_piece a b,
      ofReal_integral_eq_lintegral_ofReal (discreteOccupationDensity.integrable_piece a b)
        (Eventually.of_forall fun x => discreteOccupationDensity.piece_nonneg a b x)]
  calc ENNReal.ofReal (m * ‖b - a‖ ^ 2)
      = ENNReal.ofReal m * ∫⁻ x, ENNReal.ofReal (discreteOccupationDensity.piece a b x) := by
        rw [hint, ENNReal.ofReal_mul hm0.le]
    _ = ∫⁻ x, ENNReal.ofReal m * ENNReal.ofReal (discreteOccupationDensity.piece a b x) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ _ := lintegral_mono hpt

/-- **Subgoal** (Theorem 5.1 proof, (18), one increment): if `∇²H` varies by at most `ε` on the
increment ball `Q` of `a, b` (from `a`), then
`|(∇H(b) - ∇H(a)) · (b - a)| ≤ ∫ |∇²H| 𝓛^{n,i}_ω + 2ε |b - a|²`. -/
theorem abs_inner_increment_le_lintegral {H : Rd d → ℝ} (hH : ContDiff ℝ 2 H) {a b : Rd d}
    {ε : ℝ} (hε : ∀ z ∈ incrementBall a b, ‖smoothHessian H z - smoothHessian H a‖ ≤ ε) :
    ENNReal.ofReal |⟪gradient H b - gradient H a, b - a⟫| ≤
      (∫⁻ x, ‖smoothHessian H x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x)) +
        ENNReal.ofReal (2 * ε * ‖b - a‖ ^ 2) := by
  set m0 := ‖smoothHessian H a‖ with hm0
  have hup : ∀ z ∈ incrementBall a b, ‖smoothHessian H z‖ ≤ m0 + ε := fun z hz => by
    have := norm_le_insert' (smoothHessian H z) (smoothHessian H a)
    linarith [hε z hz]
  have hlo : ∀ z ∈ incrementBall a b, m0 - ε ≤ ‖smoothHessian H z‖ := fun z hz => by
    have := norm_le_insert' (smoothHessian H a) (smoothHessian H z)
    rw [norm_sub_rev] at this
    linarith [hε z hz]
  calc ENNReal.ofReal |⟪gradient H b - gradient H a, b - a⟫|
      ≤ ENNReal.ofReal ((m0 + ε) * ‖b - a‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (abs_inner_increment_le hH hup)
    _ = ENNReal.ofReal ((m0 - ε) * ‖b - a‖ ^ 2 + 2 * ε * ‖b - a‖ ^ 2) := by congr 1; ring
    _ ≤ ENNReal.ofReal ((m0 - ε) * ‖b - a‖ ^ 2) + ENNReal.ofReal (2 * ε * ‖b - a‖ ^ 2) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add_left (le_lintegral_piece hlo) _

/-- **Subgoal** (Theorem 5.1 proof, (18), uniform continuity): for `H ∈ C²_b` and `ε > 0`,
eventually `‖∇²H(z) - ∇²H(ω(t_k))‖ ≤ ε` on every increment ball of `π_n`. -/
theorem eventually_hessian_close {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ}
    (hH : ContDiffBounded 2 H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ k : Fin (π n).m,
      ∀ z ∈ incrementBall (ω ((π n).left k)) (ω ((π n).right k)),
        ‖smoothHessian H z - smoothHessian H (ω ((π n).left k))‖ ≤ ε := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient H = L ∘ fderiv ℝ H := rfl
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.1.fderiv_right (m := 1) (by norm_num)
  have hgc : ContDiff ℝ 1 (gradient H) := by rw [hg]; exact L.contDiff.comp hD
  have hHc : Continuous (smoothHessian H) := hgc.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hω).isBounded.exists_norm_le
  have hωC : ∀ s ∈ Icc 0 T, ‖ω s‖ ≤ C := fun s hs => hC _ (mem_image_of_mem ω hs)
  obtain ⟨δ, hδ, hδD⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : Rd d) (C + 1)).uniformContinuousOn_of_continuous hHc.continuousOn)
    ε hε
  filter_upwards [hosc.eventually (gt_mem_nhds (lt_min hδ one_pos))] with n hon k z hz
  have hΔ := lemma_4_2.norm_increment_le hω (π n) k
  have hΔ' : ‖ω ((π n).right k) - ω ((π n).left k)‖ < min δ 1 := hΔ.trans_lt hon
  have hza : dist z (ω ((π n).left k)) ≤ ‖ω ((π n).right k) - ω ((π n).left k)‖ := by
    have h1 := dist_triangle z (midpoint ℝ (ω ((π n).left k)) (ω ((π n).right k))) (ω ((π n).left k))
    rw [dist_midpoint_left (𝕜 := ℝ)] at h1
    rw [incrementBall, Metric.mem_closedBall] at hz
    have h2 : dist (ω ((π n).left k)) (ω ((π n).right k)) =
        ‖ω ((π n).right k) - ω ((π n).left k)‖ := by rw [dist_comm, dist_eq_norm]
    simp only [Real.norm_ofNat] at h1
    linarith
  have ha : ‖ω ((π n).left k)‖ ≤ C := hωC _ ((π n).t_mem _)
  have haB : ω ((π n).left k) ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith
  have hzB : z ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_insert' z (ω ((π n).left k))
    rw [← dist_eq_norm] at this
    linarith [min_le_right δ 1]
  have := hδD z hzB _ haB (by linarith [min_le_left δ 1])
  rw [dist_eq_norm] at this
  exact this.le

/-- **Subgoal** (Theorem 5.1 proof, (18), summing the increments): for `H ∈ C²_b` and `ε > 0`,
eventually `∑_k |(∇H(ω(t_{k+1})) - ∇H(ω(t_k))) · δω_k| ≤ ∫ |∇²H| 𝓛^{π_n}_ω + ε`. -/
theorem eventually_sum_abs_le {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ} (hH : ContDiffBounded 2 H) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (∑ k : Fin (π n).m,
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫|) ≤
        (∫⁻ x, ‖smoothHessian H x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) +
          ENNReal.ofReal ε := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient H = L ∘ fderiv ℝ H := rfl
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.1.fderiv_right (m := 1) (by norm_num)
  have hgc : ContDiff ℝ 1 (gradient H) := by rw [hg]; exact L.contDiff.comp hD
  have hHc : Continuous (smoothHessian H) := hgc.continuous_fderiv (by norm_num)
  set M : ℝ := |hQV.trace T| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hevS : ∀ᶠ n in atTop, ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 ≤ M :=
    ((lemma_4_2.tendsto_sum_sq hQV).eventually (gt_mem_nhds
      (show hQV.trace T < M by rw [hM]; linarith [le_abs_self (hQV.trace T)]))).mono
        fun n h => h.le
  set ε' := ε / (2 * M) with hε'
  have hε'0 : 0 < ε' := by positivity
  filter_upwards [hevS, eventually_hessian_close hω hosc hH hε'0] with n hn hc
  have hI : ∑ k : Fin (π n).m, ∫⁻ x, ‖smoothHessian H x‖ₑ *
        ENNReal.ofReal (discreteOccupationDensity.piece (ω ((π n).left k)) (ω ((π n).right k)) x) =
      ∫⁻ x, ‖smoothHessian H x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x) := by
    have hmeas : ∀ k ∈ (Finset.univ : Finset (Fin (π n).m)), AEMeasurable (fun x =>
        ‖smoothHessian H x‖ₑ * ENNReal.ofReal
          (discreteOccupationDensity.piece (ω ((π n).left k)) (ω ((π n).right k)) x)) :=
      fun k _ => hHc.measurable.enorm.aemeasurable.mul
        (discreteOccupationDensity.integrable_piece _ _).aemeasurable.ennreal_ofReal
    rw [← lintegral_finset_sum' _ hmeas]
    congr 1
    funext x
    rw [discreteOccupationDensity, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => discreteOccupationDensity.piece_nonneg _ _ x), Finset.mul_sum]
  have hR : ∑ k : Fin (π n).m,
        ENNReal.ofReal (2 * ε' * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.mul_sum]
    calc 2 * ε' * ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 ≤ 2 * ε' * M :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ε := by rw [hε']; field_simp
  calc ENNReal.ofReal (∑ k : Fin (π n).m,
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫|)
      = ∑ k : Fin (π n).m, ENNReal.ofReal
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫| :=
        ENNReal.ofReal_sum_of_nonneg fun k _ => abs_nonneg _
    _ ≤ ∑ k : Fin (π n).m, ((∫⁻ x, ‖smoothHessian H x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity.piece (ω ((π n).left k)) (ω ((π n).right k)) x)) +
          ENNReal.ofReal (2 * ε' * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => abs_inner_increment_le_lintegral hH.1 (hc k)
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hI.le hR

/-- **Subgoal** (Theorem 5.1 proof, (18), the stopped sum): for `H ∈ C²_b` and `t ∈ [0,T]`,
`|∑_k (∇H(ω(t_{k+1} ∧ t)) - ∇H(ω(t_k ∧ t))) · (ω(t_{k+1} ∧ t) - ω(t_k ∧ t))|` is at most the
full sum `∑_k |(∇H(ω(t_{k+1})) - ∇H(ω(t_k))) · δω_k|` plus a term `→ 0` (the straddling
interval). -/
theorem abs_riemannSum_le {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ}
    (hH : ContDiffBounded 2 H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n,
      |pathwiseCovariation.riemannSum (π n) (gradient H) ω t| ≤
        (∑ k : Fin (π n).m,
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫|) + e n := by
  have hg := follmer_ito_formula.contDiffBounded_gradient hH
  refine ⟨fun n => |∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
      ⟪gradient H (ω t) - gradient H (ω ((π n).left k)), ω t - ω ((π n).left k)⟫|, ?_, fun n => ?_⟩
  · simpa using (proposition_3_1.tendsto_boundary hω hosc hg ht).abs
  rw [proposition_3_1.riemannSum_eq]
  refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun k _ _ => abs_nonneg _

end eq_18

/-- **Subgoal** (Theorem 5.1 proof, eq. (18)): for `H ∈ C²_b(ℝ^d)`,
`|[∇H(ω), ω]_π(t)| ≤ C_d ‖∇²H‖_{W^0_{ω,π}}` (proved directly; see `eq_18`). -/
theorem eq_18 {π : ℕ → Partition T} {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) :
    ∃ C : ℝ≥0, ∀ (H : Rd d → ℝ), ContDiffBounded 2 H → ∀ t ∈ Icc 0 T,
      ENNReal.ofReal |pathwiseCovariation π (gradient H) ω t| ≤
        C * occupationSeminorm π ω (smoothHessian H) := by
  have key : ∀ u v : ℕ → ℝ≥0∞, limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop := by
    intro u v
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    have h2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.2 hε.ne')).ne'
    have hu : limsup u atTop < limsup u atTop + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).1.ne h2
    have hv : limsup v atTop < limsup v atTop + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).2.ne h2
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_lt_of_limsup_lt hu, eventually_lt_of_limsup_lt hv] with n h1 h3
    calc (u + v) n = u n + v n := rfl
      _ ≤ (limsup u atTop + (ε : ℝ≥0∞) / 2) + (limsup v atTop + (ε : ℝ≥0∞) / 2) :=
          add_le_add h1.le h3.le
      _ = limsup u atTop + limsup v atTop + ε := by
          rw [add_add_add_comm, ENNReal.add_halves]
  refine ⟨1, fun H hH t ht => ?_⟩
  rw [ENNReal.coe_one, one_mul]
  have hg := follmer_ito_formula.contDiffBounded_gradient hH
  have hlim := proposition_3_1 hω hQV hosc hg t ht
  rw [pathwiseCovariation, hlim.limUnder_eq]
  set v := hQV.matrixIntegral
    (fun u i j => Rd.coord i (fderiv ℝ (gradient H) (ω u) (Rd.basisVec j))) t with hv
  obtain ⟨e, he, hRS⟩ := eq_18.abs_riemannSum_le (π := π) hω hosc hH ht
  have hA : Tendsto (fun n => ENNReal.ofReal |pathwiseCovariation.riemannSum (π n) (gradient H) ω t|)
      atTop (𝓝 (ENNReal.ofReal |v|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hlim.abs
  have he' : Tendsto (fun n => ENNReal.ofReal (e n)) atTop (𝓝 0) := by
    have h0 := (ENNReal.continuous_ofReal.tendsto 0).comp he
    rw [ENNReal.ofReal_zero] at h0
    exact h0
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hev := eq_18.eventually_sum_abs_le hω hQV hosc hH (ε := (ε : ℝ)) hε
  calc ENNReal.ofReal |v|
      = limsup (fun n => ENNReal.ofReal
          |pathwiseCovariation.riemannSum (π n) (gradient H) ω t|) atTop := hA.limsup_eq.symm
    _ ≤ limsup ((fun n => ∫⁻ x, ‖smoothHessian H x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) +
          fun n => ENNReal.ofReal (ε : ℝ) + ENNReal.ofReal (e n)) atTop := by
        refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [hev] with n hn
        rw [Pi.add_apply, ← add_assoc]
        calc ENNReal.ofReal |pathwiseCovariation.riemannSum (π n) (gradient H) ω t|
            ≤ ENNReal.ofReal ((∑ k : Fin (π n).m,
                |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
                  ω ((π n).right k) - ω ((π n).left k)⟫|) + e n) :=
              ENNReal.ofReal_le_ofReal (hRS n)
          _ ≤ _ := ENNReal.ofReal_add_le
          _ ≤ _ := add_le_add_left hn _
    _ ≤ occupationSeminorm π ω (smoothHessian H) +
          limsup (fun n => ENNReal.ofReal (ε : ℝ) + ENNReal.ofReal (e n)) atTop := key _ _
    _ = occupationSeminorm π ω (smoothHessian H) + ε := by
        rw [(by simpa using tendsto_const_nhds.add he' :
          Tendsto (fun n => ENNReal.ofReal (ε : ℝ) + ENNReal.ofReal (e n)) atTop
            (𝓝 (ENNReal.ofReal (ε : ℝ)))).limsup_eq, ENNReal.ofReal_coe_nnreal]

end theorem_5_1

end WeakPathwiseIto
