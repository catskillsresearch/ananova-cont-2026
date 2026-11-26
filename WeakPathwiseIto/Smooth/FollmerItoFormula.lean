/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Smooth.FollmerIntegral
public import WeakPathwiseIto.Smooth.Proposition31

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace follmer_ito_formula

variable {T : ℝ} {d : ℕ}

/-- **Subgoal** ([Föl81] proof: `∇f ∈ C^1_b` for `f ∈ C^2_b`). -/
theorem contDiffBounded_gradient {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    ContDiffBounded 1 (gradient f) := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient f = L ∘ fderiv ℝ f := rfl
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.1.fderiv_right (m := 1) (by norm_num)
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hg]; exact L.contDiff.comp hD
  · obtain ⟨C, hC⟩ := hf.2 (i + 1) (by omega)
    refine ⟨C, fun x => ?_⟩
    rw [hg, L.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]
    exact hC x

/-- **Subgoal** ([Föl81] proof: the Hessian of a `C²` function is symmetric). -/
theorem hessian_symm {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x u v : Rd d) :
    ⟪smoothHessian f x u, v⟫ = ⟪u, smoothHessian f x v⟫ := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient f = L ∘ fderiv ℝ f := rfl
  have hH : ∀ w, smoothHessian f x w = L (fderiv ℝ (fderiv ℝ f) x w) := fun w => by
    unfold smoothHessian
    rw [hg, L.comp_fderiv]
    rfl
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  rw [hH, hH]
  change ⟪(InnerProductSpace.toDual ℝ (Rd d)).symm _, v⟫ =
    ⟪u, (InnerProductSpace.toDual ℝ (Rd d)).symm _⟫
  rw [InnerProductSpace.toDual_symm_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  exact hs u v

/-- **Subgoal** ([Föl81] proof: at `t = T` the stopped left Riemann sum is the plain one). -/
theorem riemannSum_eq (p : Partition T) (g : Rd d → Rd d) (ω : ℝ → Rd d) :
    follmerIntegral.riemannSum p g ω T =
      ∑ k, ⟪g (ω (p.left k)), ω (p.right k) - ω (p.left k)⟫ := by
  unfold follmerIntegral.riemannSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [min_eq_left (show p.left k ≤ T from (p.t_mem k.castSucc).2),
    min_eq_left (show p.right k ≤ T from (p.t_mem k.succ).2)]

/-- **Subgoal** ([Föl81] proof: telescoping `f(ω(T)) - f(ω(0)) = ∑_k (f(ω(t_{k+1})) - f(ω(t_k)))`). -/
theorem sub_eq_sum (p : Partition T) (f : Rd d → ℝ) (ω : ℝ → Rd d) :
    f (ω T) - f (ω 0) = ∑ k, (f (ω (p.right k)) - f (ω (p.left k))) := by
  have h1 := Fin.sum_univ_succ (fun j => f (ω (p.t j)))
  have h2 := Fin.sum_univ_castSucc (fun j => f (ω (p.t j)))
  have hT : f (ω T) = f (ω (p.t (Fin.last p.m))) := by rw [p.t_last]
  have h0 : f (ω 0) = f (ω (p.t 0)) := by rw [p.t_zero]
  rw [Finset.sum_sub_distrib, hT, h0]
  change _ = ∑ k : Fin p.m, f (ω (p.t k.succ)) - ∑ k : Fin p.m, f (ω (p.t k.castSucc))
  linarith

/-- **Subgoal** ([Föl81] proof: second-order Taylor remainder): if `‖∇²f(z) - ∇²f(x)‖ ≤ ε` on the
segment `[x, y]`, then `|f(y) - f(x) - ∇f(x)·(y-x) - ½⟨∇²f(x)(y-x), y-x⟩| ≤ ε |y-x|²`. -/
theorem abs_taylor2_le {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) {x y : Rd d} {ε : ℝ}
    (hε : ∀ z ∈ segment ℝ x y, ‖smoothHessian f z - smoothHessian f x‖ ≤ ε) :
    |f y - f x - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪smoothHessian f x (y - x), y - x⟫| ≤
      ε * ‖y - x‖ ^ 2 := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hgd : Differentiable ℝ (gradient f) :=
    (L.contDiff.comp (hf.fderiv_right (m := 1) (by norm_num))).differentiable (by norm_num)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set H := smoothHessian f x with hHdef
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε x (left_mem_segment ℝ x y))
  have hgrad : ∀ z w, fderiv ℝ f z w = ⟪gradient f z, w⟫ := fun z w =>
    InnerProductSpace.toDual_symm_apply.symm
  have hball : ∀ z ∈ segment ℝ x y, ‖z - x‖ ≤ ‖y - x‖ := fun z hz => by
    have := (convex_closedBall x ‖y - x‖).segment_subset (Metric.mem_closedBall_self (norm_nonneg _))
      (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hT1 : ∀ z ∈ segment ℝ x y, ‖gradient f z - gradient f x - H (z - x)‖ ≤ ε * ‖y - x‖ := by
    intro z hz
    have hsub : segment ℝ z x ⊆ segment ℝ x y :=
      (convex_segment x y).segment_subset hz (left_mem_segment ℝ x y)
    have h := proposition_3_1.norm_taylor_le (f := gradient f) hgd (x := z) (y := x) (ε := ε)
      (fun w hw => hε w (hsub hw))
    have e1 : fderiv ℝ (gradient f) x (x - z) = -(H (z - x)) := by
      rw [← map_neg, neg_sub]; rfl
    have e : gradient f x - gradient f z - fderiv ℝ (gradient f) x (x - z) =
        -(gradient f z - gradient f x - H (z - x)) := by rw [e1]; abel
    rw [e, norm_neg, norm_sub_rev x z] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hball z hz) hε0)
  have hφ := fun z => ((hfd z).hasFDerivAt.sub ((hasFDerivAt_const (gradient f x) z).inner (𝕜 := ℝ)
    ((hasFDerivAt_id z).sub_const x))).sub
    (((H.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)).inner (𝕜 := ℝ)
      ((hasFDerivAt_id z).sub_const x)).const_mul (1 / 2))
  have key := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (C := ε * ‖y - x‖) (fun z _ => (hφ z).differentiableAt)
    (fun z hz => by
      rw [(hφ z).fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      calc _ = ‖⟪gradient f z - gradient f x - H (z - x), w⟫‖ := by
            congr 1
            simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
              hgrad, inner_sub_left, ContinuousLinearMap.zero_apply, inner_zero_left,
              id_eq, ContinuousLinearMap.id_apply, smul_eq_mul]
            rw [hHdef, hessian_symm hf x w (z - x)]
            simp only [Function.comp_apply, real_inner_comm w]
            ring
        _ ≤ ‖gradient f z - gradient f x - H (z - x)‖ * ‖w‖ := by
            rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _
        _ ≤ ε * ‖y - x‖ * ‖w‖ := mul_le_mul_of_nonneg_right (hT1 z hz) (norm_nonneg _))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simp only [Pi.sub_apply, Function.comp_apply, id_eq, sub_self, inner_zero_right, map_zero,
    mul_zero, sub_zero] at key
  rw [Real.norm_eq_abs] at key
  calc _ = |f y - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪H (y - x), y - x⟫ - f x| := by
        congr 1; ring
    _ ≤ ε * ‖y - x‖ * ‖y - x‖ := key
    _ = ε * ‖y - x‖ ^ 2 := by ring

/-- **Subgoal** ([Föl81] proof: `∑_k ⟨∇²f(ω(t_k)) δ_kω, δ_kω⟩ → ∫_0^T ⟨∇²f(ω), d[ω]_π⟩`). -/
theorem tendsto_hessian_left {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    Tendsto (fun n => ∑ k, ⟪smoothHessian f (ω ((π n).left k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫) atTop
      (𝓝 (hQV.matrixIntegral
        (fun u i j => Rd.coord i (smoothHessian f (ω u) (Rd.basisVec j))) T)) := by
  have hg := contDiffBounded_gradient hf
  have hT : T ∈ Icc 0 T := ⟨(π 0).nonneg, le_rfl⟩
  have hR := proposition_3_1.tendsto_main hω hQV hg hT
  have hall : ∀ n, Finset.univ.filter (fun k => (π n).right k ≤ T) = Finset.univ := fun n =>
    Finset.filter_true_of_mem fun k _ => ((π n).t_mem k.succ).2
  simp only [hall] at hR
  have hH : Continuous (smoothHessian f) := hg.1.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hω).isBounded.exists_norm_le
  have hωC : ∀ s ∈ Icc 0 T, ‖ω s‖ ≤ C := fun s hs => hC _ (mem_image_of_mem ω hs)
  have hu := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : Rd d) C).uniformContinuousOn_of_continuous hH.continuousOn)
  set M : ℝ := |hQV.trace T| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hevS : ∀ᶠ n in atTop, ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 ≤ M :=
    ((lemma_4_2.tendsto_sum_sq hQV).eventually (gt_mem_nhds
      (show hQV.trace T < M by rw [hM]; linarith [le_abs_self (hQV.trace T)]))).mono
        fun n h => h.le
  have hdiff : Tendsto (fun n => ∑ k, (⟪smoothHessian f (ω ((π n).left k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
      ⟪smoothHessian f (ω ((π n).right k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫))
      atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδD⟩ := hu (ε / (2 * M)) (by positivity)
    filter_upwards [hevS, hosc.eventually (gt_mem_nhds hδ)] with n hn hon
    rw [Real.dist_eq, sub_zero]
    have hterm : ∀ k : Fin (π n).m, |⟪smoothHessian f (ω ((π n).left k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
      ⟪smoothHessian f (ω ((π n).right k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫| ≤
        ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 := fun k => by
      have hΔ := (lemma_4_2.norm_increment_le hω (π n) k).trans_lt hon
      have hlB : ω ((π n).left k) ∈ Metric.closedBall (0 : Rd d) C := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hωC _ ((π n).t_mem _)
      have hrB : ω ((π n).right k) ∈ Metric.closedBall (0 : Rd d) C := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hωC _ ((π n).t_mem _)
      have hD := hδD _ hlB _ hrB (by rw [dist_eq_norm, norm_sub_rev]; exact hΔ)
      rw [dist_eq_norm] at hD
      rw [← inner_sub_left, ← sub_apply]
      calc _ ≤ ‖(smoothHessian f (ω ((π n).left k)) - smoothHessian f (ω ((π n).right k)))
            (ω ((π n).right k) - ω ((π n).left k))‖ * ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (‖smoothHessian f (ω ((π n).left k)) - smoothHessian f (ω ((π n).right k))‖ *
            ‖ω ((π n).right k) - ω ((π n).left k)‖) * ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖) *
            ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD.le (norm_nonneg _))
              (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ ∑ k, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = ε / (2 * M) * ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ε / (2 * M) * M := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have h := hdiff.add hR
  rw [zero_add] at h
  refine h.congr fun n => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smoothHessian]
  ring

/-- **Subgoal** ([Föl81] proof: the second-order Taylor remainders sum to `o(1)`,
`≤ ρ_{∇²f}(osc) ∑ |δ_kω|²`). -/
theorem tendsto_remainder {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    Tendsto (fun n => ∑ k, (f (ω ((π n).right k)) - f (ω ((π n).left k)) -
        ⟪gradient f (ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
        1 / 2 * ⟪smoothHessian f (ω ((π n).left k)) (ω ((π n).right k) - ω ((π n).left k)),
          ω ((π n).right k) - ω ((π n).left k)⟫)) atTop (𝓝 0) := by
  sorry

end follmer_ito_formula

/-- **Subgoal** (Corollary 3.2 proof, [Föl81]). Föllmer's pathwise Itô formula [Föl81], used in the proof of Corollary 3.2: for
`f ∈ C^2_b` the left Riemann sums converge and
`f(ω(T)) = f(ω(0)) + ∫_0^T ∇f(ω) d^π ω + ½ ∫_0^T ⟨∇²f(ω), d[ω]_π⟩`. -/
theorem follmer_ito_formula {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    Tendsto (fun n => follmerIntegral.riemannSum (π n) (gradient f) ω T) atTop
        (𝓝 (follmerIntegral π (gradient f) ω T)) ∧
      f (ω T) = f (ω 0) + follmerIntegral π (gradient f) ω T +
        1 / 2 * hQV.matrixIntegral
          (fun u i j => Rd.coord i (smoothHessian f (ω u) (Rd.basisVec j))) T := by
  sorry

end WeakPathwiseIto
