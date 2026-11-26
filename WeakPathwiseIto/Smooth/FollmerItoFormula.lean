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
  sorry

/-- **Subgoal** ([Föl81] proof: `∑_k ⟨∇²f(ω(t_k)) δ_kω, δ_kω⟩ → ∫_0^T ⟨∇²f(ω), d[ω]_π⟩`). -/
theorem tendsto_hessian_left {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ} (hf : ContDiffBounded 2 f) :
    Tendsto (fun n => ∑ k, ⟪smoothHessian f (ω ((π n).left k))
        (ω ((π n).right k) - ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫) atTop
      (𝓝 (hQV.matrixIntegral
        (fun u i j => Rd.coord i (smoothHessian f (ω u) (Rd.basisVec j))) T)) := by
  sorry

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
