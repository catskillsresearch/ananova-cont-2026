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
  sorry

/-- **Subgoal** ([Föl81] proof: the Hessian of a `C²` function is symmetric). -/
theorem hessian_symm {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x u v : Rd d) :
    ⟪smoothHessian f x u, v⟫ = ⟪u, smoothHessian f x v⟫ := by
  sorry

/-- **Subgoal** ([Föl81] proof: at `t = T` the stopped left Riemann sum is the plain one). -/
theorem riemannSum_eq (p : Partition T) (g : Rd d → Rd d) (ω : ℝ → Rd d) :
    follmerIntegral.riemannSum p g ω T =
      ∑ k, ⟪g (ω (p.left k)), ω (p.right k) - ω (p.left k)⟫ := by
  sorry

/-- **Subgoal** ([Föl81] proof: telescoping `f(ω(T)) - f(ω(0)) = ∑_k (f(ω(t_{k+1})) - f(ω(t_k)))`). -/
theorem sub_eq_sum (p : Partition T) (f : Rd d → ℝ) (ω : ℝ → Rd d) :
    f (ω T) - f (ω 0) = ∑ k, (f (ω (p.right k)) - f (ω (p.left k))) := by
  sorry

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
