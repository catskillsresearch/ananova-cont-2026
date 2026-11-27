/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Main.WeakPathwiseIntegral
public import WeakPathwiseIto.Main.Eq18
public import WeakPathwiseIto.Main.SmoothItoAt
public import WeakPathwiseIto.Occupation.Lemma42
public import WeakPathwiseIto.Smooth.Proposition31
public import WeakPathwiseIto.Smooth.FollmerItoFormula

/-! # Steps of the proof of Theorem 5.1 -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

namespace theorem_5_1

/-- **Subgoal** (Theorem 5.1 proof: `C²_b` is closed under differences, used for `F_m - F_k`). -/
theorem contDiffBounded_sub {F G : Rd d → ℝ} (hF : ContDiffBounded 2 F) (hG : ContDiffBounded 2 G) :
    ContDiffBounded 2 (F - G) := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof: linearity of `∇` and `∇²` on `C²`). -/
theorem gradient_smoothHessian_sub {F G : Rd d → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    gradient (F - G) = gradient F - gradient G ∧
      smoothHessian (F - G) = smoothHessian F - smoothHessian G := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof: linearity of the covariation on `C²_b`):
`[∇(F - G)(ω), ω]_π(t) = [∇F(ω), ω]_π(t) - [∇G(ω), ω]_π(t)`. -/
theorem pathwiseCovariation_sub {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F G : Rd d → ℝ} (hF : ContDiffBounded 2 F)
    (hG : ContDiffBounded 2 G) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pathwiseCovariation π (gradient (F - G)) ω t =
      pathwiseCovariation π (gradient F) ω t - pathwiseCovariation π (gradient G) ω t := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, uniqueness: weak derivatives are unique a.e., by the
fundamental lemma of the calculus of variations). -/
theorem isWeakDerivative_ae_unique {α : Fin d → ℕ} {f g g' : Rd d → ℝ}
    (hg : IsWeakDerivative α f g) (hg' : IsWeakDerivative α f g') : g =ᵐ[volume] g' := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, uniqueness: weak Hessians are unique a.e. and
a.e.-strongly measurable). -/
theorem isWeakHessian_ae {F : Rd d → ℝ} {H H' : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H') :
    AEStronglyMeasurable H volume ∧ H =ᵐ[volume] H' := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, eqs. (19) and (23)): for `C²_b` functions `F, G` and
a.e.-equal measurable `H, H'`,
`|[∇F(ω), ω]_π(t) - [∇G(ω), ω]_π(t)| ≤ C_d (‖∇²F - H‖_{W^0} + ‖∇²G - H'‖_{W^0})`. -/
theorem abs_covariation_sub_le {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) :
    ∃ C : ℝ≥0, ∀ (F G : Rd d → ℝ) (H H' : Rd d → (Rd d →L[ℝ] Rd d)),
      ContDiffBounded 2 F → ContDiffBounded 2 G → AEStronglyMeasurable H volume →
      H =ᵐ[volume] H' → ∀ t ∈ Icc 0 T,
        ENNReal.ofReal |pathwiseCovariation π (gradient F) ω t -
            pathwiseCovariation π (gradient G) ω t| ≤
          C * (occupationSeminorm π ω (fun x => smoothHessian F x - H x) +
            occupationSeminorm π ω (fun x => smoothHessian G x - H' x)) := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, (20) and (15)): the covariations along an approximating
sequence form a Cauchy sequence, hence converge to `[∇F(ω), ω]_π(t)`. -/
theorem tendsto_covariation {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun m => pathwiseCovariation π (gradient (A.seq m)) ω t) atTop
      (𝓝 (weakCovariation A t)) := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, (22) and (14)): the pathwise integrals along an approximating
sequence converge to `F(ω(t)) - F(ω(0)) - ½ [∇F(ω), ω]_π(t)`. -/
theorem tendsto_integral {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun m => follmerIntegral π (gradient (A.seq m)) ω t) atTop
      (𝓝 (F (ω t) - F (ω 0) - 1 / 2 * weakCovariation A t)) := by
  sorry

end theorem_5_1

end WeakPathwiseIto
