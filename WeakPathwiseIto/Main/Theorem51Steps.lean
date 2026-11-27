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
  refine ⟨hF.1.sub hG.1, fun i hi => ?_⟩
  obtain ⟨C1, hC1⟩ := hF.2 i hi
  obtain ⟨C2, hC2⟩ := hG.2 i hi
  have hi' : (i : WithTop ℕ∞) ≤ (2 : ℕ) := by exact_mod_cast hi
  refine ⟨C1 + C2, fun x => ?_⟩
  rw [iteratedFDeriv_sub_apply (hF.1.of_le hi').contDiffAt (hG.1.of_le hi').contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hC1 x) (hC2 x))

/-- **Subgoal** (Theorem 5.1 proof: linearity of `∇` and `∇²` on `C²`). -/
theorem gradient_smoothHessian_sub {F G : Rd d → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    gradient (F - G) = gradient F - gradient G ∧
      smoothHessian (F - G) = smoothHessian F - smoothHessian G := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hgF : Differentiable ℝ (gradient F) :=
    (L.contDiff.comp (hF.fderiv_right (m := 1) (by norm_num))).differentiable (by norm_num)
  have hgG : Differentiable ℝ (gradient G) :=
    (L.contDiff.comp (hG.fderiv_right (m := 1) (by norm_num))).differentiable (by norm_num)
  have hg : gradient (F - G) = gradient F - gradient G := by
    funext x
    change L (fderiv ℝ (F - G) x) = L (fderiv ℝ F x) - L (fderiv ℝ G x)
    rw [fderiv_sub (hFd x) (hGd x), map_sub]
  refine ⟨hg, ?_⟩
  funext x
  change fderiv ℝ (gradient (F - G)) x = fderiv ℝ (gradient F) x - fderiv ℝ (gradient G) x
  rw [hg]
  exact fderiv_sub (hgF x) (hgG x)

/-- **Subgoal** (Theorem 5.1 proof: linearity of the covariation on `C²_b`):
`[∇(F - G)(ω), ω]_π(t) = [∇F(ω), ω]_π(t) - [∇G(ω), ω]_π(t)`. -/
theorem pathwiseCovariation_sub {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F G : Rd d → ℝ} (hF : ContDiffBounded 2 F)
    (hG : ContDiffBounded 2 G) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pathwiseCovariation π (gradient (F - G)) ω t =
      pathwiseCovariation π (gradient F) ω t - pathwiseCovariation π (gradient G) ω t := by
  have hF1 := proposition_3_1 hω hQV hosc (follmer_ito_formula.contDiffBounded_gradient hF) t ht
  have hG1 := proposition_3_1 hω hQV hosc (follmer_ito_formula.contDiffBounded_gradient hG) t ht
  have hg := (gradient_smoothHessian_sub hF.1 hG.1).1
  have hlim : Tendsto (fun n => pathwiseCovariation.riemannSum (π n) (gradient (F - G)) ω t) atTop
      (𝓝 (pathwiseCovariation π (gradient F) ω t - pathwiseCovariation π (gradient G) ω t)) := by
    unfold pathwiseCovariation
    rw [hF1.limUnder_eq, hG1.limUnder_eq]
    refine (hF1.sub hG1).congr fun n => ?_
    rw [hg]
    unfold pathwiseCovariation.riemannSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.sub_apply]
    rw [← inner_sub_left]
    congr 1
    abel
  unfold pathwiseCovariation at hlim ⊢
  exact hlim.limUnder_eq

/-- **Subgoal** (Theorem 5.1 proof, uniqueness: weak derivatives are unique a.e., by the
fundamental lemma of the calculus of variations). -/
theorem isWeakDerivative_ae_unique {α : Fin d → ℕ} {f g g' : Rd d → ℝ}
    (hg : IsWeakDerivative α f g) (hg' : IsWeakDerivative α f g') : g =ᵐ[volume] g' := by
  obtain ⟨_, hgl, hgi⟩ := hg
  obtain ⟨_, hgl', hgi'⟩ := hg'
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgl.sub hgl') fun φ hφ hφc => by
    have hne : ((-1 : ℝ) ^ IsWeakDerivative.order α) ≠ 0 := pow_ne_zero _ (by norm_num)
    have heq : ∫ x, g x * φ x = ∫ x, g' x * φ x :=
      mul_left_cancel₀ hne ((hgi φ hφ hφc).symm.trans (hgi' φ hφ hφc))
    have hi : Integrable (fun x => φ x • g x) :=
      hgl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hi' : Integrable (fun x => φ x • g' x) :=
      hgl'.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi hi']
    simp only [smul_eq_mul, mul_comm (φ _)]
    rw [heq, sub_self]
  filter_upwards [h0] with x hx
  exact sub_eq_zero.1 hx

/-- **Subgoal** (Theorem 5.1 proof, uniqueness: weak Hessians are unique a.e. and
a.e.-strongly measurable). -/
theorem isWeakHessian_ae {F : Rd d → ℝ} {H H' : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H') :
    AEStronglyMeasurable H volume ∧ H =ᵐ[volume] H' := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hbv : ∀ i, b i = Rd.basisVec i := fun i => by
    rw [hb, EuclideanSpace.basisFun_apply]; rfl
  set E : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j => (innerSL ℝ (b j)).smulRight (b i)
    with hE
  have hrep : ∀ A : Rd d →L[ℝ] Rd d,
      A = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) • E i j := by
    intro A
    ext1 v
    have hv : v = ∑ j, ⟪b j, v⟫ • b j := (b.sum_repr' v).symm
    have hw : ∀ w : Rd d, w = ∑ i, ⟪b i, w⟫ • b i := fun w => (b.sum_repr' w).symm
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul]
    conv_lhs => arg 2; ext j; rw [hw (A (b j))]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hE,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Finset.smul_sum, smul_smul,
      Rd.coord, ← hbv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (b i)]
    ring_nf
  have hc : ∀ i j, AEStronglyMeasurable (fun x => Rd.coord i (H x (Rd.basisVec j))) volume :=
    fun i j => (hH i j).2.1.aestronglyMeasurable
  have hae : ∀ᵐ x ∂volume, ∀ i j, Rd.coord i (H x (Rd.basisVec j)) =
      Rd.coord i (H' x (Rd.basisVec j)) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact isWeakDerivative_ae_unique (hH i j) (hH' i j)
  refine ⟨?_, ?_⟩
  · have : H = fun x => ∑ i, ∑ j, Rd.coord i (H x (Rd.basisVec j)) • E i j :=
      funext fun x => hrep (H x)
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hc i j).smul_const _
  · filter_upwards [hae] with x hx
    rw [hrep (H x), hrep (H' x)]
    simp only [hx]

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
