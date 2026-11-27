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
  obtain ⟨C, hC⟩ := eq_18 hω hQV hosc
  refine ⟨C, fun F G H H' hF hG hHm hHH' t ht => ?_⟩
  have hcongr : ∀ f g : Rd d → (Rd d →L[ℝ] Rd d), f =ᵐ[volume] g →
      occupationSeminorm π ω f = occupationSeminorm π ω g := by
    intro f g h
    unfold occupationSeminorm
    congr 1
    funext n
    apply lintegral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]
  have hneg : ∀ f : Rd d → (Rd d →L[ℝ] Rd d),
      occupationSeminorm π ω (fun x => -f x) = occupationSeminorm π ω f := by
    intro f
    unfold occupationSeminorm
    simp only [enorm_neg]
  have hcF : Continuous (smoothHessian F) :=
    (follmer_ito_formula.contDiffBounded_gradient hF).1.continuous_fderiv (by norm_num)
  have hcG : Continuous (smoothHessian G) :=
    (follmer_ito_formula.contDiffBounded_gradient hG).1.continuous_fderiv (by norm_num)
  have hH'm : AEStronglyMeasurable H' volume := hHm.congr hHH'
  have m1 : AEStronglyMeasurable (fun x => smoothHessian F x - H x) volume :=
    hcF.aestronglyMeasurable.sub hHm
  have m2 : AEStronglyMeasurable (fun x => -(smoothHessian G x - H' x)) volume :=
    (hcG.aestronglyMeasurable.sub hH'm).neg
  calc ENNReal.ofReal |pathwiseCovariation π (gradient F) ω t -
          pathwiseCovariation π (gradient G) ω t|
      = ENNReal.ofReal |pathwiseCovariation π (gradient (F - G)) ω t| := by
        rw [pathwiseCovariation_sub hω hQV hosc hF hG ht]
    _ ≤ C * occupationSeminorm π ω (smoothHessian (F - G)) :=
        hC _ (contDiffBounded_sub hF hG) t ht
    _ = C * occupationSeminorm π ω ((fun x => smoothHessian F x - H x) +
          (fun x => -(smoothHessian G x - H' x))) := by
        rw [(gradient_smoothHessian_sub hF.1 hG.1).2]
        congr 1
        apply hcongr
        filter_upwards [hHH'] with x hx
        simp only [Pi.sub_apply, Pi.add_apply, hx]
        abel
    _ ≤ C * (occupationSeminorm π ω (fun x => smoothHessian F x - H x) +
          occupationSeminorm π ω (fun x => -(smoothHessian G x - H' x))) := by
        gcongr
        exact occupationSeminorm.add_le π ω m1 m2
    _ = _ := by rw [hneg (fun x => smoothHessian G x - H' x)]

/-- **Subgoal** (Theorem 5.1 proof, (20) and (15)): the covariations along an approximating
sequence form a Cauchy sequence, hence converge to `[∇F(ω), ω]_π(t)`. -/
theorem tendsto_covariation {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun m => pathwiseCovariation π (gradient (A.seq m)) ω t) atTop
      (𝓝 (weakCovariation A t)) := by
  obtain ⟨hHm, -⟩ := isWeakHessian_ae hH hH
  obtain ⟨C, hC⟩ := abs_covariation_sub_le hω hQV hosc
  set s : ℕ → ℝ≥0∞ := fun m =>
    occupationSeminorm π ω (fun x => smoothHessian (A.seq m) x - H x) with hs
  set u : ℕ → ℝ := fun m => pathwiseCovariation π (gradient (A.seq m)) ω t with hu
  have hs0 : Tendsto s atTop (𝓝 0) := A.tendsto_hessian
  have hfin : ∀ᶠ m in atTop, s m ≠ ⊤ :=
    (hs0.eventually (gt_mem_nhds zero_lt_one)).mono fun m h => ne_top_of_lt h
  have hr : Tendsto (fun m => (s m).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs0
    rw [ENNReal.toReal_zero] at this
    exact this
  have hbound : ∀ m k, 1 ≤ m → 1 ≤ k → s m ≠ ⊤ → s k ≠ ⊤ →
      |u m - u k| ≤ C * ((s m).toReal + (s k).toReal) := by
    intro m k hm hk hsm hsk
    have h := hC (A.seq m) (A.seq k) H H (A.smooth m hm) (A.smooth k hk) hHm
      (Filter.EventuallyEq.refl _ _) t ht
    have hne : (C : ℝ≥0∞) * (s m + s k) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hsm, hsk⟩)
    have := (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hsm hsk, ENNReal.coe_toReal] at this
  have hcauchy : CauchySeq u := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    have hη : 0 < ε / (2 * ((C : ℝ) + 1)) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hfin.and (hr.eventually (gt_mem_nhds hη))).and
      (eventually_ge_atTop 1))
    refine ⟨N, fun m hm k hk => ?_⟩
    obtain ⟨⟨hsm, hrm⟩, hm1⟩ := hN m hm
    obtain ⟨⟨hsk, hrk⟩, hk1⟩ := hN k hk
    rw [Real.dist_eq]
    have hC0 : (0 : ℝ) ≤ C := C.2
    have h0m : 0 ≤ (s m).toReal := ENNReal.toReal_nonneg
    have h0k : 0 ≤ (s k).toReal := ENNReal.toReal_nonneg
    calc |u m - u k| ≤ C * ((s m).toReal + (s k).toReal) := hbound m k hm1 hk1 hsm hsk
      _ ≤ C * (2 * (ε / (2 * ((C : ℝ) + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ hC0; linarith
      _ = ε * (C / ((C : ℝ) + 1)) := by field_simp
      _ < ε := by
          have : (C : ℝ) / ((C : ℝ) + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
          nlinarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [weakCovariation, ha.limUnder_eq]
  exact ha

/-- **Subgoal** (Theorem 5.1 proof, (22) and (14)): the pathwise integrals along an approximating
sequence converge to `F(ω(t)) - F(ω(0)) - ½ [∇F(ω), ω]_π(t)`. -/
theorem tendsto_integral {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun m => follmerIntegral π (gradient (A.seq m)) ω t) atTop
      (𝓝 (F (ω t) - F (ω 0) - 1 / 2 * weakCovariation A t)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, (π 0).nonneg⟩
  have h := ((A.tendsto_path t ht).sub (A.tendsto_path 0 h0)).sub
    ((tendsto_covariation hω hQV hosc hH A ht).const_mul (1 / 2))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hI := ito_at hω hQV hosc (A.smooth m hm) ht
  unfold follmerIntegral
  rw [hI.limUnder_eq]

end theorem_5_1

end WeakPathwiseIto
