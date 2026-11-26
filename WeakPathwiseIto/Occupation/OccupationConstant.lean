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
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

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
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set σ := (volume : Measure (Rd d)).toSphere with hσ
  set g : Rd d → ℝ := (Metric.ball 0 R).indicator f with hg
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_ball).2 hf
  have hmp := (volume : Measure (Rd d)).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd (Rd d)).measurableEmbedding
  set G : Metric.sphere (0 : Rd d) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => g ((p.2 : ℝ) • (p.1 : Rd d)) with hG
  have hGh : ∀ x : ({0}ᶜ : Set (Rd d)), G (homeomorphUnitSphereProd _ x) = g x := by
    intro x
    have := homeomorphUnitSphereProd_symm_apply_coe (Rd d) (homeomorphUnitSphereProd (Rd d) x)
    rw [Homeomorph.symm_apply_apply] at this
    simp only [hG]
    rw [← this]
  have hcomp : (G ∘ homeomorphUnitSphereProd (Rd d)) = fun x : ({0}ᶜ : Set (Rd d)) => g x := funext hGh
  have hGint : Integrable G (σ.prod (Measure.volumeIoiPow (Module.finrank ℝ (Rd d) - 1))) := by
    refine (hmp.integrable_comp_emb hemb).1 ?_
    rw [hcomp]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hgi.integrableOn
  have h1 : ∫ x in Metric.ball (0 : Rd d) R, f x =
      ∫ p, G p ∂(σ.prod (Measure.volumeIoiPow (Module.finrank ℝ (Rd d) - 1))) := by
    calc ∫ x in Metric.ball (0 : Rd d) R, f x = ∫ x, g x := (integral_indicator measurableSet_ball).symm
      _ = ∫ x : ({0}ᶜ : Set (Rd d)), g x ∂(volume.comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
      _ = ∫ x : ({0}ᶜ : Set (Rd d)), G (homeomorphUnitSphereProd _ x) ∂(volume.comap Subtype.val) := by
        simp_rw [hGh]
      _ = _ := hmp.integral_comp hemb G
  set H : ℝ → ℝ := fun a => ∫ ω, g (a • (ω : Rd d)) ∂σ with hH
  have h2 : ∀ r : Ioi (0 : ℝ), ∫ ω, G (ω, r) ∂σ = H r := fun r => rfl
  rw [h1, integral_prod_symm _ hGint]
  simp_rw [h2]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      (measurable_subtype_coe.pow_const _).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ (Module.finrank ℝ (Rd d) - 1)) • H a,
    finrank_euclideanSpace_fin]
  rw [setIntegral_congr_fun measurableSet_Ioi (g := (Iio R).indicator fun a =>
      a ^ (d - 1) * ∫ ω, f (a • (ω : Rd d)) ∂σ) fun a ha => ?_,
    setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
  have ha' : (0 : ℝ) < a := ha
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg ha'.le _), smul_eq_mul]
  by_cases har : a < R
  · rw [Set.indicator_of_mem (show a ∈ Iio R from har)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hmem : a • (ω : Rd d) ∈ Metric.ball (0 : Rd d) R := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ha'.le, norm_eq_of_mem_sphere ω, mul_one]
      exact har
    simp only [hg, Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem (show a ∉ Iio R from har)]
    have : H a = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
      have hmem : a • (ω : Rd d) ∉ Metric.ball (0 : Rd d) R := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ha'.le, norm_eq_of_mem_sphere ω, mul_one]
        exact har
      simp only [hg, Set.indicator_of_notMem hmem, Pi.zero_apply]
    rw [this, mul_zero]

/-- **Subgoal** (Eq. (7) c_d, Newton step 3: rotation invariance): the surface measure on
`S^{d-1}` is invariant under linear isometries. -/
theorem integral_toSphere_isometry {d : ℕ} (L : Rd d ≃ₗᵢ[ℝ] Rd d) (g : Rd d → ℝ) :
    ∫ ω, g (L (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere =
      ∫ ω, g (ω : Rd d) ∂(volume : Measure (Rd d)).toSphere := by
  have hS : ∀ (M : Rd d ≃ₗᵢ[ℝ] Rd d) (ω : Metric.sphere (0 : Rd d) 1),
      M (ω : Rd d) ∈ Metric.sphere (0 : Rd d) 1 := fun M ω => by
    rw [mem_sphere_zero_iff_norm, M.norm_map]; exact norm_eq_of_mem_sphere ω
  set Ls : Metric.sphere (0 : Rd d) 1 → Metric.sphere (0 : Rd d) 1 := fun ω => ⟨L ω, hS L ω⟩
    with hLs
  set Ls' : Metric.sphere (0 : Rd d) 1 → Metric.sphere (0 : Rd d) 1 :=
    fun ω => ⟨L.symm ω, hS L.symm ω⟩ with hLs'
  have hmeas : Measurable Ls :=
    ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hmeas' : Measurable Ls' :=
    ((L.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  have hinv : Function.LeftInverse Ls' Ls := fun ω => Subtype.ext (L.symm_apply_apply _)
  have hinv' : Function.RightInverse Ls' Ls := fun ω => Subtype.ext (L.apply_symm_apply _)
  have hemb : MeasurableEmbedding Ls := MeasurableEmbedding.of_measurable_inverse hmeas
    (by rw [hinv'.surjective.range_eq]; exact MeasurableSet.univ) hmeas' hinv
  have hset : ∀ s : Set (Metric.sphere (0 : Rd d) 1),
      Ioo (0 : ℝ) 1 • ((↑) '' (Ls ⁻¹' s) : Set (Rd d)) = L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    intro s
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, _, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨a, ha, _, ⟨Ls ω, hω, rfl⟩, by rw [L.map_smul]⟩
    · rintro ⟨a, ha, _, ⟨ω', hω', rfl⟩, hx⟩
      refine ⟨a, ha, _, ⟨Ls' ω', ?_, rfl⟩, ?_⟩
      · rw [hinv' ω']; exact hω'
      · apply L.injective
        rw [L.map_smul, ← hx]
        exact congrArg (a • ·) (L.apply_symm_apply _)
  have hL : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) := L.measurePreserving
  have hmp : MeasurePreserving Ls (volume : Measure (Rd d)).toSphere
      (volume : Measure (Rd d)).toSphere := by
    refine ⟨hmeas, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
      Measure.toSphere_apply' _ hs, hset]
    congr 1
    exact hL.measure_preimage_equiv _
  exact hmp.integral_comp hemb (fun ω => g (ω : Rd d))

/-- **Subgoal** (Eq. (7) c_d, Newton step 4: the sphere mean is radial): `sphereMean d r y` only
depends on `|y|`. -/
theorem sphereMean_radial {d : ℕ} (r : ℝ) {y y' : Rd d} (h : ‖y‖ = ‖y'‖) :
    sphereMean d r y = sphereMean d r y' := by
  unfold sphereMean
  congr 1
  set L : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (y - y'))ᗮ.reflection with hL
  have hLy : L y = y' := Submodule.reflection_sub h
  rw [← integral_toSphere_isometry L (fun z => ‖r • z - y'‖ ^ (2 - (d : ℝ)))]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [← hLy, ← L.map_smul, ← L.map_sub, L.norm_map]

/-- **Subgoal** (Eq. (7) c_d, Newton step 5a: first derivative of `|x|^p` off the origin): for
`x ≠ 0` and any real `p`, `D(|·|^p)(x) = p |x|^{p-2} ⟨x, ·⟩`. -/
theorem hasFDerivAt_norm_rpow_of_ne {d : ℕ} {x : Rd d} (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : Rd d => ‖x‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- **Subgoal** (Eq. (7) c_d, Newton step 5b: second derivative of `|x|^p` off the origin): for
`z ≠ 0`, `D²(|·|^p)(z)(e, e) = p(p-2)|z|^{p-4}⟨z,e⟩² + p|z|^{p-2}|e|²`. -/
theorem fderiv_fderiv_norm_rpow_apply {d : ℕ} {z : Rd d} (hz : z ≠ 0) (p : ℝ) (e : Rd d) :
    fderiv ℝ (fderiv ℝ (fun x : Rd d => ‖x‖ ^ p)) z e e =
      p * (p - 2) * ‖z‖ ^ (p - 4) * ⟪z, e⟫ ^ 2 + p * ‖z‖ ^ (p - 2) * ‖e‖ ^ 2 := by
  have hev : fderiv ℝ (fun x : Rd d => ‖x‖ ^ p) =ᶠ[𝓝 z]
      fun w => (p * ‖w‖ ^ (p - 2)) • innerSL ℝ w := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact (hasFDerivAt_norm_rpow_of_ne hw p).fderiv
  have hc := (hasFDerivAt_norm_rpow_of_ne hz (p - 2)).const_mul p
  have hI : HasFDerivAt (fun w : Rd d => innerSL ℝ w) (innerSL ℝ) z := (innerSL ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Rd d => (p * ‖w‖ ^ (p - 2)) • innerSL ℝ w) _ z := hc.smul hI
  rw [hev.fderiv_eq, h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  have he : innerSL ℝ e e = ‖e‖ ^ 2 := by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [show p - 2 - 2 = p - 4 by ring, he]
  ring

open Laplacian in
/-- **Subgoal** (Eq. (7) c_d, Newton step 5: the Newton kernel is harmonic): for `d ≥ 3` and
`z ≠ 0`, `Δ |z|^{2-d} = 0`. -/
theorem laplacian_newtonKernel {d : ℕ} (hd : 3 ≤ d) {z : Rd d} (hz : z ≠ 0) :
    Δ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) z = 0 := by
  set b := stdOrthonormalBasis ℝ (Rd d) with hbdef
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [fderiv_fderiv_norm_rpow_apply hz]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hs : ∑ i, ⟪z, b i⟫ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner z z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq, real_inner_comm (b i) z]
  simp only [hb, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [hs]
  have hpow : ‖z‖ ^ (2 - (d : ℝ) - 4) * ‖z‖ ^ 2 = ‖z‖ ^ (2 - (d : ℝ) - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hz0]
    congr 1
    push_cast
    ring
  rw [mul_assoc _ (‖z‖ ^ (2 - (d : ℝ) - 4)), hpow]
  ring

/-- **Subgoal** (Eq. (7) c_d, Newton step 6a: differentiation under the sphere integral): if
`K(·, ω)` has derivative `K'(·, ω)` on an open `U`, with `K` and `K'` jointly continuous on
`U × S^{d-1}`, then `y ↦ ∫ K(y, ω) dσ(ω)` has derivative `∫ K'(y, ω) dσ(ω)` on `U`. -/
theorem hasFDerivAt_integral_sphere {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set (Rd d)} (hU : IsOpen U)
    {K : Rd d → Metric.sphere (0 : Rd d) 1 → F}
    {K' : Rd d → Metric.sphere (0 : Rd d) 1 → (Rd d →L[ℝ] F)}
    (hK : ∀ ω, ∀ y ∈ U, HasFDerivAt (fun y => K y ω) (K' y ω) y)
    (hKc : ContinuousOn (Function.uncurry K) (U ×ˢ univ))
    (hK'c : ContinuousOn (Function.uncurry K') (U ×ˢ univ)) {y : Rd d} (hy : y ∈ U) :
    HasFDerivAt (fun y => ∫ ω, K y ω ∂(volume : Measure (Rd d)).toSphere)
      (∫ ω, K' y ω ∂(volume : Measure (Rd d)).toSphere) y := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  have hBU : Metric.closedBall y (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hcpt : IsCompact (Metric.closedBall y (ε / 2) ×ˢ (univ : Set (Metric.sphere (0 : Rd d) 1))) :=
    (isCompact_closedBall y _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hK'c.mono (prod_mono hBU subset_rfl))
  obtain ⟨C₀, hC₀⟩ := hcpt.exists_bound_of_continuousOn (hKc.mono (prod_mono hBU subset_rfl))
  have hcont : ∀ x ∈ U, Continuous (K x) := fun x hx =>
    hKc.comp_continuous (by fun_prop : Continuous fun ω : Metric.sphere (0 : Rd d) 1 => (x, ω))
      (fun ω => ⟨hx, trivial⟩)
  have hcont' : Continuous (K' y) :=
    hK'c.comp_continuous (by fun_prop : Continuous fun ω : Metric.sphere (0 : Rd d) 1 => (y, ω))
      (fun ω => ⟨hy, trivial⟩)
  have hB : Metric.closedBall y (ε / 2) ∈ 𝓝 y := Metric.closedBall_mem_nhds y (half_pos hε)
  have hyB : y ∈ Metric.closedBall y (ε / 2) := Metric.mem_closedBall_self (half_pos hε).le
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hB ?_ ?_
    hcont'.aestronglyMeasurable ?_ (integrable_const C) ?_
  · filter_upwards [hB] with x hx
    exact (hcont x (hBU hx)).aestronglyMeasurable
  · exact Integrable.of_bound (hcont y hy).aestronglyMeasurable C₀
      (Filter.Eventually.of_forall fun ω => hC₀ (y, ω) ⟨hyB, trivial⟩)
  · exact Filter.Eventually.of_forall fun ω x hx => hC (x, ω) ⟨hx, trivial⟩
  · exact Filter.Eventually.of_forall fun ω x hx => hK ω x (hBU hx)

/-- **Subgoal** (Eq. (7) c_d, Newton step 6b: continuity of the sphere integral): if `K` is
jointly continuous on `U × S^{d-1}` with `U` open, `y ↦ ∫ K(y, ω) dσ(ω)` is continuous on `U`. -/
theorem continuousOn_integral_sphere {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set (Rd d)} (hU : IsOpen U)
    {K : Rd d → Metric.sphere (0 : Rd d) 1 → F}
    (hKc : ContinuousOn (Function.uncurry K) (U ×ˢ univ)) :
    ContinuousOn (fun y => ∫ ω, K y ω ∂(volume : Measure (Rd d)).toSphere) U := by
  intro y hy
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  have hBU : Metric.closedBall y (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hcpt : IsCompact (Metric.closedBall y (ε / 2) ×ˢ (univ : Set (Metric.sphere (0 : Rd d) 1))) :=
    (isCompact_closedBall y _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hKc.mono (prod_mono hBU subset_rfl))
  have hcont : ∀ x ∈ U, Continuous (K x) := fun x hx =>
    hKc.comp_continuous (by fun_prop : Continuous fun ω : Metric.sphere (0 : Rd d) 1 => (x, ω))
      (fun ω => ⟨hx, trivial⟩)
  have hB : Metric.closedBall y (ε / 2) ∈ 𝓝 y := Metric.closedBall_mem_nhds y (half_pos hε)
  refine (continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C)
    ?_).continuousWithinAt
  · filter_upwards [hB] with x hx
    exact (hcont x (hBU hx)).aestronglyMeasurable
  · filter_upwards [hB] with x hx
    exact Filter.Eventually.of_forall fun ω => hC (x, ω) ⟨hx, trivial⟩
  · refine Filter.Eventually.of_forall fun ω => ?_
    have h1 : ContinuousAt (Function.uncurry K) (y, ω) :=
      hKc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, trivial⟩)
    have h2 : ContinuousAt (fun x : Rd d => (x, ω)) y := by fun_prop
    exact ContinuousAt.comp (g := Function.uncurry K) (f := fun x : Rd d => (x, ω)) h1 h2

/-- **Subgoal** (Eq. (7) c_d, Newton step 6c: second derivative of the shifted kernel): for
`y ≠ c`, `D²(|· - c|^p)(y)(e, e) = p(p-2)|y-c|^{p-4}⟨y-c,e⟩² + p|y-c|^{p-2}|e|²`. -/
theorem fderiv_fderiv_norm_sub_rpow_apply {d : ℕ} {y c : Rd d} (hy : y ≠ c) (p : ℝ)
    (e : Rd d) :
    fderiv ℝ (fderiv ℝ (fun x : Rd d => ‖x - c‖ ^ p)) y e e =
      p * (p - 2) * ‖y - c‖ ^ (p - 4) * ⟪y - c, e⟫ ^ 2 + p * ‖y - c‖ ^ (p - 2) * ‖e‖ ^ 2 := by
  have h1 : fderiv ℝ (fun x : Rd d => ‖x - c‖ ^ p) =
      fun x => fderiv ℝ (fun x : Rd d => ‖x‖ ^ p) (x - c) :=
    funext fun x => fderiv_comp_sub (f := fun x : Rd d => ‖x‖ ^ p) (x := x) c
  rw [h1, fderiv_comp_sub (f := fderiv ℝ fun x : Rd d => ‖x‖ ^ p) (x := y) c,
    fderiv_fderiv_norm_rpow_apply (sub_ne_zero.2 hy)]

/-- **Subgoal** (Eq. (7) c_d, Newton step 6d: the trace of 6c vanishes): for `d ≥ 3` and any
orthonormal basis `b`, `∑_i D²(|· - c|^{2-d})(y)(b_i, b_i) = 0` when `y ≠ c`. -/
theorem sum_fderiv_fderiv_newtonKernel_sub {d : ℕ} (hd : 3 ≤ d) {y c : Rd d} (hy : y ≠ c)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (Rd d)) :
    ∑ i, fderiv ℝ (fderiv ℝ (fun x : Rd d => ‖x - c‖ ^ (2 - (d : ℝ)))) y (b i) (b i) = 0 := by
  set z := y - c with hzdef
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  simp_rw [fderiv_fderiv_norm_sub_rpow_apply hy]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hs : ∑ i, ⟪z, b i⟫ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner z z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq, real_inner_comm (b i) z]
  have hcard : (Fintype.card ι : ℝ) = d := by
    rw [← Module.finrank_eq_card_basis b.toBasis, finrank_euclideanSpace_fin]
  simp only [hb, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  rw [hs]
  have hpow : ‖z‖ ^ (2 - (d : ℝ) - 4) * ‖z‖ ^ 2 = ‖z‖ ^ (2 - (d : ℝ) - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hz0]
    congr 1
    push_cast
    ring
  rw [mul_assoc _ (‖z‖ ^ (2 - (d : ℝ) - 4)), hpow]
  ring

/-- **Subgoal** (Eq. (7) c_d, Newton step 6e: smoothness of the power kernel): `z ↦ |z|^p` is
`C^n` on `ℝ^d ∖ {0}`. -/
theorem contDiffOn_norm_rpow {d : ℕ} {n : WithTop ℕ∞} (p : ℝ) :
    ContDiffOn ℝ n (fun z : Rd d => ‖z‖ ^ p) {z | z ≠ 0} := by
  intro z hz
  exact ((contDiffAt_norm ℝ hz).rpow_const_of_ne (norm_ne_zero_iff.2 hz)).contDiffWithinAt

/-- **Subgoal** (Eq. (7) c_d, Newton step 6f: kernel form of the sphere mean):
`sphereMean d r y = ∫ σ(S)⁻¹ |y - rω|^{2-d} dσ(ω)`. -/
theorem sphereMean_eq_integral (d : ℕ) (r : ℝ) :
    sphereMean d r = fun y : Rd d => ∫ ω, ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ * ‖y - r • (ω : Rd d)‖ ^ (2 - (d : ℝ)) ∂(volume : Measure (Rd d)).toSphere := by
  funext y
  rw [sphereMean, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [norm_sub_rev]

/-- **Subgoal** (Eq. (7) c_d, Newton step 6g: first derivative of the sphere mean): off the
sphere `|y| = r`, the sphere mean is differentiable with derivative the sphere integral of the
kernel derivative. -/
theorem hasFDerivAt_sphereMean {d : ℕ} {r : ℝ} (hr : 0 < r) {y : Rd d} (hy : ‖y‖ ≠ r) :
    HasFDerivAt (sphereMean d r)
      (∫ ω, ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ • fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (y - r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere) y := by
  have hU : IsOpen {y : Rd d | ‖y‖ ≠ r} := isOpen_ne_fun continuous_norm continuous_const
  have hV : IsOpen {z : Rd d | z ≠ 0} := isOpen_ne
  have hmaps : ∀ p ∈ {y : Rd d | ‖y‖ ≠ r} ×ˢ (univ : Set (Metric.sphere (0 : Rd d) 1)),
      p.1 - r • (p.2 : Rd d) ∈ {z : Rd d | z ≠ 0} := by
    rintro ⟨y, ω⟩ ⟨hy, -⟩
    simp only [Set.mem_setOf_eq, sub_ne_zero] at hy ⊢
    rintro rfl
    apply hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere ω, mul_one]
  have hg : Continuous fun p : Rd d × Metric.sphere (0 : Rd d) 1 => p.1 - r • (p.2 : Rd d) := by
    fun_prop
  have h2 := contDiffOn_norm_rpow (d := d) (n := 2) (2 - (d : ℝ))
  have h0 : ContinuousOn (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) {z : Rd d | z ≠ 0} := h2.continuousOn
  have h1 : ContinuousOn (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))) {z : Rd d | z ≠ 0} :=
    h2.continuousOn_fderiv_of_isOpen hV (by norm_num)
  rw [sphereMean_eq_integral]
  refine hasFDerivAt_integral_sphere (F := ℝ)
    (K := fun y ω => ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ *
      ‖y - r • (ω : Rd d)‖ ^ (2 - (d : ℝ)))
    (K' := fun y ω => ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ •
      fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (y - r • (ω : Rd d))) hU (fun ω x hx => ?_) ?_ ?_ hy
  · have hx0 : x - r • (ω : Rd d) ∈ {z : Rd d | z ≠ 0} := hmaps (x, ω) ⟨hx, trivial⟩
    have hd : DifferentiableAt ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (x - r • (ω : Rd d)) :=
      (h2.differentiableOn (by norm_num) _ hx0).differentiableAt (hV.mem_nhds hx0)
    have := (hd.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (r • (ω : Rd d)))).const_mul
      ((volume : Measure (Rd d)).toSphere.real univ)⁻¹
    simpa using this
  · exact (h0.comp hg.continuousOn hmaps).const_smul ((volume : Measure (Rd d)).toSphere.real univ)⁻¹
  · exact (h1.comp hg.continuousOn hmaps).const_smul ((volume : Measure (Rd d)).toSphere.real univ)⁻¹

/-- **Subgoal** (Eq. (7) c_d, Newton step 6h: second derivative of the sphere mean): off the
sphere, the derivative from 6g is differentiable with derivative the sphere integral of the
kernel Hessian. -/
theorem hasFDerivAt_fderiv_sphereMean {d : ℕ} {r : ℝ} (hr : 0 < r) {y : Rd d}
    (hy : ‖y‖ ≠ r) :
    HasFDerivAt (fun y : Rd d => ∫ ω, ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ • fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (y - r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere)
      (∫ ω, ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ • fderiv ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))) (y - r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere) y := by
  have hU : IsOpen {y : Rd d | ‖y‖ ≠ r} := isOpen_ne_fun continuous_norm continuous_const
  have hV : IsOpen {z : Rd d | z ≠ 0} := isOpen_ne
  have hmaps : ∀ p ∈ {y : Rd d | ‖y‖ ≠ r} ×ˢ (univ : Set (Metric.sphere (0 : Rd d) 1)),
      p.1 - r • (p.2 : Rd d) ∈ {z : Rd d | z ≠ 0} := by
    rintro ⟨y, ω⟩ ⟨hy, -⟩
    simp only [Set.mem_setOf_eq, sub_ne_zero] at hy ⊢
    rintro rfl
    apply hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere ω, mul_one]
  have hg : Continuous fun p : Rd d × Metric.sphere (0 : Rd d) 1 => p.1 - r • (p.2 : Rd d) := by
    fun_prop
  have h3 := contDiffOn_norm_rpow (d := d) (n := 2) (2 - (d : ℝ))
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))) {z : Rd d | z ≠ 0} :=
    h3.fderiv_of_isOpen hV (by norm_num)
  have h0 := h2.continuousOn
  have h1 : ContinuousOn (fderiv ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))))
      {z : Rd d | z ≠ 0} :=
    h2.continuousOn_fderiv_of_isOpen hV le_rfl
  refine hasFDerivAt_integral_sphere
      (K := fun y ω => ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ •
        fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))) (y - r • (ω : Rd d)))
      (K' := fun y ω => ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ •
        fderiv ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))) (y - r • (ω : Rd d)))
      hU (fun ω x hx => ?_) ?_ ?_ hy
  · have hx0 : x - r • (ω : Rd d) ∈ {z : Rd d | z ≠ 0} := hmaps (x, ω) ⟨hx, trivial⟩
    have hd : DifferentiableAt ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ))))
        (x - r • (ω : Rd d)) :=
      (h2.differentiableOn one_ne_zero _ hx0).differentiableAt (hV.mem_nhds hx0)
    have := (hd.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (r • (ω : Rd d)))).const_smul
      ((volume : Measure (Rd d)).toSphere.real univ)⁻¹
    convert this using 1 <;> first | rfl | simp
  · exact (h0.comp hg.continuousOn hmaps).const_smul ((volume : Measure (Rd d)).toSphere.real univ)⁻¹
  · exact (h1.comp hg.continuousOn hmaps).const_smul ((volume : Measure (Rd d)).toSphere.real univ)⁻¹

/-- **Subgoal** (Eq. (7) c_d, Newton step 6i: continuity of the second derivative): the sphere
integral of the kernel Hessian is continuous on `{|y| ≠ r}`. -/
theorem continuousOn_fderiv_fderiv_sphereMean {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun y : Rd d => ∫ ω, ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ • fderiv ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))) (y - r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere)
      {y | ‖y‖ ≠ r} := by
  have hU : IsOpen {y : Rd d | ‖y‖ ≠ r} := isOpen_ne_fun continuous_norm continuous_const
  have hV : IsOpen {z : Rd d | z ≠ 0} := isOpen_ne
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ (fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)))))
      {z : Rd d | z ≠ 0} :=
    (((contDiffOn_norm_rpow (n := 2) (2 - (d : ℝ))).fderiv_of_isOpen hV
      (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl)
  have hmaps : ∀ p ∈ {y : Rd d | ‖y‖ ≠ r} ×ˢ (univ : Set (Metric.sphere (0 : Rd d) 1)),
      p.1 - r • (p.2 : Rd d) ∈ {z : Rd d | z ≠ 0} := by
    rintro ⟨y, ω⟩ ⟨hy, -⟩
    simp only [Set.mem_setOf_eq, sub_ne_zero] at hy ⊢
    rintro rfl
    apply hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere ω, mul_one]
  refine continuousOn_integral_sphere hU ?_
  have hg : Continuous fun p : Rd d × Metric.sphere (0 : Rd d) 1 => p.1 - r • (p.2 : Rd d) := by
    fun_prop
  exact ((h2.comp hg.continuousOn hmaps).const_smul
    ((volume : Measure (Rd d)).toSphere.real univ)⁻¹)

/-- **Subgoal** (Eq. (7) c_d, Newton step 6j: continuous linear maps commute with the sphere
integral): for `φ : S^{d-1} → L(ℝ^d, F)` continuous and `L` continuous linear,
`L (∫ φ dσ) = ∫ L (φ ω) dσ(ω)`. -/
theorem clm_integral_sphere {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : (Rd d →L[ℝ] F) →L[ℝ] G) {φ : Metric.sphere (0 : Rd d) 1 → (Rd d →L[ℝ] F)}
    (hφ : Continuous φ) :
    L (∫ ω, φ ω ∂(volume : Measure (Rd d)).toSphere) =
      ∫ ω, L (φ ω) ∂(volume : Measure (Rd d)).toSphere := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Metric.sphere (0 : Rd d) 1)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hInt : Integrable φ (volume : Measure (Rd d)).toSphere :=
    Integrable.of_bound hφ.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => hC ω trivial)
  exact (L.integral_comp_comm hInt).symm

/-- **Subgoal** (Eq. (7) c_d, Newton step 6: the sphere mean is harmonic off the sphere): for
`d ≥ 3`, `r > 0` and `|y| ≠ r`, `sphereMean d r` is harmonic at `y`. -/
theorem harmonicAt_sphereMean {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) {y : Rd d}
    (hy : ‖y‖ ≠ r) : InnerProductSpace.HarmonicAt (sphereMean d r) y := by
  set S := ((volume : Measure (Rd d)).toSphere.real univ)⁻¹ with hS
  set N := fun z : Rd d => ‖z‖ ^ (2 - (d : ℝ)) with hN
  set U := {y : Rd d | ‖y‖ ≠ r} with hUdef
  have hU : IsOpen U := isOpen_ne_fun continuous_norm continuous_const
  have hV : IsOpen {z : Rd d | z ≠ 0} := isOpen_ne
  have hne : ∀ z ∈ U, ∀ ω : Metric.sphere (0 : Rd d) 1, z ≠ r • (ω : Rd d) := by
    intro z hz ω h
    apply hz
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere ω, mul_one]
  set G1 := fun y : Rd d => ∫ ω, S • fderiv ℝ N (y - r • (ω : Rd d))
    ∂(volume : Measure (Rd d)).toSphere with hG1
  set G2 := fun y : Rd d => ∫ ω, S • fderiv ℝ (fderiv ℝ N) (y - r • (ω : Rd d))
    ∂(volume : Measure (Rd d)).toSphere with hG2
  have hD1 : ∀ z ∈ U, fderiv ℝ (sphereMean d r) z = G1 z := fun z hz =>
    (hasFDerivAt_sphereMean hr hz).fderiv
  have hD2 : ∀ z ∈ U, fderiv ℝ G1 z = G2 z := fun z hz =>
    (hasFDerivAt_fderiv_sphereMean hr hz).fderiv
  have hcd : ContDiffOn ℝ 2 (sphereMean d r) U := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hasFDerivAt_sphereMean hr hz).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine ContDiffOn.congr ?_ hD1
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz =>
      (hasFDerivAt_fderiv_sphereMean hr hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_fderiv_fderiv_sphereMean hr).congr hD2
  refine ⟨hcd.contDiffAt (hU.mem_nhds hy), ?_⟩
  filter_upwards [hU.mem_nhds hy] with z hz
  set b := stdOrthonormalBasis ℝ (Rd d) with hbdef
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
  have hF : fderiv ℝ (fderiv ℝ (sphereMean d r)) z = G2 z := by
    rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) hD1)]
    exact hD2 z hz
  rw [hF]
  have h2 := contDiffOn_norm_rpow (d := d) (n := 2) (2 - (d : ℝ))
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ N)) {z : Rd d | z ≠ 0} :=
    (h2.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  have hmem : ∀ ω : Metric.sphere (0 : Rd d) 1, z - r • (ω : Rd d) ∈ {z : Rd d | z ≠ 0} :=
    fun ω => by simpa [sub_eq_zero] using hne z hz ω
  set T : (Rd d →L[ℝ] Rd d →L[ℝ] ℝ) →L[ℝ] ℝ := ∑ i, (ContinuousLinearMap.apply ℝ ℝ (b i)).comp
    (ContinuousLinearMap.apply ℝ (Rd d →L[ℝ] ℝ) (b i)) with hT
  have hTapp : ∀ Φ : Rd d →L[ℝ] Rd d →L[ℝ] ℝ, T Φ = ∑ i, Φ (b i) (b i) := fun Φ => by
    simp [hT]
  rw [← hTapp]
  show T (∫ ω, S • fderiv ℝ (fderiv ℝ N) (z - r • (ω : Rd d)) ∂(volume : Measure (Rd d)).toSphere) = 0
  rw [clm_integral_sphere T (φ := fun ω : Metric.sphere (0 : Rd d) 1 =>
    S • fderiv ℝ (fderiv ℝ N) (z - r • (ω : Rd d)))
    ((hH.comp_continuous (f := fun ω : Metric.sphere (0 : Rd d) 1 => z - r • (ω : Rd d))
      (by fun_prop) hmem).const_smul S)]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans (integral_zero _ _)
  have h6 := sum_fderiv_fderiv_newtonKernel_sub hd (hne z hz ω) b
  have hcomp : fderiv ℝ (fderiv ℝ (fun x : Rd d => ‖x - r • (ω : Rd d)‖ ^ (2 - (d : ℝ)))) z =
      fderiv ℝ (fderiv ℝ N) (z - r • (ω : Rd d)) := by
    have h1 : fderiv ℝ (fun x : Rd d => ‖x - r • (ω : Rd d)‖ ^ (2 - (d : ℝ))) =
        fun x => fderiv ℝ N (x - r • (ω : Rd d)) :=
      funext fun x => fderiv_comp_sub (f := N) (x := x) (r • (ω : Rd d))
    rw [h1, fderiv_comp_sub (f := fderiv ℝ N) (x := z) (r • (ω : Rd d))]
  rw [hcomp] at h6
  show T (S • fderiv ℝ (fderiv ℝ N) (z - r • (ω : Rd d))) = 0
  rw [hTapp]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, h6, mul_zero]

/-- **Subgoal** (Eq. (7) c_d, Newton step 7a: radial profile): a radial `u` on `ℝ^d`, `d > 0`,
satisfies `u y = u(|y| e₀)` with `e₀` the first unit vector. -/
theorem radial_eq_profile {d : ℕ} (hd : 0 < d) {u : Rd d → ℝ}
    (hrad : ∀ y y' : Rd d, ‖y‖ = ‖y'‖ → u y = u y') (y : Rd d) :
    u y = u (‖y‖ • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) := by
  apply hrad
  simp [norm_smul]

/-- **Subgoal** (Eq. (7) c_d, Newton step 7b: first derivative of a radial function): for
`x ≠ 0` and `f` differentiable at `|x|`, `D(f ∘ |·|)(x) = (f'(|x|)/|x|) ⟨x, ·⟩`. -/
theorem hasFDerivAt_comp_norm {d : ℕ} {f : ℝ → ℝ} {x : Rd d} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f ‖x‖) :
    HasFDerivAt (fun z : Rd d => f ‖z‖) ((deriv f ‖x‖ / ‖x‖) • innerSL ℝ x) x := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 7c: second derivative of a radial function): for
`y ≠ 0` and `f` `C²` at `|y|`, with `s = |y|`,
`D²(f ∘ |·|)(y)(e, e) = (f''(s) - f'(s)/s)/s² ⟨y,e⟩² + (f'(s)/s) |e|²`. -/
theorem fderiv_fderiv_comp_norm_apply {d : ℕ} {f : ℝ → ℝ} {y : Rd d} (hy : y ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖y‖) (e : Rd d) :
    fderiv ℝ (fderiv ℝ (fun z : Rd d => f ‖z‖)) y e e =
      (deriv (deriv f) ‖y‖ - deriv f ‖y‖ / ‖y‖) / ‖y‖ ^ 2 * ⟪y, e⟫ ^ 2 +
        deriv f ‖y‖ / ‖y‖ * ‖e‖ ^ 2 := by
  sorry

open Laplacian in
/-- **Subgoal** (Eq. (7) c_d, Newton step 7d: Laplacian of a radial function): for `y ≠ 0` and
`f` `C²` at `s = |y|`, `Δ(f ∘ |·|)(y) = f''(s) + (d-1)/s f'(s)`. -/
theorem laplacian_comp_norm {d : ℕ} {f : ℝ → ℝ} {y : Rd d} (hy : y ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖y‖) :
    Δ (fun z : Rd d => f ‖z‖) y =
      deriv (deriv f) ‖y‖ + ((d : ℝ) - 1) / ‖y‖ * deriv f ‖y‖ := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, Newton step 7e: the radial Laplace ODE): for `d ≥ 3` and
`r ≥ 0`, if `f'' + (d-1)/s f' = 0` on `(r, ∞)`, then `f = a + b s^{2-d}` there. -/
theorem radial_ode_eq {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 ≤ r) {f f' f'' : ℝ → ℝ}
    (hf : ∀ s, r < s → HasDerivAt f (f' s) s) (hf' : ∀ s, r < s → HasDerivAt f' (f'' s) s)
    (hode : ∀ s, r < s → f'' s + ((d : ℝ) - 1) / s * f' s = 0) :
    ∃ a b : ℝ, ∀ s, r < s → f s = a + b * s ^ (2 - (d : ℝ)) := by
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
  set e : Rd 1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ) with he
  have hmp : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
      (volume_preserving_funUnique (Fin 1) ℝ)
  have hnorm : ∀ x : Rd 1, ‖x‖ = |e x| := fun x => by
    simp [he, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have hsub : ∀ x : Rd 1, e (x - y) = e x - e y := fun x => by simp [he]
  have hball : e.symm ⁻¹' Metric.ball 0 R = Ioo (-R) R := by
    ext t
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hnorm,
      MeasurableEquiv.apply_symm_apply, Set.mem_Ioo, abs_lt]
  have h1 : (2 - ((1 : ℕ) : ℝ)) = 1 := by norm_num
  have hvol : volume (Metric.ball (0 : Rd 1) R) = volume (Ioo (-R) R) := by
    rw [← hball, hmp.symm.measure_preimage measurableSet_ball.nullMeasurableSet]
  have hint := hmp.symm.setIntegral_preimage_emb e.symm.measurableEmbedding
    (fun x : Rd 1 => ‖x - y‖ ^ (2 - ((1 : ℕ) : ℝ))) (Metric.ball 0 R)
  rw [← hint, hball, hvol, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), h1,
    Real.rpow_one]
  simp only [Real.rpow_one, hnorm, hsub, MeasurableEquiv.apply_symm_apply]
  rw [hnorm] at hy
  rcases (abs_eq hR.le).1 hy with hc | hc
  · rw [hc, setIntegral_congr_fun measurableSet_Ioo (g := fun t => R - t)
      (fun t ht => by rw [abs_of_nonpos (by linarith [ht.2])]; ring),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  · rw [hc, setIntegral_congr_fun measurableSet_Ioo (g := fun t => t + R)
      (fun t ht => by rw [sub_neg_eq_add, abs_of_nonneg (by linarith [ht.1])]),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring

/-- **Subgoal** (Eq. (7) c_d, Newton step 12: `d = 2`): the kernel is `1`. -/
theorem newton_ball_dim_two {R : ℝ} {y : Rd 2} :
    ∫ x in Metric.ball (0 : Rd 2) R, ‖x - y‖ ^ (2 - ((2 : ℕ) : ℝ)) =
      (volume (Metric.ball (0 : Rd 2) R)).toReal * R ^ (2 - ((2 : ℕ) : ℝ)) := by
  have h0 : (2 - ((2 : ℕ) : ℝ)) = 0 := by norm_num
  simp only [h0, Real.rpow_zero, mul_one]
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real_def]

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
