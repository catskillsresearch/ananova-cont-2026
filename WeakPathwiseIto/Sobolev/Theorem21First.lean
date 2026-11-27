/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.IsCubeOrBall
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakGradient
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Sobolev.Lemma22

/-! # Steps of the proof of Theorem 2.1, first estimate ([BH93], `m = 1`)

Following [BH93, §2]: the Poincaré-type bound (2) for `C¹` functions on a convex `Q`
([GT, Lemma 7.16], proved here by a homothety change of variables instead of polar
coordinates), its a.e. extension to `W^{1,1}` by mollification, and the passage to a Lebesgue
point by averaging over `Q ∩ B(x,r)` with [BH93, Lemma 2]. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_2_1_first

variable {d : ℕ}

/-- **Subgoal** (Theorem 2.1 proof, (2) for `C¹`, step 1: integrating along the segment):
`|f(y) - f(x)| ≤ ∫_0^1 |∇f(x + s(y - x))| |y - x| ds`. -/
theorem abs_sub_le_lintegral_segment {f : Rd d → ℝ} (hf : ContDiff ℝ 1 f) (x y : Rd d) :
    ENNReal.ofReal |f y - f x| ≤
      ∫⁻ s in Ioc (0 : ℝ) 1, ‖gradient f (x + s • (y - x))‖ₑ * ‖y - x‖ₑ := by
  set v := y - x
  have hcont : Continuous fun s : ℝ => fderiv ℝ f (x + s • v) v := by
    have h1 : Continuous fun s : ℝ => fderiv ℝ f (x + s • v) :=
      (hf.continuous_fderiv one_ne_zero).comp (continuous_const.add (continuous_id.smul continuous_const))
    exact h1.clm_apply continuous_const
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s := by
    intro s _
    have hl : HasDerivAt (fun s : ℝ => x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    exact ((hf.differentiable one_ne_zero) (x + s • v)).hasFDerivAt.comp_hasDerivAt s hl
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero, v, add_sub_cancel] at hftc
  rw [← Real.enorm_eq_ofReal_abs, ← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
  have hg : ‖gradient f (x + s • v)‖ = ‖fderiv ℝ f (x + s • v)‖ :=
    (InnerProductSpace.toDual ℝ (Rd d)).symm.norm_map _
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), hg]
  exact ENNReal.ofReal_le_ofReal ((fderiv ℝ f (x + s • v)).le_opNorm v)

/-- **Subgoal** (Theorem 2.1 proof, (2) for `C¹`, step 2: the homothety `y ↦ x + s(y - x)`):
for convex `Q ∋ x` with `|z - x| ≤ D` on `Q` and `0 < s ≤ 1`,
`∫_Q g(x + s(y-x)) |y-x| dy ≤ s^{-d-1} ∫_Q 1_{|z-x| ≤ sD} g(z) |z-x| dz`. -/
theorem lintegral_comp_homothety_le {Q : Set (Rd d)} (hQ : Convex ℝ Q) (hQm : MeasurableSet Q)
    {x : Rd d} (hx : x ∈ Q) {D : ℝ} (hD : ∀ z ∈ Q, dist z x ≤ D) {g : Rd d → ℝ≥0∞}
    (_hg : Measurable g) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ≤
      ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
        ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ) z := by
  have hs0 : 0 < s := hs.1
  set H : Rd d → ℝ≥0∞ := Q.indicator ({z | dist z x ≤ s * D}.indicator fun z => g z * ‖z - x‖ₑ)
    with hH
  have hinv : ENNReal.ofReal s⁻¹ * ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le), inv_mul_cancel₀ hs0.ne', ENNReal.ofReal_one]
  have step1 : ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal s⁻¹ * H (x + s • (y - x)) := by
    refine (lintegral_mono_ae ((ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy => ?_))).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hzQ : x + s • (y - x) ∈ Q := hQ.add_smul_sub_mem hx hy ⟨hs0.le, hs.2⟩
    have hzd : dist (x + s • (y - x)) x ≤ s * D := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hD y hy) hs0.le
    have hval : H (x + s • (y - x)) =
        g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ) := by
      rw [hH, indicator_of_mem hzQ, indicator_of_mem (show _ ∈ {z | dist z x ≤ s * D} from hzd),
        add_sub_cancel_left, enorm_smul, Real.enorm_of_nonneg hs0.le]
    rw [hval]
    refine le_of_eq ?_
    calc g (x + s • (y - x)) * ‖y - x‖ₑ
        = (ENNReal.ofReal s⁻¹ * ENNReal.ofReal s) * (g (x + s • (y - x)) * ‖y - x‖ₑ) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal s⁻¹ * (g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ)) := by ring
  have step4 : ∫⁻ w, H (x + s • w) =
      ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ u, H (x + u) := by
    have := lintegral_map_equiv (fun u => H (x + u)) (MeasurableEquiv.smul₀ s hs0.ne') (μ := volume)
    have hmap : Measure.map (MeasurableEquiv.smul₀ s hs0.ne' : Rd d ≃ᵐ Rd d) volume =
        ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) • volume :=
      Measure.map_addHaar_smul volume hs0.ne'
    rw [hmap, lintegral_smul_measure] at this
    exact this.symm
  calc ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal s⁻¹ * H (x + s • (y - x)) := step1
    _ = ENNReal.ofReal s⁻¹ * ∫⁻ w, H (x + s • w) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun w => H (x + s • w)) x]
    _ = ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ z, H z) := by
        rw [step4, lintegral_add_left_eq_self H x]
    _ = ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
          ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ) z := by
        rw [hH, lintegral_indicator hQm, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le)]
        congr 2
        rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 (pow_pos hs0 d)),
          Real.rpow_sub hs0, Real.rpow_one, Real.rpow_neg hs0.le, Real.rpow_natCast]
        field_simp

/-- **Subgoal** (Theorem 2.1 proof, (2) for `C¹`, step 3: the `s`-integral):
`∫_0^1 1_{r ≤ sD} s^{-d-1} ds ≤ D^d r^{-d} / d`. -/
theorem lintegral_Ioc_rpow_indicator_le (hd : 0 < d) {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    ∫⁻ s in Ioc (0 : ℝ) 1, {s : ℝ | r ≤ s * D}.indicator
        (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s ≤
      ENNReal.ofReal (D ^ d / d * r ^ (-(d : ℝ))) := by
  set a := r / D with ha_def
  have ha : 0 < a := div_pos hr hD
  have hset : {s : ℝ | r ≤ s * D} = Ici a := by
    ext s; simp [a, div_le_iff₀ hD]
  have hexp : -(d : ℝ) - 1 < -1 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  rw [hset, lintegral_indicator measurableSet_Ici]
  calc ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) ∂(volume.restrict (Ioc (0 : ℝ) 1))
      ≤ ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) :=
        lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
    _ = ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) :=
        (setLIntegral_congr Ioi_ae_eq_Ici).symm
    _ = ENNReal.ofReal (∫ s in Ioi a, s ^ (-(d : ℝ) - 1)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hexp ha)]
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact Real.rpow_nonneg (ha.trans hs).le _
    _ = ENNReal.ofReal (D ^ d / d * r ^ (-(d : ℝ))) := by
        rw [integral_Ioi_rpow_of_lt hexp ha]
        congr 1
        have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        have e1 : -(d : ℝ) - 1 + 1 = -(d : ℝ) := by ring
        rw [e1, ha_def, Real.div_rpow hr.le hD.le, Real.rpow_neg hD.le, Real.rpow_natCast]
        field_simp

/-- **Subgoal** (Theorem 2.1 proof, eq. (2) of [BH93] for `C¹`, [GT, Lemma 7.16]): for convex
bounded `Q` of positive measure and `x ∈ Q`,
`|f(x) - f_Q| ≤ (diam Q)^d / (d |Q|) ∫_Q |∇f(z)| / |x - z|^{d-1} dz`. -/
theorem poincare_of_contDiff (hd : 0 < d) {f : Rd d → ℝ} (hf : ContDiff ℝ 1 f) {Q : Set (Rd d)}
    (hQ : Convex ℝ Q) (hQm : MeasurableSet Q) (hQb : Bornology.IsBounded Q) (hQ0 : volume Q ≠ 0)
    {x : Rd d} (hx : x ∈ Q) :
    ENNReal.ofReal |f x - ⨍ y in Q, f y| ≤
      Metric.ediam Q ^ (d : ℝ) / (d * volume Q) *
        ∫⁻ z in Q, ‖gradient f z‖ₑ / edist x z ^ ((d : ℝ) - 1) := by
  set D := Metric.diam Q with hDdef
  have hD : ∀ z ∈ Q, dist z x ≤ D := fun z hz => Metric.dist_le_diam_of_mem hQb hz hx
  set g : Rd d → ℝ≥0∞ := fun z => ‖gradient f z‖ₑ with hgdef
  have hgc : Continuous fun z => gradient f z :=
    (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hgm : Measurable g := (continuous_enorm.comp hgc).measurable
  have hVt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hi : IntegrableOn f Q :=
    (hf.continuous.continuousOn.integrableOn_compact hQb.isCompact_closure).mono_set subset_closure
  set G : Rd d → ℝ≥0∞ := fun z => g z * ‖z - x‖ₑ with hGdef
  set C : ℝ≥0∞ := Metric.ediam Q ^ (d : ℝ) / d with hCdef
  -- Step A: average bound
  have stepA : ENNReal.ofReal |f x - ⨍ y in Q, f y| ≤
      (volume Q)⁻¹ * ∫⁻ y in Q, ENNReal.ofReal |f y - f x| := by
    have hreal : volume.real Q ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hQ0, hVt⟩
    have hint : IntegrableOn (fun y => f y - f x) Q := hi.sub (integrableOn_const hVt)
    have e : f x - ⨍ y in Q, f y = -((volume.real Q)⁻¹ * ∫ y in Q, (f y - f x)) := by
      rw [setAverage_eq, smul_eq_mul, integral_sub hi (integrableOn_const hVt), setIntegral_const,
        smul_eq_mul]
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg]
    calc ENNReal.ofReal ((volume.real Q)⁻¹ * |∫ y in Q, (f y - f x)|)
        ≤ ENNReal.ofReal ((volume.real Q)⁻¹ * ∫ y in Q, |f y - f x|) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
            (inv_nonneg.2 measureReal_nonneg))
      _ = (volume Q)⁻¹ * ∫⁻ y in Q, ENNReal.ofReal |f y - f x| := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg),
            ofReal_integral_eq_lintegral_ofReal hint.abs (Eventually.of_forall fun _ => abs_nonneg _),
            measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hQ0 hVt),
            ENNReal.ofReal_toReal hVt]
  -- Steps B–F: the double integral
  have hmeas1 : AEMeasurable (Function.uncurry fun (y : Rd d) (s : ℝ) =>
      g (x + s • (y - x)) * ‖y - x‖ₑ) ((volume.restrict Q).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : Rd d × ℝ => g (x + p.2 • (p.1 - x)) * ‖p.1 - x‖ₑ
    exact (hgm.comp (continuous_const.add (continuous_snd.smul
      (continuous_fst.sub continuous_const))).measurable).mul
      (continuous_enorm.comp (continuous_fst.sub continuous_const)).measurable
  set F : Rd d → ℝ → ℝ≥0∞ := fun z s =>
    G z * {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s
    with hFdef
  have hmeas2 : AEMeasurable (Function.uncurry F)
      ((volume.restrict Q).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    have hS : MeasurableSet {p : Rd d × ℝ | dist p.1 x ≤ p.2 * D} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h1 : Measurable fun p : Rd d × ℝ => G p.1 :=
      (hgm.mul (continuous_enorm.comp (continuous_id.sub continuous_const)).measurable).comp
        measurable_fst
    have h2 : Measurable fun p : Rd d × ℝ => ENNReal.ofReal (p.2 ^ (-(d : ℝ) - 1)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    exact h1.mul (h2.indicator hS)
  have hFeq : ∀ s z, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
      {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ) z = F z s := by
    intro s z
    by_cases h : dist z x ≤ s * D
    · rw [hFdef]; simp only [indicator_of_mem (show z ∈ {z | dist z x ≤ s * D} from h),
        indicator_of_mem (show s ∈ {s : ℝ | dist z x ≤ s * D} from h), hGdef]
      ring
    · rw [hFdef]; simp only [indicator_of_notMem (show z ∉ {z | dist z x ≤ s * D} from h),
        indicator_of_notMem (show s ∉ {s : ℝ | dist z x ≤ s * D} from h), mul_zero]
  have stepBF : ∫⁻ y in Q, ENNReal.ofReal |f y - f x| ≤
      ∫⁻ z in Q, G z * ∫⁻ s in Ioc (0 : ℝ) 1,
        {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s := by
    calc ∫⁻ y in Q, ENNReal.ofReal |f y - f x|
        ≤ ∫⁻ y in Q, ∫⁻ s in Ioc (0 : ℝ) 1, g (x + s • (y - x)) * ‖y - x‖ₑ :=
          lintegral_mono fun y => abs_sub_le_lintegral_segment hf x y
      _ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ :=
          lintegral_lintegral_swap hmeas1
      _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
            ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ) z :=
          setLIntegral_mono' measurableSet_Ioc fun s hs =>
            lintegral_comp_homothety_le hQ hQm hx hD hgm hs
      _ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ z in Q, F z s := by
          refine lintegral_congr fun s => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun z => hFeq s z
      _ = ∫⁻ z in Q, ∫⁻ s in Ioc (0 : ℝ) 1, F z s := (lintegral_lintegral_swap hmeas2).symm
      _ = _ := by
          refine lintegral_congr fun z => ?_
          rw [hFdef]
          exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
  -- Step G: the radial integral
  have hdiam : ENNReal.ofReal D = Metric.ediam Q := by
    rw [hDdef, Metric.diam, ENNReal.ofReal_toReal hQb.ediam_ne_top]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have stepG : ∀ z ∈ Q, G z * ∫⁻ s in Ioc (0 : ℝ) 1,
        {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s ≤
      C * (‖gradient f z‖ₑ / edist x z ^ ((d : ℝ) - 1)) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [hGdef]
    have hr : 0 < dist z x := dist_pos.2 hzx
    have hDpos : 0 < D := hr.trans_le (hD z hz)
    refine (mul_le_mul' le_rfl (lintegral_Ioc_rpow_indicator_le hd hDpos hr)).trans (le_of_eq ?_)
    set r := dist z x
    have h1 : ‖z - x‖ₑ = ENNReal.ofReal r := by rw [← ofReal_norm, ← dist_eq_norm]
    have h2 : edist x z ^ ((d : ℝ) - 1) = ENNReal.ofReal (r ^ ((d : ℝ) - 1)) := by
      rw [edist_dist, dist_comm, ENNReal.ofReal_rpow_of_pos hr]
    have h3 : C = ENNReal.ofReal (D ^ d / d) := by
      rw [hCdef, ← hdiam, ENNReal.ofReal_rpow_of_nonneg hDpos.le hdpos.le, Real.rpow_natCast,
        ENNReal.ofReal_div_of_pos hdpos, ENNReal.ofReal_natCast]
    simp only [hGdef, g]
    rw [h1, h2, h3]
    have hDd : 0 ≤ D ^ d / d := div_nonneg (pow_nonneg hDpos.le _) hdpos.le
    have eR : ENNReal.ofReal (D ^ d / d) * (‖gradient f z‖ₑ / ENNReal.ofReal (r ^ ((d : ℝ) - 1))) =
        ‖gradient f z‖ₑ * ENNReal.ofReal (D ^ d / d * (r ^ ((d : ℝ) - 1))⁻¹) := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _),
        ← mul_assoc, ← ENNReal.ofReal_mul hDd, mul_comm]
    rw [eR, mul_assoc, ← ENNReal.ofReal_mul hr.le]
    congr 2
    rw [Real.rpow_neg hr.le, Real.rpow_sub_one hr.ne']
    simp only [Real.rpow_natCast]
    field_simp
  -- Assemble
  calc ENNReal.ofReal |f x - ⨍ y in Q, f y|
      ≤ (volume Q)⁻¹ * ∫⁻ y in Q, ENNReal.ofReal |f y - f x| := stepA
    _ ≤ (volume Q)⁻¹ * ∫⁻ z in Q, C * (‖gradient f z‖ₑ / edist x z ^ ((d : ℝ) - 1)) :=
        mul_le_mul' le_rfl (stepBF.trans (setLIntegral_mono_ae' hQm
          (Eventually.of_forall fun z hz => stepG z hz)))
    _ = Metric.ediam Q ^ (d : ℝ) / (d * volume Q) *
          ∫⁻ z in Q, ‖gradient f z‖ₑ / edist x z ^ ((d : ℝ) - 1) := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_lt_top
          (ENNReal.rpow_ne_top_of_nonneg hdpos.le hQb.ediam_ne_top)
          (by exact_mod_cast hd.ne')).ne, ← mul_assoc]
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (by exact_mod_cast hd.ne'))
          (Or.inl (ENNReal.natCast_ne_top d))]
        ring

/-- **Subgoal** (Theorem 2.1 proof: ball sandwich for cubes and balls): a cube or ball `Q` is
convex and measurable, and `B(c, ρ) ⊆ Q ⊆ B̄(c, d ρ)` for some centre `c` and `ρ > 0`. -/
theorem ball_subset_subset (hd : 0 < d) {Q : Set (Rd d)} (hQ : IsCubeOrBall Q) :
    ∃ (c : Rd d) (ρ : ℝ), 0 < ρ ∧ Convex ℝ Q ∧ MeasurableSet Q ∧
      Metric.ball c ρ ⊆ Q ∧ Q ⊆ Metric.closedBall c (d * ρ) := by
  have hcoord : ∀ (i : Fin d) (v : Rd d), Rd.coord i v = v i := by
    intro i v; simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hco : ∀ (i : Fin d) (v : Rd d), |Rd.coord i v| ≤ ‖v‖ := by
    intro i v; rw [hcoord, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le v i
  have hnorm : ∀ (v : Rd d) {r : ℝ}, 0 < r → (∀ i, |Rd.coord i v| ≤ r) → ‖v‖ ≤ d * r := by
    intro v r hr h
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := h i
          rw [hcoord, ← Real.norm_eq_abs] at this
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = d * r ^ 2 := by simp
      _ ≤ (d * r) ^ 2 := by nlinarith [sq_nonneg r]
  have hcc : ∀ (c : Rd d) (i : Fin d), Continuous fun y : Rd d => |Rd.coord i (y - c)| := by
    intro c i; unfold Rd.coord; fun_prop
  have hlin : ∀ (c y z : Rd d) (a b : ℝ), a + b = 1 → ∀ i,
      Rd.coord i (a • y + b • z - c) = a * Rd.coord i (y - c) + b * Rd.coord i (z - c) := by
    intro c y z a b hab i
    simp only [hcoord, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (c i) * hab
  -- Per-shape facts: convex, measurable, ball c r ⊆ Q ⊆ closedBall c (d * r).
  have shape : ∀ Q : Set (Rd d), IsCubeOrBall Q → ∃ (c : Rd d) (r : ℝ), 0 < r ∧
      Convex ℝ Q ∧ MeasurableSet Q ∧ Metric.ball c r ⊆ Q ∧ Q ⊆ Metric.closedBall c (d * r) := by
    rintro Q ⟨c, r, hr, hQ | hQ | hQ | hQ⟩ <;> refine ⟨c, r, hr, ?_⟩ <;> subst hQ
    · refine ⟨convex_ball c r, measurableSet_ball, subset_rfl,
        Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)⟩
      nlinarith
    · refine ⟨convex_closedBall c r, measurableSet_closedBall, Metric.ball_subset_closedBall,
        Metric.closedBall_subset_closedBall ?_⟩
      nlinarith
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro y hy z hz a b ha hb hab i
        rw [hlin c y z a b hab i]
        have h1 := hy i; have h2 := hz i
        calc |a * Rd.coord i (y - c) + b * Rd.coord i (z - c)|
            ≤ a * |Rd.coord i (y - c)| + b * |Rd.coord i (z - c)| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
          _ < r := by
              rcases ha.lt_or_eq with ha' | ha'
              · nlinarith [abs_nonneg (Rd.coord i (z - c))]
              · subst ha'; simp at hab; subst hab; simpa using h2
      · have : IsCubeOrBall.openCube c r = ⋂ i, {y | |Rd.coord i (y - c)| < r} := by
          ext; simp [IsCubeOrBall.openCube]
        rw [this]
        exact MeasurableSet.iInter fun i => measurableSet_lt (hcc c i).measurable measurable_const
      · intro y hy i
        exact (hco i _).trans_lt (by simpa [dist_eq_norm] using hy)
      · intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact hnorm _ hr fun i => (hy i).le
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro y hy z hz a b ha hb hab i
        rw [hlin c y z a b hab i]
        have h1 := hy i; have h2 := hz i
        calc |a * Rd.coord i (y - c) + b * Rd.coord i (z - c)|
            ≤ a * |Rd.coord i (y - c)| + b * |Rd.coord i (z - c)| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
          _ ≤ r := by nlinarith [abs_nonneg (Rd.coord i (z - c))]
      · have : IsCubeOrBall.closedCube c r = ⋂ i, {y | |Rd.coord i (y - c)| ≤ r} := by
          ext; simp [IsCubeOrBall.closedCube]
        rw [this]
        exact MeasurableSet.iInter fun i => measurableSet_le (hcc c i).measurable measurable_const
      · intro y hy i
        exact (hco i _).trans (by simpa [dist_eq_norm] using (Metric.mem_ball.1 hy).le)
      · intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact hnorm _ hr hy
  exact shape Q hQ

/-- **Subgoal** (Theorem 2.1 proof: cubes and balls): a cube or ball is convex, measurable,
bounded, of positive measure, and `(diam Q)^d ≤ K_d |Q|`. -/
theorem isCubeOrBall_props (hd : 0 < d) : ∃ K : ℝ≥0, ∀ Q : Set (Rd d), IsCubeOrBall Q →
    Convex ℝ Q ∧ MeasurableSet Q ∧ Bornology.IsBounded Q ∧ volume Q ≠ 0 ∧
      Metric.ediam Q ^ (d : ℝ) ≤ K * volume Q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have shape : ∀ Q : Set (Rd d), IsCubeOrBall Q → ∃ (c : Rd d) (r : ℝ), 0 < r ∧
      Convex ℝ Q ∧ MeasurableSet Q ∧ Metric.ball c r ⊆ Q ∧ Q ⊆ Metric.closedBall c (d * r) :=
    fun Q hQ => ball_subset_subset hd hQ
  -- The constant.
  set B := volume (Metric.ball (0 : Rd d) 1) with hBdef
  have hB0 : B ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨((2 * d : ℝ≥0) ^ d) / B.toNNReal, fun Q hQ => ?_⟩
  obtain ⟨c, r, hr, hcv, hm, hin, hout⟩ := shape Q hQ
  have hb : Bornology.IsBounded Q := Metric.isBounded_closedBall.subset hout
  have hball : volume (Metric.ball c r) = ENNReal.ofReal (r ^ d) * B := by
    rw [Measure.addHaar_ball_of_pos volume c hr, finrank_euclideanSpace_fin]
  refine ⟨hcv, hm, hb, ?_, ?_⟩
  · refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hin))
    exact Metric.measure_ball_pos volume c hr
  · have hdiam : Metric.diam Q ≤ 2 * (d * r) :=
      (Metric.diam_mono hout Metric.isBounded_closedBall).trans
        (Metric.diam_closedBall (by positivity))
    have hed : Metric.ediam Q = ENNReal.ofReal (Metric.diam Q) := by
      rw [Metric.diam, ENNReal.ofReal_toReal hb.ediam_ne_top]
    calc Metric.ediam Q ^ (d : ℝ)
        ≤ ENNReal.ofReal (2 * (d * r)) ^ (d : ℝ) := by
          rw [hed]; exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdiam) hdpos.le
      _ = ((2 * d : ℝ≥0) ^ d : ℝ≥0∞) * ENNReal.ofReal (r ^ d) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hdpos.le, Real.rpow_natCast,
            ← mul_assoc, mul_pow, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [← ENNReal.ofReal_coe_nnreal]
          push_cast
          exact ENNReal.ofReal_pow (by positivity) _
      _ = (((2 * d : ℝ≥0) ^ d / B.toNNReal : ℝ≥0) : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * B) := by
          rw [ENNReal.coe_div (ENNReal.toNNReal_ne_zero.2 ⟨hB0, hBt⟩), ENNReal.coe_toNNReal hBt,
            mul_comm (ENNReal.ofReal (r ^ d)) B, ← mul_assoc, ENNReal.div_mul_cancel hB0 hBt]
          push_cast; rfl
      _ ≤ _ := by rw [← hball]; exact mul_le_mul' le_rfl (measure_mono hin)

/-- **Subgoal** (Theorem 2.1 proof, mollification step 1, first-order test derivative):
`D^{e_i} φ = ∂_i φ`. -/
theorem testDeriv_single (φ : Rd d → ℝ) (i : Fin d) (x : Rd d) :
    IsWeakDerivative.testDeriv (Pi.single i 1) φ x = fderiv ℝ φ x (Rd.basisVec i) := by
  classical
  set f : Fin d → List (Rd d) := fun k => List.replicate ((Pi.single i 1 : Fin d → ℕ) k)
    (Rd.basisVec k) with hf
  set P : Fin d → Bool := fun k => decide (k = i) with hP
  have hfl : ∀ L : List (Fin d), L.flatMap f = (L.filter P).flatMap f := by
    intro L
    induction L with
    | nil => rfl
    | cons k L ih =>
      by_cases hk : k = i
      · have : P k = true := by simp [hP, hk]
        rw [List.filter_cons_of_pos this, List.flatMap_cons, List.flatMap_cons, ih]
      · have : P k = false := by simpa [hP] using hk
        have h0 : f k = [] := by simp [hf, Pi.single_apply, hk]
        rw [List.filter_cons_of_neg (by simp [this]), List.flatMap_cons, h0, List.nil_append, ih]
  have hsorted : ((List.finRange d).filter P).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange d).filter _
  have hfilt : (List.finRange d).filter P = [i] := by
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hsorted.imp le_of_lt) (by simp)
    rw [List.perm_ext_iff_of_nodup (hsorted.imp ne_of_lt) (by simp)]
    intro a
    simp [hP, List.mem_filter]
  have hdir : IsWeakDerivative.directions (Pi.single i 1 : Fin d → ℕ) = [Rd.basisVec i] := by
    have : IsWeakDerivative.directions (Pi.single i 1 : Fin d → ℕ) =
        (List.finRange d).flatMap f := rfl
    rw [this, hfl, hfilt]
    simp [hf]
  have key : ∀ (a : Rd d) (l : List (Rd d)), l = [a] →
      iteratedFDeriv ℝ l.length φ x (fun k => l.get k) = fderiv ℝ φ x a := by
    rintro a l rfl
    exact iteratedFDeriv_one_apply _
  exact key _ _ hdir

/-- **Subgoal** (Theorem 2.1 proof, mollification step 1): for `f` with weak gradient `G` and a
smooth compactly supported `ψ`, `f * ψ` is `C¹` with `∇(f * ψ) = G * ψ`. -/
theorem contDiff_convolution {f : Rd d → ℝ} {G : Rd d → Rd d} (hG : IsWeakGradient f G)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiff ℝ 1 (fun x => ∫ y, f y * ψ (x - y)) ∧
      ∀ x, gradient (fun x => ∫ y, f y * ψ (x - y)) x =
        ∑ i, (∫ y, Rd.coord i (G y) * ψ (x - y)) • Rd.basisVec i := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hsub : ∀ u v : Rd 0, u = v := fun u v => Subsingleton.elim u v
    refine ⟨?_, fun x => hsub _ _⟩
    have : (fun x => ∫ y, f y * ψ (x - y)) = fun _ => ∫ y, f y * ψ (0 - y) := by
      funext x; rw [hsub x 0]
    rw [this]; exact contDiff_const
  have hfl : LocallyIntegrable f := (hG ⟨0, hd⟩).1
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  set F := fun x => ∫ y, f y * ψ (x - y) with hFdef
  have hFeq : F = convolution f ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x; simp [hFdef, convolution_def, smul_eq_mul]
  refine ⟨?_, fun x => ?_⟩
  · rw [hFeq]
    exact hψc.contDiff_convolution_right (n := 1) (L := ContinuousLinearMap.lsmul ℝ ℝ) hfl hψ1
  -- the partial derivatives
  have hpart : ∀ i, fderiv ℝ F x (Rd.basisVec i) = ∫ y, Rd.coord i (G y) * ψ (x - y) := by
    intro i
    have hD := hψc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hfl hψ1 x
    rw [← hFeq] at hD
    rw [hD.fderiv, convolution_precompR_apply (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ) hfl
      (hψc.fderiv (𝕜 := ℝ)) (hψ1.continuous_fderiv one_ne_zero)]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    -- weak derivative against `φ y = ψ (x - y)`
    set φ : Rd d → ℝ := fun y => ψ (x - y) with hφdef
    have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := hψ.comp (contDiff_const.sub contDiff_id)
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph (Homeomorph.subLeft x)
    have hφd : ∀ y, fderiv ℝ φ y (Rd.basisVec i) = -fderiv ℝ ψ (x - y) (Rd.basisVec i) := by
      intro y
      have h1 : HasFDerivAt (fun y : Rd d => x - y) (-ContinuousLinearMap.id ℝ (Rd d)) y :=
        (hasFDerivAt_id y).const_sub x
      have h2 : HasFDerivAt φ ((fderiv ℝ ψ (x - y)).comp (-ContinuousLinearMap.id ℝ (Rd d))) y :=
        ((hψ1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y h1
      rw [h2.fderiv]
      simp
    have hw := (hG i).2.2 φ hφs hφc
    simp only [testDeriv_single, hφd, IsWeakDerivative.order] at hw
    have hord : ∑ k, (Pi.single i 1 : Fin d → ℕ) k = 1 := by simp
    rw [hord, pow_one] at hw
    have : ∫ y, f y * -fderiv ℝ ψ (x - y) (Rd.basisVec i) =
        -∫ y, f y * fderiv ℝ ψ (x - y) (Rd.basisVec i) := by
      rw [← integral_neg]; simp [mul_neg]
    rw [this] at hw
    linarith
  -- assemble via the orthonormal basis
  have hexp := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (gradient F x)
  rw [← hexp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : (EuclideanSpace.basisFun (Fin d) ℝ) i = Rd.basisVec i := by
    simp [Rd.basisVec]
  rw [hb, ← hpart i, real_inner_comm]
  congr 1
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- **Subgoal** (Theorem 2.1 proof, mollification step 2: Young's inequality in `L¹`):
`‖h * ψ‖_1 ≤ ‖h‖_1 ‖ψ‖_1`. -/
theorem lintegral_convolution_le {h ψ : Rd d → ℝ} (hh : Integrable h) (hψ : Integrable ψ) :
    ∫⁻ x, ‖∫ y, h y * ψ (x - y)‖ₑ ≤ (∫⁻ y, ‖h y‖ₑ) * ∫⁻ y, ‖ψ y‖ₑ := by
  have hm : AEMeasurable (Function.uncurry fun (x y : Rd d) => ‖h y‖ₑ * ‖ψ (x - y)‖ₑ)
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖h p.2‖ₑ) (volume.prod volume) :=
      hh.aemeasurable.enorm.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd)
    have h2 : AEMeasurable (fun p : Rd d × Rd d => ‖ψ (p.1 - p.2)‖ₑ) (volume.prod volume) :=
      hψ.aemeasurable.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub volume volume)
    exact h1.mul h2
  calc ∫⁻ x, ‖∫ y, h y * ψ (x - y)‖ₑ
      ≤ ∫⁻ x, ∫⁻ y, ‖h y‖ₑ * ‖ψ (x - y)‖ₑ := lintegral_mono fun x =>
        (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => enorm_mul _ _))
    _ = ∫⁻ y, ∫⁻ x, ‖h y‖ₑ * ‖ψ (x - y)‖ₑ := lintegral_lintegral_swap hm
    _ = ∫⁻ y, ‖h y‖ₑ * ∫⁻ z, ‖ψ z‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          lintegral_sub_right_eq_self (fun z => ‖ψ z‖ₑ) y]
    _ = (∫⁻ y, ‖h y‖ₑ) * ∫⁻ y, ‖ψ y‖ₑ := lintegral_mul_const' _ _ hψ.2.ne

/-- **Subgoal** (Theorem 2.1 proof, mollification step 3: continuous compactly supported case):
for an approximate identity `ψ_n` (nonnegative, continuous, mass `1`, supported in
`B(0, 1/(n+1))`), `h * ψ_n → h` in `L¹` when `h` is continuous with compact support. -/
theorem tendsto_convolution_of_hasCompactSupport {h : Rd d → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (_hψc : ∀ n, Continuous (ψ n)) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ) atTop (𝓝 0) := by
  -- rewrite the convolution with `ψ` on the left
  have hconv : ∀ n x, ∫ y, h y * ψ n (x - y) =
      convolution (ψ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro n x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self (fun t => ψ n t * h (x - t)) volume x]
    simp [mul_comm]
  have hR : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hR1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  set M := Metric.cthickening 1 (tsupport h) with hM
  have hMc : IsCompact M := hhc.isCompact.cthickening
  have hMt : volume M ≠ ⊤ := hMc.measure_lt_top.ne
  have hmeas : AEStronglyMeasurable h volume := hh.aestronglyMeasurable
  -- uniform bound
  have hbound : ∀ (n : ℕ) (η : ℝ), 0 ≤ η →
      (∀ a b : Rd d, dist a b < 1 / ((n : ℝ) + 1) → dist (h a) (h b) ≤ η) →
      ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ ≤ ENNReal.ofReal η * volume M := by
    intro n η hη hδ
    rw [← lintegral_indicator_const hMc.isClosed.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [hconv]
    by_cases hx : x ∈ M
    · rw [indicator_of_mem hx, ← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal (dist_convolution_le hη (hψs n) (hψ0 n) (hψ1 n) hmeas ?_)
      intro y hy
      exact hδ y x (Metric.mem_ball.1 hy)
    · rw [indicator_of_notMem hx]
      have hz : ∀ y ∈ Metric.ball x (1 / ((n : ℝ) + 1)), h y = 0 := by
        intro y hy
        by_contra hne
        exact hx (Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hne)
          (by rw [dist_comm]; exact (Metric.mem_ball.1 hy).le.trans (hR1 n)))
      have h0 := dist_convolution_le (μ := volume) (z₀ := (0 : ℝ)) le_rfl (hψs n) (hψ0 n) (hψ1 n)
        hmeas (fun y hy => by rw [hz y hy, dist_self])
      have hx0 : h x = 0 := hz x (Metric.mem_ball_self (hR n))
      rw [dist_le_zero] at h0
      rw [h0, hx0, sub_zero, enorm_zero]
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  -- choose η with ofReal η * vol M < ε
  have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal η * volume M) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => ENNReal.ofReal η * volume M) (𝓝 0) (𝓝 (ENNReal.ofReal 0 * volume M)) :=
      ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hMt)
    rw [ENNReal.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨η, hηε, hη0⟩ := ((hlim.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  replace hη0 : 0 < η := hη0
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
    (hhc.uniformContinuous_of_continuous hh) η hη0
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ0
  refine ⟨N, fun n hn => (hbound n η (le_of_lt hη0) fun a b hab => (hδ ?_).le).trans hηε.le⟩
  refine hab.trans_le ((one_div_le_one_div_of_le (by positivity) ?_).trans hN.le)
  exact_mod_cast Nat.add_le_add_right hn 1

/-- **Subgoal** (Theorem 2.1 proof, mollification step 4): for `h ∈ L¹` and an approximate
identity `ψ_n` as above, `h * ψ_n → h` in `L¹`. -/
theorem tendsto_convolution {h : Rd d → ℝ} (hh : Integrable h) {ψ : ℕ → Rd d → ℝ}
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψc : ∀ n, Continuous (ψ n)) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ) atTop (𝓝 0) := by
  have hψcs : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (isCompact_closedBall (0 : Rd d) (1 / ((n : ℝ) + 1))).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hψint : ∀ n, Integrable (ψ n) := fun n => integrable_of_integral_eq_one (hψ1 n)
  have hψL : ∀ n, ∫⁻ y, ‖ψ n y‖ₑ = 1 := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hψint n)]
    simp_rw [Real.norm_of_nonneg (hψ0 n _)]
    rw [hψ1 n, ENNReal.ofReal_one]
  -- integrability of `y ↦ k y * ψ n (x - y)` for integrable `k`
  have hint : ∀ {k : Rd d → ℝ}, Integrable k → ∀ n x, Integrable fun y => k y * ψ n (x - y) := by
    intro k hk n x
    obtain ⟨C, hC⟩ := (hψc n).bounded_above_of_compact_support (hψcs n)
    exact hk.mul_bdd ((hψc n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => hC _)
  rw [ENNReal.tendsto_atTop_zero]
  intro ε' hε'
  obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε'
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · rw [← h, ENNReal.ofReal_zero] at hr; exact absurd hr (lt_irrefl _)
  set ε : ℝ := r / 3 with hεdef
  have hε0 : 0 < ε := by positivity
  obtain ⟨g, hgc, hgL, hgcont, hgm⟩ := (memLp_one_iff_integrable.2 hh).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.one_ne_top (ENNReal.ofReal_pos.2 hε0).ne'
  have hgi : Integrable g := memLp_one_iff_integrable.1 hgm
  rw [eLpNorm_one_eq_lintegral_enorm (hh.sub hgi).aestronglyMeasurable] at hgL
  have hT := tendsto_convolution_of_hasCompactSupport hgcont hgc hψ0 hψc hψ1 hψs
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 hT) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε0)
  refine ⟨N, fun n hn => ?_⟩
  have hgconvc : Continuous fun x => ∫ y, g y * ψ n (x - y) := by
    have : (fun x => ∫ y, g y * ψ n (x - y)) =
        convolution g (ψ n) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext x; simp [convolution_def, smul_eq_mul]
    rw [this]
    exact hgc.continuous_convolution_left _ hgcont (hψint n).locallyIntegrable
  have hpt : ∀ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ ≤
      (‖∫ y, (h - g) y * ψ n (x - y)‖ₑ + ‖(∫ y, g y * ψ n (x - y)) - g x‖ₑ) + ‖(g - h) x‖ₑ := by
    intro x
    have e : (∫ y, h y * ψ n (x - y)) - h x =
        (∫ y, (h - g) y * ψ n (x - y)) + ((∫ y, g y * ψ n (x - y)) - g x) + (g - h) x := by
      have : ∫ y, (h - g) y * ψ n (x - y) = (∫ y, h y * ψ n (x - y)) - ∫ y, g y * ψ n (x - y) := by
        rw [← integral_sub (hint hh n x) (hint hgi n x)]
        congr 1; funext y; simp [sub_mul]
      rw [this]; simp only [Pi.sub_apply]; ring
    rw [e]
    exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
  have hmeas3 : AEMeasurable (fun x => ‖(g - h) x‖ₑ) volume :=
    (hgi.sub hh).aemeasurable.enorm
  have hmeas2 : AEMeasurable (fun x => ‖(∫ y, g y * ψ n (x - y)) - g x‖ₑ) volume :=
    ((hgconvc.sub hgcont).enorm).measurable.aemeasurable
  calc ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ
      ≤ ∫⁻ x, (‖∫ y, (h - g) y * ψ n (x - y)‖ₑ + ‖(∫ y, g y * ψ n (x - y)) - g x‖ₑ) +
          ‖(g - h) x‖ₑ := lintegral_mono hpt
    _ = (∫⁻ x, ‖∫ y, (h - g) y * ψ n (x - y)‖ₑ) + (∫⁻ x, ‖(∫ y, g y * ψ n (x - y)) - g x‖ₑ) +
          ∫⁻ x, ‖(g - h) x‖ₑ := by
        rw [lintegral_add_right' _ hmeas3, lintegral_add_right' _ hmeas2]
    _ ≤ ENNReal.ofReal ε * 1 + ENNReal.ofReal ε + ENNReal.ofReal ε := by
        refine add_le_add (add_le_add ?_ (hN n hn)) ?_
        · rw [← hψL n]
          exact (lintegral_convolution_le (hh.sub hgi) (hψint n)).trans (mul_le_mul' hgL le_rfl)
        · calc ∫⁻ x, ‖(g - h) x‖ₑ = ∫⁻ x, ‖(h - g) x‖ₑ := by
                congr 1; funext x; rw [← enorm_neg]; simp
            _ ≤ _ := hgL
    _ = ENNReal.ofReal r := by
        rw [mul_one, ← ENNReal.ofReal_add hε0.le hε0.le, ← ENNReal.ofReal_add (by positivity) hε0.le]
        congr 1; rw [hεdef]; ring
    _ ≤ ε' := hrε.le

/-- **Subgoal** (Theorem 2.1 proof: the Riesz potential `I¹_Q` is bounded on `L¹(Q)`):
`∫_Q ∫_Q |h(z)| / |y - z|^{d-1} dz dy ≤ C_Q ∫_Q |h|` for bounded `Q`. -/
theorem lintegral_potential_le (_hd : 0 < d) {Q : Set (Rd d)} (hQb : Bornology.IsBounded Q)
    (hQm : MeasurableSet Q) :
    ∃ C : ℝ≥0, ∀ h : Rd d → ℝ, AEStronglyMeasurable h →
      ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1) ≤ C * ∫⁻ z in Q, ‖h z‖ₑ := by
  obtain ⟨C0, -, hC0⟩ := lemma_2_2 d (α := 1) one_pos
  set D : ℝ := Metric.diam Q + 1 with hDdef
  have hD : 0 < D := by positivity
  refine ⟨C0 * (2 * D).toNNReal, fun h hh => ?_⟩
  set C : ℝ≥0∞ := ((C0 * (2 * D).toNNReal : ℝ≥0) : ℝ≥0∞) with hCdef
  -- the kernel integral is uniformly bounded on `Q`
  have hK : ∀ z ∈ Q, ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 1) ≤ C := by
    intro z hz
    have hsub : Q ⊆ Metric.closedBall z D := fun y hy => by
      rw [Metric.mem_closedBall]
      exact (Metric.dist_le_diam_of_mem hQb hy hz).trans (by linarith)
    have hball : IsCubeOrBall (Metric.closedBall z D) := ⟨z, D, hD, Or.inr (Or.inl rfl)⟩
    have hlem := hC0 (Metric.closedBall z D) (fun _ => (1 : ℝ)) hball
      (integrableOn_const measure_closedBall_lt_top.ne) z (Metric.mem_closedBall_self hD.le)
    have hM : localMaximalFunction (Metric.ediam (Metric.closedBall z D)) (fun _ : Rd d => (1 : ℝ)) z
        ≤ 1 := by
      refine iSup_le fun r => iSup_le fun _ => iSup_le fun _ => ?_
      rw [laverage_eq]
      simp only [enorm_one, lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact ENNReal.div_self_le_one
    have hdiam : Metric.ediam (Metric.closedBall z D) ≤ ENNReal.ofReal (2 * D) := by
      rw [← ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top]
      exact ENNReal.ofReal_le_ofReal (Metric.diam_closedBall hD.le)
    calc ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 1)
        ≤ ∫⁻ y in Metric.closedBall z D, 1 / edist y z ^ ((d : ℝ) - 1) := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.closedBall z D, ‖(fun _ : Rd d => (1 : ℝ)) y‖ₑ / edist z y ^ ((d : ℝ) - 1) := by
          simp only [enorm_one, edist_comm]
      _ ≤ C0 * Metric.ediam (Metric.closedBall z D) ^ (1 : ℝ) *
            localMaximalFunction (Metric.ediam (Metric.closedBall z D)) (fun _ => (1 : ℝ)) z := hlem
      _ ≤ C0 * ENNReal.ofReal (2 * D) * 1 := by
          rw [ENNReal.rpow_one]; gcongr
      _ = C := by
          rw [mul_one, hCdef, ENNReal.coe_mul, ENNReal.ofReal]
  have hm : AEMeasurable (Function.uncurry fun (y z : Rd d) => ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1))
      ((volume.restrict Q).prod (volume.restrict Q)) := by
    have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖h p.2‖ₑ)
        ((volume.restrict Q).prod (volume.restrict Q)) :=
      hh.restrict.aemeasurable.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable fun p : Rd d × Rd d => edist p.1 p.2 ^ ((d : ℝ) - 1) :=
      (continuous_edist.measurable).pow_const _
    exact h1.div h2.aemeasurable
  calc ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1)
      = ∫⁻ z in Q, ∫⁻ y in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1) := lintegral_lintegral_swap hm
    _ = ∫⁻ z in Q, ‖h z‖ₑ * ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 1) := by
        refine lintegral_congr fun z => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun y => ?_
        rw [div_eq_mul_inv, one_div]
    _ ≤ ∫⁻ z in Q, ‖h z‖ₑ * C := by
        refine lintegral_mono_ae ((ae_restrict_iff' hQm).2 (Eventually.of_forall fun z hz => ?_))
        exact mul_le_mul' le_rfl (hK z hz)
    _ = C * ∫⁻ z in Q, ‖h z‖ₑ := by
        rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, mul_comm]

/-- **Subgoal** (Theorem 2.1 proof, mollification: the weak gradient of `f ∈ W^{1,1}` is
integrable, since it agrees a.e. with the `L¹` weak derivatives given by `W^{1,1}`). -/
theorem coord_integrable {f : Rd d → ℝ} {G : Rd d → Rd d} (hf : MemW 1 1 f)
    (hG : IsWeakGradient f G) (i : Fin d) : Integrable fun z => Rd.coord i (G z) := by
  have hord : IsWeakDerivative.order (Pi.single i 1 : Fin d → ℕ) ≤ 1 := by
    simp [IsWeakDerivative.order]
  obtain ⟨g, hg, hgL⟩ := hf.2 _ hord
  -- uniqueness of weak derivatives (as in `theorem_5_1.isWeakDerivative_ae_unique`)
  have hG' := hG i
  obtain ⟨_, hgl, hgi⟩ := hg
  obtain ⟨_, hgl', hgi'⟩ := hG'
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgl.sub hgl') fun φ hφ hφc => by
    have hne : ((-1 : ℝ) ^ IsWeakDerivative.order (Pi.single i 1 : Fin d → ℕ)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have heq : ∫ x, g x * φ x = ∫ x, Rd.coord i (G x) * φ x :=
      mul_left_cancel₀ hne ((hgi φ hφ hφc).symm.trans (hgi' φ hφ hφc))
    have hi : Integrable (fun x => φ x • g x) :=
      hgl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hi' : Integrable (fun x => φ x • Rd.coord i (G x)) :=
      hgl'.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi hi']
    simp only [smul_eq_mul, mul_comm (φ _)]
    rw [heq, sub_self]
  have hae : g =ᵐ[volume] fun z => Rd.coord i (G z) := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  exact (memLp_one_iff_integrable.1 hgL).congr hae

/-- **Subgoal** (Theorem 2.1 proof, mollification: a smooth approximate identity exists). -/
theorem exists_mollifier : ∃ ψ : ℕ → Rd d → ℝ,
    (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n x, 0 ≤ ψ n x) ∧ (∀ n, ∫ x, ψ n x = 1) ∧
        ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)) := by
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Rd d) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by have := hpos n; positivity,
      by have := hpos n; linarith⟩
  refine ⟨fun n => (φ n).normed volume, fun n => (φ n).contDiff_normed (n := ⊤),
    fun n => (φ n).hasCompactSupport_normed, fun n x => (φ n).nonneg_normed x,
    fun n => (φ n).integral_normed, fun n => ?_⟩
  rw [(φ n).support_normed_eq]

/-- **Subgoal** (Theorem 2.1 proof, mollification: `∇(f * ψ_n) → ∇f` in `L¹`). -/
theorem tendsto_lintegral_gradient {f : Rd d → ℝ} {G : Rd d → Rd d} (hf : MemW 1 1 f)
    (hG : IsWeakGradient f G) {ψ : ℕ → Rd d → ℝ}
    (hψ : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) (hψc : ∀ n, HasCompactSupport (ψ n))
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫⁻ z, ‖gradient (fun x => ∫ y, f y * ψ n (x - y)) z - G z‖ₑ) atTop
      (𝓝 0) := by
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) := coord_integrable hf hG
  set T : ℕ → Fin d → Rd d → ℝ≥0∞ := fun n i z =>
    ‖(∫ y, Rd.coord i (G y) * ψ n (z - y)) - Rd.coord i (G z)‖ₑ with hT
  have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hbound : ∀ n z, ‖gradient (fun x => ∫ y, f y * ψ n (x - y)) z - G z‖ₑ ≤ ∑ i, T n i z := by
    intro n z
    rw [(contDiff_convolution hG (hψ n) (hψc n)).2 z, hexpG z, ← Finset.sum_sub_distrib]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← sub_smul, enorm_smul]
    have : ‖Rd.basisVec i‖ₑ = 1 := by
      have hn : ‖Rd.basisVec i‖ = 1 := by
        simp [Rd.basisVec]
      rw [← ofReal_norm, hn, ENNReal.ofReal_one]
    rw [this, mul_one]
  have hmeas : ∀ n i, AEMeasurable (T n i) volume := by
    intro n i
    have hc : Continuous fun z => ∫ y, Rd.coord i (G y) * ψ n (z - y) := by
      have : (fun z => ∫ y, Rd.coord i (G y) * ψ n (z - y)) =
          convolution (fun y => Rd.coord i (G y)) (ψ n) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        funext z; simp [convolution_def, smul_eq_mul]
      rw [this]
      exact (hψc n).continuous_convolution_right _ (hGi i).locallyIntegrable (hψ n).continuous
    exact (hc.aemeasurable.sub (hGi i).aemeasurable).enorm
  have hlim : Tendsto (fun n => ∑ i, ∫⁻ z, T n i z) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_convolution (hGi i) hψ0 (fun n => (hψ n).continuous) hψ1 hψs
    simpa [hT] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) fun n => ?_
  calc ∫⁻ z, ‖gradient (fun x => ∫ y, f y * ψ n (x - y)) z - G z‖ₑ
      ≤ ∫⁻ z, ∑ i, T n i z := lintegral_mono (hbound n)
    _ = ∑ i, ∫⁻ z, T n i z := lintegral_finsetSum' _ fun i _ => hmeas n i

/-- **Subgoal** (Theorem 2.1 proof, mollification: `L¹` convergence gives a.e. convergence of a
subsequence, for `ℝ≥0∞`-valued functions). -/
theorem exists_subseq_ae_tendsto_zero {μ : Measure (Rd d)} {S : ℕ → Rd d → ℝ≥0∞}
    (hS : ∀ n, AEMeasurable (S n) μ) (h : Tendsto (fun n => ∫⁻ y, S n y ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ y ∂μ, Tendsto (fun k => S (φ k) y) atTop (𝓝 0) := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, ∫⁻ y, S n y ∂μ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 h _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (ENNReal.ofNat_ne_top (n := 2))) k)
    exact eventually_atTop.2 ⟨N, hN⟩
  obtain ⟨φ, hφ, hφk⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∫⁻ y, ∑' k, S (φ k) y ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun k => hS (φ k)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφk)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun k => hS (φ k)) hsum] with y hy
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne

/-- **Subgoal** (Theorem 2.1 proof, eq. (2) of [BH93] a.e. for `W^{1,1}`, by mollification): for
a cube or ball `Q`, for a.e. `y ∈ Q`, `|f(y) - f_Q| ≤ K ∫_Q |∇f(z)| / |y - z|^{d-1} dz`. -/
theorem poincare_ae (hd : 0 < d) : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G → ∀ Q : Set (Rd d), IsCubeOrBall Q →
      ∀ᵐ y ∂volume, y ∈ Q → ENNReal.ofReal |f y - ⨍ z in Q, f z| ≤
        K * ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1) := by
  obtain ⟨K0, hK0⟩ := isCubeOrBall_props hd
  obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ := exists_mollifier (d := d)
  refine ⟨K0, fun f G hf hG Q hQ => ?_⟩
  obtain ⟨hQc, hQm, hQb, hQ0, hQK⟩ := hK0 Q hQ
  have hQt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) := coord_integrable hf hG
  -- measurability of `G`
  have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGm : AEStronglyMeasurable G volume := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext hexpG
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGi i).aestronglyMeasurable.smul_const _
  set G' := hGm.mk G with hG'def
  have hG'm : Measurable G' := hGm.stronglyMeasurable_mk.measurable
  have hGG' : G =ᵐ[volume] G' := hGm.ae_eq_mk
  -- the mollified functions
  set F : ℕ → Rd d → ℝ := fun n x => ∫ y, f y * ψ n (x - y) with hFdef
  have hFc : ∀ n, ContDiff ℝ 1 (F n) := fun n => (contDiff_convolution hG (hψ n) (hψc n)).1
  have hgradc : ∀ n, Continuous (gradient (F n)) := fun n =>
    (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp ((hFc n).continuous_fderiv one_ne_zero)
  set e : ℝ := (d : ℝ) - 1 with he
  set P : ℕ → Rd d → ℝ≥0∞ := fun n y =>
    ∫⁻ z in Q, ‖gradient (F n) z - G' z‖ₑ / edist y z ^ e with hPdef
  have hPm : ∀ n, Measurable (P n) := by
    intro n
    have hm : Measurable fun p : Rd d × Rd d => ‖gradient (F n) p.2 - G' p.2‖ₑ / edist p.1 p.2 ^ e :=
      ((((hgradc n).measurable.sub hG'm).enorm).comp measurable_snd).div
        ((continuous_edist.measurable).pow_const _)
    exact hm.lintegral_prod_right'
  set S : ℕ → Rd d → ℝ≥0∞ := fun n y => ‖F n y - f y‖ₑ + P n y with hSdef
  have hSm : ∀ n, AEMeasurable (S n) (volume.restrict Q) := fun n =>
    ((((hFc n).continuous.measurable.aemeasurable.sub hfi.aemeasurable).enorm).add
      (hPm n).aemeasurable).restrict
  -- `L¹` convergence
  obtain ⟨CQ, hCQ⟩ := lintegral_potential_le hd hQb hQm
  have hA := tendsto_convolution hfi hψ0 (fun n => (hψ n).continuous) hψ1 hψs
  have hB := tendsto_lintegral_gradient hf hG hψ hψc hψ0 hψ1 hψs
  have hB' : ∀ n, ∫⁻ z, ‖gradient (F n) z - G' z‖ₑ = ∫⁻ z, ‖gradient (F n) z - G z‖ₑ := by
    intro n
    refine lintegral_congr_ae (hGG'.mono fun z hz => ?_)
    simp only [hz]
  have hSint : Tendsto (fun n => ∫⁻ y in Q, S n y) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => (∫⁻ x, ‖F n x - f x‖ₑ) + CQ * ∫⁻ z, ‖gradient (F n) z - G z‖ₑ)
        atTop (𝓝 (0 + (CQ : ℝ≥0∞) * 0)) :=
      hA.add (ENNReal.Tendsto.const_mul hB (Or.inr ENNReal.coe_ne_top))
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => zero_le)
      fun n => ?_
    have hpot := hCQ (fun z => ‖gradient (F n) z - G' z‖)
      (((hgradc n).aestronglyMeasurable.sub hG'm.aestronglyMeasurable).norm)
    simp only [enorm_norm] at hpot
    calc ∫⁻ y in Q, S n y
        = (∫⁻ y in Q, ‖F n y - f y‖ₑ) + ∫⁻ y in Q, P n y := by
          have hm1 : AEMeasurable (fun y => ‖F n y - f y‖ₑ) (volume.restrict Q) :=
            (((hFc n).continuous.measurable.aemeasurable.sub hfi.aemeasurable).enorm).restrict
          simp only [hSdef]
          rw [lintegral_add_left' hm1]
      _ ≤ (∫⁻ x, ‖F n x - f x‖ₑ) + CQ * ∫⁻ z, ‖gradient (F n) z - G z‖ₑ := by
          refine add_le_add (setLIntegral_le_lintegral _ _) ?_
          rw [← hB' n]
          exact hpot.trans (mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _))
  obtain ⟨φ, hφmono, hφ⟩ := exists_subseq_ae_tendsto_zero hSm hSint
  -- convergence of the averages
  have hFi : ∀ n, IntegrableOn (F n) Q := fun n =>
    ((hFc n).continuous.continuousOn.integrableOn_compact hQb.isCompact_closure).mono_set
      subset_closure
  have hfQ : IntegrableOn f Q := hfi.integrableOn
  have hav : Tendsto (fun n => ⨍ z in Q, F n z) atTop (𝓝 (⨍ z in Q, f z)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hlim : Tendsto (fun n => (volume Q)⁻¹ * ∫⁻ x, ‖F n x - f x‖ₑ) atTop
        (𝓝 ((volume Q)⁻¹ * 0)) :=
      ENNReal.Tendsto.const_mul hA (Or.inr (ENNReal.inv_ne_top.2 hQ0))
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      fun n => ?_
    rw [edist_dist, Real.dist_eq, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub,
      ← integral_sub (hFi n) hfQ, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg,
      ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg), measureReal_def,
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hQ0 hQt), ENNReal.ofReal_toReal hQt]
    refine mul_le_mul' le_rfl ?_
    calc ENNReal.ofReal |∫ x in Q, (F n x - f x)|
        ≤ ENNReal.ofReal (∫ x in Q, |F n x - f x|) :=
          ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
      _ = ∫⁻ x in Q, ‖F n x - f x‖ₑ := by
          have hi2 : Integrable (fun x => |F n x - f x|) (volume.restrict Q) := ((hFi n).sub hfQ).abs
          rw [ofReal_integral_eq_lintegral_ofReal hi2
            (Eventually.of_forall fun _ => abs_nonneg _)]
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ x, ‖F n x - f x‖ₑ := setLIntegral_le_lintegral _ _
  -- the constant of `poincare_of_contDiff`
  have hcQ : Metric.ediam Q ^ (d : ℝ) / (d * volume Q) ≤ K0 := by
    refine ENNReal.div_le_of_le_mul (hQK.trans ?_)
    rw [mul_comm (d : ℝ≥0∞), ← mul_assoc]
    refine le_mul_of_one_le_right' ?_
    exact_mod_cast hd
  -- conclude
  rw [ae_restrict_iff' hQm] at hφ
  have hGae : ∀ᵐ z ∂volume, G z = G' z := hGG'
  filter_upwards [hφ] with y hy hyQ
  have hSy := hy hyQ
  have h1 : Tendsto (fun k => ‖F (φ k) y - f y‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSy (fun k => zero_le)
      fun k => le_self_add
  have h2 : Tendsto (fun k => P (φ k) y) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSy (fun k => zero_le)
      fun k => le_add_self
  have hFy : Tendsto (fun k => F (φ k) y) atTop (𝓝 (f y)) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa [edist_eq_enorm_sub] using h1
  have hav' : Tendsto (fun k => ⨍ z in Q, F (φ k) z) atTop (𝓝 (⨍ z in Q, f z)) :=
    hav.comp hφmono.tendsto_atTop
  set A : ℝ≥0∞ := ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e with hA
  have hlhs : Tendsto (fun k => ENNReal.ofReal |F (φ k) y - ⨍ z in Q, F (φ k) z|) atTop
      (𝓝 (ENNReal.ofReal |f y - ⨍ z in Q, f z|)) :=
    ENNReal.tendsto_ofReal ((hFy.sub hav').abs)
  have hrhs : Tendsto (fun k => (K0 : ℝ≥0∞) * (A + P (φ k) y)) atTop (𝓝 ((K0 : ℝ≥0∞) * (A + 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h2) (Or.inr ENNReal.coe_ne_top)
  rw [add_zero] at hrhs
  refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
  have hp := poincare_of_contDiff hd (hFc (φ k)) hQc hQm hQb hQ0 hyQ
  refine hp.trans (mul_le_mul' hcQ ?_)
  have hAm : AEMeasurable (fun z => ‖G z‖ₑ / edist y z ^ e) (volume.restrict Q) :=
    (hGm.aemeasurable.enorm.div
      ((continuous_const.edist continuous_id).measurable.pow_const _).aemeasurable).restrict
  calc ∫⁻ z in Q, ‖gradient (F (φ k)) z‖ₑ / edist y z ^ e
      ≤ ∫⁻ z in Q, (‖G z‖ₑ / edist y z ^ e + ‖gradient (F (φ k)) z - G' z‖ₑ / edist y z ^ e) := by
        refine lintegral_mono_ae (ae_restrict_of_ae (hGae.mono fun z hz => ?_))
        rw [← ENNReal.add_div]
        refine ENNReal.div_le_div_right ?_ _
        rw [hz]
        calc ‖gradient (F (φ k)) z‖ₑ = ‖G' z + (gradient (F (φ k)) z - G' z)‖ₑ := by
              rw [add_sub_cancel]
          _ ≤ _ := enorm_add_le _ _
    _ = A + P (φ k) y := by rw [lintegral_add_left' hAm]

/-- **Subgoal** (Theorem 2.1 proof: at a Lebesgue point the precise representative is the
Lebesgue value). -/
theorem preciseRepresentative_eq {f : Rd d → ℝ} (hf : LocallyIntegrable f) {x : Rd d} {c : ℝ}
    (hc : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0)) :
    preciseRepresentative f x = c := by
  have key : ∀ r : ℝ, 0 < r →
      |(⨍ y in Metric.ball x r, f y) - c| ≤ ⨍ y in Metric.ball x r, |f y - c| := by
    intro r hr
    have hfin : volume (Metric.ball x r) ≠ ⊤ := measure_ball_lt_top.ne
    have hpos : volume (Metric.ball x r) ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
    have hi : IntegrableOn f (Metric.ball x r) :=
      (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
    have hreal : volume.real (Metric.ball x r) ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    have e : (volume.real (Metric.ball x r))⁻¹ * (∫ y in Metric.ball x r, f y) - c =
        (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, (f y - c) := by
      rw [integral_sub hi (integrableOn_const hfin), setIntegral_const, smul_eq_mul]
      field_simp
    rw [e, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.2 measureReal_nonneg)
  have ht : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y) (𝓝[>] 0) (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hc
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Real.norm_eq_abs]
    exact key r hr
  exact ht.limsup_eq

/-- **Subgoal** (Theorem 2.1 proof: cubes and balls have positive density at each of their
points): `|Q ∩ B(x,r)| ≥ κ_d |B(x,r)|` for `x ∈ Q` and small `r`. -/
theorem volume_inter_ball_ge (hd : 0 < d) : ∃ κ : ℝ≥0, 0 < κ ∧ ∀ Q : Set (Rd d), IsCubeOrBall Q →
    ∀ x ∈ Q, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (κ : ℝ≥0∞) * volume (Metric.ball x r) ≤ volume (Q ∩ Metric.ball x r) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨Real.toNNReal (((4 * d : ℝ) ^ d)⁻¹), Real.toNNReal_pos.2 (by positivity),
    fun Q hQ x hx => ?_⟩
  obtain ⟨c, ρ, hρ, hQc, -, hin, hout⟩ := ball_subset_subset hd hQ
  have hxc : ‖x - c‖ ≤ d * ρ := by
    have := hout hx; rwa [Metric.mem_closedBall, dist_eq_norm] at this
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 4 * d * ρ)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  set t : ℝ := r / (4 * d * ρ) with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [htdef, div_le_one (by positivity)]; exact hr1.le
  set c' : Rd d := x + t • (c - x) with hc'
  have hsub : Metric.ball c' (t * ρ) ⊆ Q ∩ Metric.ball x r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    set y : Rd d := x + t⁻¹ • (z - x) with hy
    have hyc : y - c = t⁻¹ • (z - c') := by
      have h1 : t⁻¹ • (t • (c - x)) = c - x := by
        rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
      rw [hy, hc', sub_add_eq_sub_sub, smul_sub (t⁻¹) (z - x), h1]; abel
    have hyQ : y ∈ Q := by
      apply hin
      rw [Metric.mem_ball, dist_eq_norm, hyc, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
      calc t⁻¹ * ‖z - c'‖ < t⁻¹ * (t * ρ) := mul_lt_mul_of_pos_left hz (inv_pos.2 ht0)
        _ = ρ := by field_simp
    have hzeq : z = x + t • (y - x) := by
      simp only [hy, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]; abel
    refine ⟨hzeq ▸ hQc.add_smul_sub_mem hx hyQ ⟨ht0.le, ht1⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, hzeq, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht0.le]
    have hyx : ‖y - x‖ < 2 * d * ρ := by
      calc ‖y - x‖ = ‖(y - c) + (c - x)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - c‖ + ‖c - x‖ := norm_add_le _ _
        _ < ρ + d * ρ := by
            refine add_lt_add_of_lt_of_le ?_ (by rw [norm_sub_rev]; exact hxc)
            have := hin.trans_eq rfl
            rw [hyc, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
            calc t⁻¹ * ‖z - c'‖ < t⁻¹ * (t * ρ) := mul_lt_mul_of_pos_left hz (inv_pos.2 ht0)
              _ = ρ := by field_simp
        _ ≤ 2 * d * ρ := by nlinarith
    calc t * ‖y - x‖ ≤ t * (2 * d * ρ) := mul_le_mul_of_nonneg_left hyx.le ht0.le
      _ = r / 2 := by rw [htdef]; field_simp; ring
      _ < r := by linarith
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [Measure.addHaar_ball_of_pos volume x hr0, Measure.addHaar_ball_of_pos volume c' (by positivity),
    finrank_euclideanSpace_fin, ← mul_assoc, ENNReal.ofReal.eq_def, ← ENNReal.coe_mul]
  congr 2
  rw [← Real.toNNReal_mul (by positivity)]
  congr 1
  have htr : r / (4 * d * ρ) * ρ = r / (4 * d) := by field_simp
  rw [htdef, htr, div_pow]
  field_simp

/-- **Subgoal** (Theorem 2.1 proof, [BH93, Lemma 2] with `α = 1`):
`∫_{B(x,r)} |y - z|^{1-d} dy ≤ C |B(x,r)| |x - z|^{1-d}`. -/
theorem lintegral_ball_kernel_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (x z : Rd d) {r : ℝ}, 0 < r →
    ∫⁻ y in Metric.ball x r, 1 / edist y z ^ ((d : ℝ) - 1) ≤
      C * volume (Metric.ball x r) / edist x z ^ ((d : ℝ) - 1) := by
  obtain ⟨C0, -, hC0⟩ := lemma_2_2 d (α := 1) one_pos
  set e : ℝ := (d : ℝ) - 1 with he
  have he0 : 0 ≤ e := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set V := volume (Metric.ball (0 : Rd d) 1) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set Vr : ℝ := V.toReal with hVr
  have hVr0 : 0 < Vr := ENNReal.toReal_pos hV0 hVt
  set Cr : ℝ := (2 : ℝ) ^ e + C0 * 6 * (2 : ℝ) ^ e / Vr with hCr
  have h2e : 0 < (2 : ℝ) ^ e := by positivity
  have hCr0 : 0 ≤ Cr := by positivity
  refine ⟨Cr.toNNReal, fun x z r hr => ?_⟩
  have hCe : ((Cr.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cr := rfl
  have hvol : volume (Metric.ball x r) = ENNReal.ofReal (r ^ d) * V := by
    rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin]
  rcases le_or_gt (2 * r) (dist x z) with hfar | hnear
  · -- far case: `|y - z| ≥ |x - z| / 2` on the ball
    have hxz : 0 < dist x z := by linarith
    have hE : edist x z ^ e = ENNReal.ofReal (dist x z ^ e) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg he0]
    have hpt : ∀ y ∈ Metric.ball x r, 1 / edist y z ^ e ≤ ENNReal.ofReal ((2 : ℝ) ^ e / dist x z ^ e) := by
      intro y hy
      have hyz : dist x z / 2 ≤ dist y z := by
        have := dist_triangle x y z
        have hxy : dist x y < r := by rw [dist_comm]; exact Metric.mem_ball.1 hy
        linarith
      have hpos : 0 < dist x z / 2 := by positivity
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg he0, one_div,
        ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (hpos.trans_le hyz) _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (dist y z ^ e)⁻¹ ≤ ((dist x z / 2) ^ e)⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hyz he0)
        _ = (2 : ℝ) ^ e / dist x z ^ e := by
            rw [Real.div_rpow hxz.le (by norm_num), inv_div]
    calc ∫⁻ y in Metric.ball x r, 1 / edist y z ^ e
        ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal ((2 : ℝ) ^ e / dist x z ^ e) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ((2 : ℝ) ^ e / dist x z ^ e) * volume (Metric.ball x r) :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal Cr * volume (Metric.ball x r) / edist x z ^ e := by
          rw [hE, ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hxz _), div_eq_mul_inv,
            div_eq_mul_inv, mul_right_comm]
          refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
          rw [hCr]; have : 0 ≤ C0 * 6 * (2 : ℝ) ^ e / Vr := by positivity
          linarith
      _ = _ := by rw [hCe]
  · -- near case: `B(x, r) ⊆ B̄(z, 3r)` and Lemma 2.2
    have hsub : Metric.ball x r ⊆ Metric.closedBall z (3 * r) := fun y hy => by
      rw [Metric.mem_closedBall]
      have := dist_triangle y x z
      have : dist y x < r := Metric.mem_ball.1 hy
      linarith
    have h3 : 0 < 3 * r := by positivity
    have hball : IsCubeOrBall (Metric.closedBall z (3 * r)) := ⟨z, 3 * r, h3, Or.inr (Or.inl rfl)⟩
    have hlem := hC0 (Metric.closedBall z (3 * r)) (fun _ => (1 : ℝ)) hball
      (integrableOn_const measure_closedBall_lt_top.ne) z (Metric.mem_closedBall_self h3.le)
    have hM : localMaximalFunction (Metric.ediam (Metric.closedBall z (3 * r)))
        (fun _ : Rd d => (1 : ℝ)) z ≤ 1 := by
      refine iSup_le fun r => iSup_le fun _ => iSup_le fun _ => ?_
      rw [laverage_eq]
      simp only [enorm_one, lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact ENNReal.div_self_le_one
    have hdiam : Metric.ediam (Metric.closedBall z (3 * r)) ≤ ENNReal.ofReal (2 * (3 * r)) := by
      rw [← ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top]
      exact ENNReal.ofReal_le_ofReal (Metric.diam_closedBall h3.le)
    have hE : edist x z ^ e ≤ ENNReal.ofReal ((2 * r) ^ e) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg he0]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow dist_nonneg hnear.le he0)
    have h2r : 0 < (2 * r) ^ e := by positivity
    calc ∫⁻ y in Metric.ball x r, 1 / edist y z ^ e
        ≤ ∫⁻ y in Metric.closedBall z (3 * r), 1 / edist y z ^ e := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.closedBall z (3 * r),
            ‖(fun _ : Rd d => (1 : ℝ)) y‖ₑ / edist z y ^ ((d : ℝ) - 1) := by
          simp only [enorm_one, edist_comm, he]
      _ ≤ C0 * Metric.ediam (Metric.closedBall z (3 * r)) ^ (1 : ℝ) *
            localMaximalFunction (Metric.ediam (Metric.closedBall z (3 * r)))
              (fun _ => (1 : ℝ)) z := hlem
      _ ≤ C0 * ENNReal.ofReal (2 * (3 * r)) * 1 := by rw [ENNReal.rpow_one]; gcongr
      _ = ENNReal.ofReal (C0 * 6 * r) := by
          rw [mul_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (Cr * r ^ d * Vr / (2 * r) ^ e) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hrd : r ^ d / (2 * r) ^ e = r / (2 : ℝ) ^ e := by
            rw [Real.mul_rpow (by norm_num) hr.le, he, Real.rpow_sub_one hr.ne', Real.rpow_natCast]
            field_simp
          rw [show Cr * r ^ d * Vr / (2 * r) ^ e = Cr * Vr * (r ^ d / (2 * r) ^ e) by ring, hrd,
            hCr, add_mul, add_mul]
          have : 0 ≤ (2 : ℝ) ^ e * Vr * (r / (2 : ℝ) ^ e) := by positivity
          have key : C0 * 6 * (2 : ℝ) ^ e / Vr * Vr * (r / (2 : ℝ) ^ e) = C0 * 6 * r := by
            field_simp
          linarith [key, this]
      _ = ENNReal.ofReal Cr * (ENNReal.ofReal (r ^ d) * V) / ENNReal.ofReal ((2 * r) ^ e) := by
          rw [ENNReal.ofReal_div_of_pos h2r, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hCr0, hVr, ENNReal.ofReal_toReal hVt, mul_assoc]
      _ ≤ ENNReal.ofReal Cr * volume (Metric.ball x r) / edist x z ^ e := by
          rw [hvol]; exact ENNReal.div_le_div_left hE _
      _ = _ := by rw [hCe]

/-- **Subgoal** (Theorem 2.1 proof, the Lebesgue-point limit): if `x ∈ Q` is a Lebesgue point of
`f ∈ W^{1,1}` with value `c`, then `|c - f_Q| ≤ C ∫_Q |∇f(z)| / |x - z|^{d-1} dz` (average (2)
over `Q ∩ B(x,r)`, use [BH93, Lemma 2] and let `r → 0`). -/
theorem abs_sub_average_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (Q : Set (Rd d)) (x : Rd d) (c : ℝ), MemW 1 1 f → IsWeakGradient f G → IsCubeOrBall Q →
      x ∈ Q → Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0) →
        ENNReal.ofReal |c - ⨍ z in Q, f z| ≤
          C * ∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1) := by
  obtain ⟨K, hK⟩ := poincare_ae hd
  obtain ⟨κ, hκ0, hκ⟩ := volume_inter_ball_ge hd
  obtain ⟨C, hC⟩ := lintegral_ball_kernel_le hd
  obtain ⟨K0, hK0⟩ := isCubeOrBall_props hd
  refine ⟨κ⁻¹ * K * C, fun f G Q x c hf hG hQ hx hc => ?_⟩
  obtain ⟨-, hQm, hQb, -, -⟩ := hK0 Q hQ
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) := coord_integrable hf hG
  have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGm : AEStronglyMeasurable G volume := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext hexpG
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGi i).aestronglyMeasurable.smul_const _
  set e : ℝ := (d : ℝ) - 1 with he
  set L : ℝ≥0∞ := ENNReal.ofReal |c - ⨍ z in Q, f z| with hL
  set I : ℝ≥0∞ := ∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ e with hI
  have hκ0' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0.ne'
  have key : ∀ᶠ r in 𝓝[>] (0 : ℝ), (κ : ℝ≥0∞) * L ≤
      ENNReal.ofReal (⨍ y in Metric.ball x r, |f y - c|) + K * C * I := by
    filter_upwards [hκ Q hQ x hx, self_mem_nhdsWithin] with r hr hr0
    have hr0 : (0 : ℝ) < r := hr0
    set B := Metric.ball x r with hB
    set A := Q ∩ B with hA
    have hAm : MeasurableSet A := hQm.inter measurableSet_ball
    have hVB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr0).ne'
    have hVBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
    -- pointwise on `A`
    have hpt : ∀ᵐ y ∂(volume.restrict A), L ≤ ENNReal.ofReal |f y - c| +
        K * ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e := by
      have h1 := ae_restrict_of_ae (μ := volume) (s := A) (hK f G hf hG Q hQ)
      filter_upwards [h1, ae_restrict_mem hAm] with y hy hyA
      refine le_trans ?_ (add_le_add le_rfl (hy hyA.1))
      rw [hL, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |c - ⨍ z in Q, f z| ≤ |c - f y| + |f y - ⨍ z in Q, f z| := abs_sub_le _ _ _
        _ = |f y - c| + |f y - ⨍ z in Q, f z| := by rw [abs_sub_comm c]
    -- the kernel term
    have hm : AEMeasurable (Function.uncurry fun (y z : Rd d) => ‖G z‖ₑ / edist y z ^ e)
        ((volume.restrict A).prod (volume.restrict Q)) := by
      have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖G p.2‖ₑ)
          ((volume.restrict A).prod (volume.restrict Q)) :=
        hGm.restrict.aemeasurable.enorm.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      have h2 : Measurable fun p : Rd d × Rd d => edist p.1 p.2 ^ e :=
        (continuous_edist.measurable).pow_const _
      exact h1.div h2.aemeasurable
    have hJ : ∫⁻ y in A, ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e ≤ C * volume B * I := by
      calc ∫⁻ y in A, ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e
          = ∫⁻ z in Q, ∫⁻ y in A, ‖G z‖ₑ / edist y z ^ e := lintegral_lintegral_swap hm
        _ = ∫⁻ z in Q, ‖G z‖ₑ * ∫⁻ y in A, 1 / edist y z ^ e := by
            refine lintegral_congr fun z => ?_
            rw [← lintegral_const_mul' _ _ enorm_ne_top]
            refine lintegral_congr fun y => ?_
            rw [div_eq_mul_inv, one_div]
        _ ≤ ∫⁻ z in Q, ‖G z‖ₑ * (C * volume B / edist x z ^ e) := by
            refine lintegral_mono fun z => mul_le_mul' le_rfl ?_
            exact (lintegral_mono_set Set.inter_subset_right).trans (hC x z hr0)
        _ = ∫⁻ z in Q, (C * volume B) * (‖G z‖ₑ / edist x z ^ e) := by
            refine lintegral_congr fun z => ?_
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        _ = C * volume B * I := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hVBt)]
    have hfB : IntegrableOn (fun y => |f y - c|) B :=
      (hfi.integrableOn.sub (integrableOn_const hVBt)).abs
    have havg : ENNReal.ofReal (⨍ y in B, |f y - c|) =
        (volume B)⁻¹ * ∫⁻ y in B, ENNReal.ofReal |f y - c| := by
      rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg),
        ofReal_integral_eq_lintegral_ofReal hfB (Eventually.of_forall fun _ => abs_nonneg _),
        measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hVB0 hVBt),
        ENNReal.ofReal_toReal hVBt]
    have hint : (κ : ℝ≥0∞) * volume B * L ≤
        (∫⁻ y in B, ENNReal.ofReal |f y - c|) + K * (C * volume B * I) := by
      calc (κ : ℝ≥0∞) * volume B * L ≤ volume A * L := mul_le_mul' hr le_rfl
        _ = ∫⁻ y in A, L := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in A, (ENNReal.ofReal |f y - c| + K * ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e) :=
            lintegral_mono_ae hpt
        _ = (∫⁻ y in A, ENNReal.ofReal |f y - c|) +
              K * ∫⁻ y in A, ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ e := by
            have hm1 : AEMeasurable (fun y => ENNReal.ofReal |f y - c|) (volume.restrict A) :=
              (hfi.aemeasurable.sub aemeasurable_const).abs.ennreal_ofReal.restrict
            rw [lintegral_add_left' hm1,
              lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        _ ≤ _ := add_le_add (lintegral_mono_set Set.inter_subset_right) (mul_le_mul' le_rfl hJ)
    calc (κ : ℝ≥0∞) * L = (volume B)⁻¹ * ((κ : ℝ≥0∞) * volume B * L) := by
          rw [show (κ : ℝ≥0∞) * volume B * L = volume B * (κ * L) by ring, ← mul_assoc,
            ENNReal.inv_mul_cancel hVB0 hVBt, one_mul]
      _ ≤ (volume B)⁻¹ * ((∫⁻ y in B, ENNReal.ofReal |f y - c|) + K * (C * volume B * I)) :=
          mul_le_mul' le_rfl hint
      _ = ENNReal.ofReal (⨍ y in B, |f y - c|) + K * C * I := by
          rw [mul_add, havg]
          congr 1
          rw [show (K : ℝ≥0∞) * (C * volume B * I) = volume B * (K * C * I) by ring, ← mul_assoc,
            ENNReal.inv_mul_cancel hVB0 hVBt, one_mul]
  have hlim : Tendsto (fun r => ENNReal.ofReal (⨍ y in Metric.ball x r, |f y - c|) + K * C * I)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 + K * C * I)) := by
    have := ENNReal.tendsto_ofReal hc
    rw [ENNReal.ofReal_zero] at this
    exact this.add tendsto_const_nhds
  rw [zero_add] at hlim
  have hκL : (κ : ℝ≥0∞) * L ≤ K * C * I := ge_of_tendsto hlim key
  calc L = (κ : ℝ≥0∞)⁻¹ * ((κ : ℝ≥0∞) * L) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hκ0' ENNReal.coe_ne_top, one_mul]
    _ ≤ (κ : ℝ≥0∞)⁻¹ * (K * C * I) := mul_le_mul' le_rfl hκL
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hκ0.ne']
        ring

end theorem_2_1_first

end WeakPathwiseIto
