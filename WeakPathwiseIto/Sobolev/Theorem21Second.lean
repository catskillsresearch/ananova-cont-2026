/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.Theorem21First
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace

/-! # Steps of the proof of Theorem 2.1, second estimate ([BH93, Thm 2], `m = 2`)

Following [BH93, §2]: with the averaged Taylor polynomial
`T_Q f (w) = ⨍_{z ∈ Q} (f z + ⟪∇f z, w - z⟫)`, the bound [BH93, (5)] for `m = 2`
(`|f x - T_Q f x| ≤ C ∫_Q |∇²f| / |x - z|^{d-2}`) is proved for `C²` functions by Taylor's
formula along segments and a homothety change of variables, extended a.e. to `W^{2,1}` by
mollification, and passed to Lebesgue points by averaging over `Q ∩ B(x,r)`
([BH93, Lemma 2]).  The splitting [BH93, (8)] then reduces the estimate to this bound at `x`
and `y` plus the first estimate applied to the coordinates `∂_i f`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_2_1_second

variable {d : ℕ}

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²`, step 1: homothety with
quadratic weight): the substitution `z = x + s (y - x)` on a convex `Q ∋ x`. -/
theorem lintegral_comp_homothety_sq_le {Q : Set (Rd d)} (hQ : Convex ℝ Q)
    (hQm : MeasurableSet Q) {x : Rd d} (hx : x ∈ Q) {D : ℝ} (hD : ∀ z ∈ Q, dist z x ≤ D)
    {g : Rd d → ℝ≥0∞} (hg : Measurable g) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2 ≤
      ENNReal.ofReal (s ^ (-(d : ℝ) - 2)) *
        ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z := by
  have hs0 : 0 < s := hs.1
  set H : Rd d → ℝ≥0∞ :=
    Q.indicator ({z | dist z x ≤ s * D}.indicator fun z => g z * ‖z - x‖ₑ ^ 2) with hH
  have hinv : ENNReal.ofReal (s⁻¹ ^ 2) * ENNReal.ofReal s ^ 2 = 1 := by
    rw [← ENNReal.ofReal_pow hs0.le, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hs0.le) 2),
      ← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, ENNReal.ofReal_one]
  have step1 : ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2 ≤
      ∫⁻ y, ENNReal.ofReal (s⁻¹ ^ 2) * H (x + s • (y - x)) := by
    refine (lintegral_mono_ae ((ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy => ?_))).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hzQ : x + s • (y - x) ∈ Q := hQ.add_smul_sub_mem hx hy ⟨hs0.le, hs.2⟩
    have hzd : dist (x + s • (y - x)) x ≤ s * D := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hD y hy) hs0.le
    have hval : H (x + s • (y - x)) =
        g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ) ^ 2 := by
      rw [hH, indicator_of_mem hzQ, indicator_of_mem (show _ ∈ {z | dist z x ≤ s * D} from hzd),
        add_sub_cancel_left, enorm_smul, Real.enorm_of_nonneg hs0.le]
    rw [hval]
    refine le_of_eq ?_
    calc g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2
        = (ENNReal.ofReal (s⁻¹ ^ 2) * ENNReal.ofReal s ^ 2) * (g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal (s⁻¹ ^ 2) * (g (x + s • (y - x)) * (ENNReal.ofReal s * ‖y - x‖ₑ) ^ 2) := by
          ring
  have step4 : ∫⁻ w, H (x + s • w) =
      ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ u, H (x + u) := by
    have := lintegral_map_equiv (fun u => H (x + u)) (MeasurableEquiv.smul₀ s hs0.ne') (μ := volume)
    have hmap : Measure.map (MeasurableEquiv.smul₀ s hs0.ne' : Rd d ≃ᵐ Rd d) volume =
        ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) • volume :=
      Measure.map_addHaar_smul volume hs0.ne'
    rw [hmap, lintegral_smul_measure] at this
    exact this.symm
  calc ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ^ 2
      ≤ ∫⁻ y, ENNReal.ofReal (s⁻¹ ^ 2) * H (x + s • (y - x)) := step1
    _ = ENNReal.ofReal (s⁻¹ ^ 2) * ∫⁻ w, H (x + s • w) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun w => H (x + s • w)) x]
    _ = ENNReal.ofReal (s⁻¹ ^ 2) *
          (ENNReal.ofReal (|(s ^ Module.finrank ℝ (Rd d))⁻¹|) * ∫⁻ z, H z) := by
        rw [step4, lintegral_add_left_eq_self H x]
    _ = ENNReal.ofReal (s ^ (-(d : ℝ) - 2)) *
          ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z := by
        rw [hH, lintegral_indicator hQm, ← mul_assoc,
          ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hs0.le) 2)]
        congr 2
        rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 (pow_pos hs0 d)),
          Real.rpow_sub hs0, Real.rpow_neg hs0.le, Real.rpow_natCast,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²`, step 2: Taylor's formula
with integral remainder along the segment from `z` to `x`, reparametrised from `x`). -/
theorem abs_taylor_le {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x z : Rd d) :
    ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫| ≤
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t *
        ‖fderiv ℝ (fderiv ℝ f) (x + t • (z - x))‖ₑ * ‖z - x‖ₑ ^ 2 := by
  set v := z - x
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD2 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable one_ne_zero
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv one_ne_zero
  have hl : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  -- φ' and φ''
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t :=
    fun t => (hD1 (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hφ' : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
    intro t
    have h := (hD2 (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
    exact h.clm_apply (hasDerivAt_const t v) |>.congr_deriv (by simp)
  set F : ℝ → ℝ := fun t => t * fderiv ℝ f (x + t • v) v - f (x + t • v) with hF
  have hFd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt F (t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
    intro t _
    have h := (((hasDerivAt_id t).mul (hφ' t)).sub (hφ t))
    refine h.congr_deriv ?_
    simp only [id]; ring
  have hcont : Continuous fun t : ℝ => t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
    have h1 : Continuous fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) :=
      hc2.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact continuous_id.mul ((h1.clm_apply continuous_const).clm_apply continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFd (hcont.intervalIntegrable 0 1)
  have hgrad : ⟪gradient f z, x - z⟫ = fderiv ℝ f z (x - z) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hxz : x - z = -v := by simp [v]
  have hkey : f x - f z - ⟪gradient f z, x - z⟫ =
      ∫ t in (0 : ℝ)..1, t * fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
    rw [hftc, hgrad, hxz, map_neg]
    simp only [hF, one_smul, zero_smul, add_zero, one_mul, zero_mul, zero_sub, v,
      add_sub_cancel]
    ring
  rw [hkey, ← Real.enorm_eq_ofReal_abs, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans
    (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_)
  have ht0 : 0 ≤ t := ht.1.le
  rw [enorm_mul, Real.enorm_of_nonneg ht0, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have h1 := (fderiv ℝ (fderiv ℝ f) (x + t • v) v).le_opNorm v
  have h2 := (fderiv ℝ (fderiv ℝ f) (x + t • v)).le_opNorm v
  calc ‖fderiv ℝ (fderiv ℝ f) (x + t • v) v v‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • v) v‖ * ‖v‖ := h1
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • v)‖ * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = _ := by ring

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `C²` on a convex `Q`). -/
theorem poincare2_of_contDiff (hd : 0 < d) {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f)
    {Q : Set (Rd d)} (hQ : Convex ℝ Q) (hQm : MeasurableSet Q) (hQb : Bornology.IsBounded Q)
    (hQ0 : volume Q ≠ 0) {x : Rd d} (hx : x ∈ Q) :
    ENNReal.ofReal |f x - ⨍ z in Q, (f z + ⟪gradient f z, x - z⟫)| ≤
      Metric.ediam Q ^ (d : ℝ) / (d * volume Q) *
        ∫⁻ z in Q, ‖fderiv ℝ (fderiv ℝ f) z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
  set D := Metric.diam Q with hDdef
  have hD : ∀ z ∈ Q, dist z x ≤ D := fun z hz => Metric.dist_le_diam_of_mem hQb hz hx
  set g : Rd d → ℝ≥0∞ := fun z => ‖fderiv ℝ (fderiv ℝ f) z‖ₑ with hgdef
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgm : Measurable g := (continuous_enorm.comp (hf1.continuous_fderiv one_ne_zero)).measurable
  have hVt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  set φ : Rd d → ℝ := fun z => f z + ⟪gradient f z, x - z⟫ with hφdef
  have hφc : Continuous φ := by
    have hgc : Continuous fun z => gradient f z :=
      (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp
        (hf.continuous_fderiv (by norm_num))
    exact hf.continuous.add (hgc.inner (continuous_const.sub continuous_id))
  have hi : IntegrableOn φ Q :=
    (hφc.continuousOn.integrableOn_compact hQb.isCompact_closure).mono_set subset_closure
  set G : Rd d → ℝ≥0∞ := fun z => g z * ‖z - x‖ₑ ^ 2 with hGdef
  set C : ℝ≥0∞ := Metric.ediam Q ^ (d : ℝ) / d with hCdef
  -- Step A: average bound
  have stepA : ENNReal.ofReal |f x - ⨍ z in Q, φ z| ≤
      (volume Q)⁻¹ * ∫⁻ z in Q, ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫| := by
    have hreal : volume.real Q ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨hQ0, hVt⟩
    have hint : IntegrableOn (fun y => φ y - f x) Q := hi.sub (integrableOn_const hVt)
    have e : f x - ⨍ y in Q, φ y = -((volume.real Q)⁻¹ * ∫ y in Q, (φ y - f x)) := by
      rw [setAverage_eq, smul_eq_mul, integral_sub hi (integrableOn_const hVt), setIntegral_const,
        smul_eq_mul]
      field_simp
      ring
    have habs : ∀ z, |f x - f z - ⟪gradient f z, x - z⟫| = |φ z - f x| := fun z => by
      rw [← abs_neg]; congr 1; simp only [hφdef]; ring
    simp_rw [habs]
    rw [e, abs_neg, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg]
    calc ENNReal.ofReal ((volume.real Q)⁻¹ * |∫ y in Q, (φ y - f x)|)
        ≤ ENNReal.ofReal ((volume.real Q)⁻¹ * ∫ y in Q, |φ y - f x|) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
            (inv_nonneg.2 measureReal_nonneg))
      _ = (volume Q)⁻¹ * ∫⁻ y in Q, ENNReal.ofReal |φ y - f x| := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg),
            ofReal_integral_eq_lintegral_ofReal hint.abs (Eventually.of_forall fun _ => abs_nonneg _),
            measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hQ0 hVt),
            ENNReal.ofReal_toReal hVt]
  -- Steps B–F: the double integral
  have hmeas1 : AEMeasurable (Function.uncurry fun (z : Rd d) (t : ℝ) =>
      ENNReal.ofReal t * g (x + t • (z - x)) * ‖z - x‖ₑ ^ 2)
      ((volume.restrict Q).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : Rd d × ℝ => ENNReal.ofReal p.2 * g (x + p.2 • (p.1 - x)) * ‖p.1 - x‖ₑ ^ 2
    exact ((ENNReal.measurable_ofReal.comp measurable_snd).mul
      (hgm.comp (continuous_const.add (continuous_snd.smul
      (continuous_fst.sub continuous_const))).measurable)).mul
      ((continuous_enorm.comp (continuous_fst.sub continuous_const)).measurable.pow_const 2)
  set F : Rd d → ℝ → ℝ≥0∞ := fun z s =>
    G z * {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s
    with hFdef
  have hmeas2 : AEMeasurable (Function.uncurry F)
      ((volume.restrict Q).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    have hS : MeasurableSet {p : Rd d × ℝ | dist p.1 x ≤ p.2 * D} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h1 : Measurable fun p : Rd d × ℝ => G p.1 :=
      (hgm.mul ((continuous_enorm.comp (continuous_id.sub continuous_const)).measurable.pow_const 2)).comp
        measurable_fst
    have h2 : Measurable fun p : Rd d × ℝ => ENNReal.ofReal (p.2 ^ (-(d : ℝ) - 1)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    exact h1.mul (h2.indicator hS)
  have hFeq : ∀ s z, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
      {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z = F z s := by
    intro s z
    by_cases h : dist z x ≤ s * D
    · rw [hFdef]; simp only [indicator_of_mem (show z ∈ {z | dist z x ≤ s * D} from h),
        indicator_of_mem (show s ∈ {s : ℝ | dist z x ≤ s * D} from h), hGdef]
      ring
    · rw [hFdef]; simp only [indicator_of_notMem (show z ∉ {z | dist z x ≤ s * D} from h),
        indicator_of_notMem (show s ∉ {s : ℝ | dist z x ≤ s * D} from h), mul_zero]
  have hpow : ∀ s ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal s * ENNReal.ofReal (s ^ (-(d : ℝ) - 2)) =
      ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) := by
    intro s hs
    rw [← ENNReal.ofReal_mul hs.1.le]
    congr 1
    rw [show -(d : ℝ) - 1 = 1 + (-(d : ℝ) - 2) by ring, Real.rpow_add hs.1, Real.rpow_one]
  have stepBF : ∫⁻ z in Q, ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫| ≤
      ∫⁻ z in Q, G z * ∫⁻ s in Ioc (0 : ℝ) 1,
        {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s := by
    calc ∫⁻ z in Q, ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫|
        ≤ ∫⁻ z in Q, ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal t * g (x + t • (z - x)) * ‖z - x‖ₑ ^ 2 :=
          lintegral_mono fun z => abs_taylor_le hf x z
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in Q, ENNReal.ofReal t * g (x + t • (z - x)) * ‖z - x‖ₑ ^ 2 :=
          lintegral_lintegral_swap hmeas1
      _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
            ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ ^ 2) z := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          simp_rw [mul_assoc]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hpow s hs, mul_assoc]
          exact mul_le_mul' le_rfl (lintegral_comp_homothety_sq_le hQ hQm hx hD hgm hs)
      _ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ z in Q, F z s := by
          refine lintegral_congr fun s => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun z => hFeq s z
      _ = ∫⁻ z in Q, ∫⁻ s in Ioc (0 : ℝ) 1, F z s := (lintegral_lintegral_swap hmeas2).symm
      _ = _ := by
          refine lintegral_congr fun z => ?_
          rw [hFdef]
          exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top
            (ENNReal.pow_ne_top enorm_ne_top))
  -- Step G: the radial integral
  have hdiam : ENNReal.ofReal D = Metric.ediam Q := by
    rw [hDdef, Metric.diam, ENNReal.ofReal_toReal hQb.ediam_ne_top]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have stepG : ∀ z ∈ Q, G z * ∫⁻ s in Ioc (0 : ℝ) 1,
        {s : ℝ | dist z x ≤ s * D}.indicator (fun s => ENNReal.ofReal (s ^ (-(d : ℝ) - 1))) s ≤
      C * (‖fderiv ℝ (fderiv ℝ f) z‖ₑ / edist x z ^ ((d : ℝ) - 2)) := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [hGdef]
    have hr : 0 < dist z x := dist_pos.2 hzx
    have hDpos : 0 < D := hr.trans_le (hD z hz)
    refine (mul_le_mul' le_rfl (theorem_2_1_first.lintegral_Ioc_rpow_indicator_le hd hDpos hr)).trans (le_of_eq ?_)
    set r := dist z x
    have h1 : ‖z - x‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
      rw [← ofReal_norm, ← dist_eq_norm, ENNReal.ofReal_pow dist_nonneg]
    have h2 : edist x z ^ ((d : ℝ) - 2) = ENNReal.ofReal (r ^ ((d : ℝ) - 2)) := by
      rw [edist_dist, dist_comm, ENNReal.ofReal_rpow_of_pos hr]
    have h3 : C = ENNReal.ofReal (D ^ d / d) := by
      rw [hCdef, ← hdiam, ENNReal.ofReal_rpow_of_nonneg hDpos.le hdpos.le, Real.rpow_natCast,
        ENNReal.ofReal_div_of_pos hdpos, ENNReal.ofReal_natCast]
    simp only [hGdef, g]
    rw [h1, h2, h3]
    have hDd : 0 ≤ D ^ d / d := div_nonneg (pow_nonneg hDpos.le _) hdpos.le
    have eR : ENNReal.ofReal (D ^ d / d) *
        (‖fderiv ℝ (fderiv ℝ f) z‖ₑ / ENNReal.ofReal (r ^ ((d : ℝ) - 2))) =
        ‖fderiv ℝ (fderiv ℝ f) z‖ₑ * ENNReal.ofReal (D ^ d / d * (r ^ ((d : ℝ) - 2))⁻¹) := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _),
        ← mul_assoc, ← ENNReal.ofReal_mul hDd, mul_comm]
    rw [eR, mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]
    congr 2
    rw [Real.rpow_neg hr.le, Real.rpow_sub hr, Real.rpow_two]
    simp only [Real.rpow_natCast]
    field_simp
  -- Assemble
  calc ENNReal.ofReal |f x - ⨍ z in Q, (f z + ⟪gradient f z, x - z⟫)|
      ≤ (volume Q)⁻¹ * ∫⁻ z in Q, ENNReal.ofReal |f x - f z - ⟪gradient f z, x - z⟫| := stepA
    _ ≤ (volume Q)⁻¹ * ∫⁻ z in Q, C * (‖fderiv ℝ (fderiv ℝ f) z‖ₑ / edist x z ^ ((d : ℝ) - 2)) :=
        mul_le_mul' le_rfl (stepBF.trans (setLIntegral_mono_ae' hQm
          (Eventually.of_forall fun z hz => stepG z hz)))
    _ = Metric.ediam Q ^ (d : ℝ) / (d * volume Q) *
          ∫⁻ z in Q, ‖fderiv ℝ (fderiv ℝ f) z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_lt_top
          (ENNReal.rpow_ne_top_of_nonneg hdpos.le hQb.ediam_ne_top)
          (by exact_mod_cast hd.ne')).ne, ← mul_assoc]
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (by exact_mod_cast hd.ne'))
          (Or.inl (ENNReal.natCast_ne_top d))]
        ring

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the coordinates `∂_i f` of the weak
gradient have weak gradient `(∂_j ∂_i f)_j` read off the weak Hessian). -/
theorem isWeakGradient_coord {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) (i : Fin d) :
    IsWeakGradient (fun z => Rd.coord i (G z))
      (fun z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • Rd.basisVec j) := by
  intro j
  have hcoord : (fun z => Rd.coord j (∑ k, Rd.coord i (H z (Rd.basisVec k)) • Rd.basisVec k)) =
      fun z => Rd.coord i (H z (Rd.basisVec j)) := by
    funext z
    simp [Rd.coord, Rd.basisVec, sum_inner, inner_smul_left, EuclideanSpace.inner_single_right]
  rw [hcoord]
  obtain ⟨hfl, hGl, hGw⟩ := hG i
  obtain ⟨-, hHl, hHw⟩ := hH i j
  refine ⟨hGl, hHl, fun φ hφ hφc => ?_⟩
  have hord1 : ∀ k : Fin d, IsWeakDerivative.order (Pi.single k 1 : Fin d → ℕ) = 1 := by
    intro k; simp [IsWeakDerivative.order]
  have hord2 : IsWeakDerivative.order (Pi.single i 1 + Pi.single j 1 : Fin d → ℕ) = 2 := by
    simp [IsWeakDerivative.order, Finset.sum_add_distrib]
  set ψ : Rd d → ℝ := fun y => fderiv ℝ φ y (Rd.basisVec j) with hψ
  have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl).clm_apply contDiff_const
  have hψc : HasCompactSupport ψ := hφc.fderiv_apply (𝕜 := ℝ) _
  have h1 := hGw ψ hψs hψc
  have h2 := hHw φ hφ hφc
  rw [hord2] at h2
  rw [hord1]
  have e1 : (fun x => f x * IsWeakDerivative.testDeriv (Pi.single i 1) ψ x) =
      fun x => f x * IsWeakDerivative.testDeriv (Pi.single i 1 + Pi.single j 1) φ x := by
    funext x
    rw [theorem_2_1_first.testDeriv_single, PathwiseSobolevSpace.testDeriv_single_add_single hφ]
  have e2 : (fun x => Rd.coord i (G x) * IsWeakDerivative.testDeriv (Pi.single j 1) φ x) =
      fun x => Rd.coord i (G x) * ψ x := by
    funext x; rw [theorem_2_1_first.testDeriv_single]
  rw [e1, h2, hord1] at h1
  rw [e2]
  simp only [pow_one, neg_one_mul, even_two, Even.neg_one_pow, one_mul] at h1 ⊢
  linarith

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the Hessian entries are integrable). -/
theorem coord_hessian_integrable {f : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hf : MemW 2 1 f) (hH : IsWeakHessian f H) (i j : Fin d) :
    Integrable fun z => Rd.coord i (H z (Rd.basisVec j)) := by
  set α : Fin d → ℕ := Pi.single i 1 + Pi.single j 1 with hα
  have hord : IsWeakDerivative.order α ≤ 2 := by
    simp [hα, IsWeakDerivative.order, Finset.sum_add_distrib]
  obtain ⟨g, hg, hgL⟩ := hf.2 _ hord
  obtain ⟨_, hgl, hgi⟩ := hg
  obtain ⟨_, hgl', hgi'⟩ := hH i j
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgl.sub hgl') fun φ hφ hφc => by
    have hne : ((-1 : ℝ) ^ IsWeakDerivative.order α) ≠ 0 := pow_ne_zero _ (by norm_num)
    have heq : ∫ x, g x * φ x = ∫ x, Rd.coord i (H x (Rd.basisVec j)) * φ x :=
      mul_left_cancel₀ hne ((hgi φ hφ hφc).symm.trans (hgi' φ hφ hφc))
    have hi : Integrable (fun x => φ x • g x) :=
      hgl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hi' : Integrable (fun x => φ x • Rd.coord i (H x (Rd.basisVec j))) :=
      hgl'.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi hi']
    simp only [smul_eq_mul, mul_comm (φ _)]
    rw [heq, sub_self]
  have hae : g =ᵐ[volume] fun z => Rd.coord i (H z (Rd.basisVec j)) := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  exact (memLp_one_iff_integrable.1 hgL).congr hae

/-- **Subgoal** (Theorem 2.1 proof, second estimate: `∂_i f ∈ W^{1,1}`). -/
theorem memW_coord {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hf : MemW 2 1 f) (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) (i : Fin d) :
    MemW 1 1 (fun z => Rd.coord i (G z)) := by
  have hf1 : MemW 1 1 f := ⟨hf.1, fun α h => hf.2 α (h.trans (by norm_num))⟩
  have hGi := theorem_2_1_first.coord_integrable hf1 hG i
  refine ⟨memLp_one_iff_integrable.2 hGi, fun α hα => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
  · -- `α = 0`: the function itself
    have hα0 : α = 0 := by
      funext k
      exact (Finset.sum_eq_zero_iff.1 h0) k (Finset.mem_univ k)
    subst hα0
    refine ⟨fun z => Rd.coord i (G z), ⟨hGi.locallyIntegrable, hGi.locallyIntegrable,
      fun φ _ _ => ?_⟩, memLp_one_iff_integrable.2 hGi⟩
    have hdir : IsWeakDerivative.directions (0 : Fin d → ℕ) = [] := by
      simp [IsWeakDerivative.directions]
    have ht : ∀ x, IsWeakDerivative.testDeriv (0 : Fin d → ℕ) φ x = φ x := by
      intro x
      unfold IsWeakDerivative.testDeriv
      rw [hdir]
      simp
    simp only [ht]
    simp [IsWeakDerivative.order]
  · -- `α = e_j`
    have hex : ∃ j, α j ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have : IsWeakDerivative.order α = 0 := Finset.sum_eq_zero fun k _ => hne k
      omega
    obtain ⟨j, hj⟩ := hex
    have hsplit := Finset.add_sum_erase Finset.univ α (Finset.mem_univ j)
    have hsum : α j + ∑ k ∈ Finset.univ.erase j, α k = 1 := by
      rw [hsplit]; exact h1
    have hαj : α j = 1 := by omega
    have hrest : ∑ k ∈ Finset.univ.erase j, α k = 0 := by omega
    have hαe : α = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [hαj]
      · rw [Pi.single_eq_of_ne hk]
        exact (Finset.sum_eq_zero_iff.1 hrest) k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    subst hαe
    refine ⟨_, isWeakGradient_coord hG hH i j, ?_⟩
    have hcoord : (fun z => Rd.coord j (∑ k, Rd.coord i (H z (Rd.basisVec k)) • Rd.basisVec k)) =
        fun z => Rd.coord i (H z (Rd.basisVec j)) := by
      funext z
      simp [Rd.coord, Rd.basisVec, sum_inner, inner_smul_left, EuclideanSpace.inner_single_right]
    rw [hcoord]
    exact memLp_one_iff_integrable.2 (coord_hessian_integrable hf hH i j)

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the mollification of a `W^{2,1}`
function is `C²`, with second derivatives the mollified weak Hessian entries). -/
theorem hessian_convolution {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) {ψ : Rd d → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiff ℝ 2 (fun x => ∫ y, f y * ψ (x - y)) ∧
      ∀ w i j, fderiv ℝ (fderiv ℝ (fun x => ∫ y, f y * ψ (x - y))) w (Rd.basisVec i)
          (Rd.basisVec j) = ∫ y, Rd.coord j (H y (Rd.basisVec i)) * ψ (w - y) := by
  set F : Rd d → ℝ := fun x => ∫ y, f y * ψ (x - y) with hF
  set c : Fin d → Rd d → ℝ := fun i x => ∫ y, Rd.coord i (G y) * ψ (x - y) with hc
  obtain ⟨hF1, hFg⟩ := theorem_2_1_first.contDiff_convolution hG hψ hψc
  have hfg : ∀ (g : Rd d → ℝ) w v, fderiv ℝ g w v = ⟪gradient g w, v⟫ := by
    intro g w v
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hcoordsum : ∀ (a : Fin d → ℝ) (v : Rd d),
      ⟪∑ i, a i • Rd.basisVec i, v⟫ = ∑ i, a i * Rd.coord i v := by
    intro a v
    simp [sum_inner, inner_smul_left, Rd.coord, real_inner_comm]
  have hFd : ∀ x v, fderiv ℝ F x v = ∑ i, c i x * Rd.coord i v := by
    intro x v
    rw [hfg, hFg x, hcoordsum]
  have hci : ∀ j, ContDiff ℝ 1 (c j) ∧ ∀ x, gradient (c j) x =
      ∑ k, (∫ y, Rd.coord k (∑ l, Rd.coord j (H y (Rd.basisVec l)) • Rd.basisVec l) *
        ψ (x - y)) • Rd.basisVec k :=
    fun j => theorem_2_1_first.contDiff_convolution (isWeakGradient_coord hG hH j) hψ hψc
  have hcoord : ∀ (a : Fin d → ℝ) k, Rd.coord k (∑ l, a l • Rd.basisVec l) = a k := by
    intro a k
    simp [Rd.coord, Rd.basisVec, sum_inner, inner_smul_left, EuclideanSpace.inner_single_right]
  have hbasis : ∀ i j : Fin d, Rd.coord i (Rd.basisVec j) = if i = j then 1 else 0 := by
    intro i j
    simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]
  have hFe : ∀ j, (fun x => fderiv ℝ F x (Rd.basisVec j)) = c j := by
    intro j; funext x
    rw [hFd]
    simp [hbasis]
  have hC2 : ContDiff ℝ 2 F := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv_apply]
    refine ⟨hF1.differentiable one_ne_zero, by simp, fun v => ?_⟩
    have : (fun x => fderiv ℝ F x v) = fun x => ∑ i, c i x * Rd.coord i v := by
      funext x; exact hFd x v
    rw [this]
    exact ContDiff.sum fun i _ => (hci i).1.mul contDiff_const
  refine ⟨hC2, fun w i j => ?_⟩
  · have hdiff : Differentiable ℝ (fderiv ℝ F) :=
      (hC2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have happ := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ F) (u := fun _ : Rd d => Rd.basisVec j)
      (x := w) (hdiff w) (differentiableAt_const _)
    have e1 : fderiv ℝ (fderiv ℝ F) w (Rd.basisVec i) (Rd.basisVec j) =
        fderiv ℝ (fun y => fderiv ℝ F y (Rd.basisVec j)) w (Rd.basisVec i) := by
      rw [happ]; simp
    rw [e1, hFe j, hfg, (hci j).2 w, hcoordsum]
    simp only [hcoord, hbasis]
    simp

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the weak Hessian of a `W^{2,1}` function
is integrable as an operator-valued map). -/
theorem integrable_hessian {f : Rd d → ℝ} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hf : MemW 2 1 f) (hH : IsWeakHessian f H) : Integrable H := by
  have hexp : ∀ w : Rd d, w = ∑ i, Rd.coord i w • Rd.basisVec i := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  set E : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j =>
    (innerSL ℝ (Rd.basisVec i)).smulRight (Rd.basisVec j) with hE
  have hz : H = fun z => ∑ i, ∑ j, Rd.coord j (H z (Rd.basisVec i)) • E i j := by
    funext z
    ext1 v
    calc H z v = H z (∑ i, Rd.coord i v • Rd.basisVec i) := by rw [← hexp v]
      _ = ∑ i, Rd.coord i v • H z (Rd.basisVec i) := by simp [map_sum, map_smul]
      _ = ∑ i, Rd.coord i v • ∑ j, Rd.coord j (H z (Rd.basisVec i)) • Rd.basisVec j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hexp]
      _ = _ := by
          simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hE,
            ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Finset.smul_sum, smul_smul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [Rd.coord, real_inner_comm, mul_comm]
  rw [hz]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (coord_hessian_integrable hf hH j i).smul_const _

/-- **Subgoal** (Theorem 2.1 proof, second estimate: a bilinear form is bounded by the sum of
its entries in the standard basis). -/
theorem norm_le_sum_entries (A : Rd d →L[ℝ] Rd d →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A (Rd.basisVec i) (Rd.basisVec j)| := by
  have hexp : ∀ v : Rd d, v = ∑ i, Rd.coord i v • Rd.basisVec i := by
    intro v
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' v]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hcv : ∀ (i : Fin d) (v : Rd d), |Rd.coord i v| ≤ ‖v‖ := by
    intro i v
    have h := abs_real_inner_le_norm v (Rd.basisVec i)
    have hb : ‖Rd.basisVec i‖ = 1 := by simp [Rd.basisVec]
    rw [hb, mul_one] at h
    exact h
  have key : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Rd d →L[ℝ] F),
      ‖L‖ ≤ ∑ i, ‖L (Rd.basisVec i)‖ := by
    intro F _ _ L
    refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
    conv_lhs => rw [hexp v]
    rw [map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcv i v) (norm_nonneg _)
  refine (key _ A).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (key ℝ (A (Rd.basisVec i))).trans (le_of_eq ?_)
  simp [Real.norm_eq_abs]

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the local Riesz potential of order `2`
is bounded on `L¹(Q)`). -/
theorem lintegral_potential2_le (hd : 0 < d) {Q : Set (Rd d)} (hQb : Bornology.IsBounded Q)
    (hQm : MeasurableSet Q) :
    ∃ C : ℝ≥0, ∀ h : Rd d → ℝ, AEStronglyMeasurable h →
      ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2) ≤ C * ∫⁻ z in Q, ‖h z‖ₑ := by
  obtain ⟨C0, -, hC0⟩ := lemma_2_2 d (α := 2) two_pos
  set D : ℝ := Metric.diam Q + 1 with hDdef
  have hD : 0 < D := by positivity
  refine ⟨C0 * ((2 * D) ^ (2 : ℝ)).toNNReal, fun h hh => ?_⟩
  set C : ℝ≥0∞ := ((C0 * ((2 * D) ^ (2 : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) with hCdef
  -- the kernel integral is uniformly bounded on `Q`
  have hK : ∀ z ∈ Q, ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 2) ≤ C := by
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
    calc ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 2)
        ≤ ∫⁻ y in Metric.closedBall z D, 1 / edist y z ^ ((d : ℝ) - 2) := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.closedBall z D, ‖(fun _ : Rd d => (1 : ℝ)) y‖ₑ / edist z y ^ ((d : ℝ) - 2) := by
          simp only [enorm_one, edist_comm]
      _ ≤ C0 * Metric.ediam (Metric.closedBall z D) ^ (2 : ℝ) *
            localMaximalFunction (Metric.ediam (Metric.closedBall z D)) (fun _ => (1 : ℝ)) z := hlem
      _ ≤ C0 * ENNReal.ofReal (2 * D) ^ (2 : ℝ) * 1 := by gcongr
      _ = C := by
          rw [mul_one, hCdef, ENNReal.coe_mul, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ENNReal.ofReal]
  have hm : AEMeasurable (Function.uncurry fun (y z : Rd d) => ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2))
      ((volume.restrict Q).prod (volume.restrict Q)) := by
    have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖h p.2‖ₑ)
        ((volume.restrict Q).prod (volume.restrict Q)) :=
      hh.restrict.aemeasurable.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable fun p : Rd d × Rd d => edist p.1 p.2 ^ ((d : ℝ) - 2) :=
      (continuous_edist.measurable).pow_const _
    exact h1.div h2.aemeasurable
  calc ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2)
      = ∫⁻ z in Q, ∫⁻ y in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2) := lintegral_lintegral_swap hm
    _ = ∫⁻ z in Q, ‖h z‖ₑ * ∫⁻ y in Q, 1 / edist y z ^ ((d : ℝ) - 2) := by
        refine lintegral_congr fun z => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun y => ?_
        rw [div_eq_mul_inv, one_div]
    _ ≤ ∫⁻ z in Q, ‖h z‖ₑ * C := by
        refine lintegral_mono_ae ((ae_restrict_iff' hQm).2 (Eventually.of_forall fun z hz => ?_))
        exact mul_le_mul' le_rfl (hK z hz)
    _ = C * ∫⁻ z in Q, ‖h z‖ₑ := by
        rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, mul_comm]

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `m = 2` almost everywhere on `Q`
for `W^{2,1}` functions, by mollification). -/
theorem poincare2_ae (hd : 0 < d) : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)), MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H →
      ∀ Q : Set (Rd d), IsCubeOrBall Q →
        ∀ᵐ y ∂volume, y ∈ Q → ENNReal.ofReal |f y - ⨍ z in Q, (f z + ⟪G z, y - z⟫)| ≤
          K * ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2) := by
  obtain ⟨K0, hK0⟩ := theorem_2_1_first.isCubeOrBall_props hd
  obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ := theorem_2_1_first.exists_mollifier (d := d)
  refine ⟨K0 * (d : ℝ≥0) ^ 2, fun f G H hf hG hH Q hQ => ?_⟩
  obtain ⟨hQc, hQm, hQb, hQ0, hQK⟩ := hK0 Q hQ
  have hQt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hf1 : MemW 1 1 f := ⟨hf.1, fun α h => hf.2 α (h.trans (by norm_num))⟩
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) :=
    theorem_2_1_first.coord_integrable hf1 hG
  have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGint : Integrable G := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext hexpG
    rw [this]
    exact integrable_finset_sum _ fun i _ => (hGi i).smul_const _
  -- Hessian entries and measurable versions
  set Hc : Fin d → Fin d → Rd d → ℝ := fun i j z => Rd.coord j (H z (Rd.basisVec i)) with hHcdef
  have hHi : ∀ i j, Integrable (Hc i j) := fun i j => coord_hessian_integrable hf hH j i
  set Hc' : Fin d → Fin d → Rd d → ℝ := fun i j => (hHi i j).aestronglyMeasurable.mk (Hc i j)
    with hHc'def
  have hHc'm : ∀ i j, Measurable (Hc' i j) := fun i j =>
    (hHi i j).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hHcae : ∀ᵐ z ∂volume, ∀ i j, Hc i j z = Hc' i j z := by
    have : ∀ i j, ∀ᵐ z ∂volume, Hc i j z = Hc' i j z := fun i j =>
      (hHi i j).aestronglyMeasurable.ae_eq_mk
    simpa only [ae_all_iff] using this
  have hHnorm : ∀ i j z, |Hc i j z| ≤ ‖H z‖ := by
    intro i j z
    have hb : ∀ k : Fin d, ‖Rd.basisVec k‖ = 1 := fun k => by simp [Rd.basisVec]
    have h1 := abs_real_inner_le_norm (H z (Rd.basisVec i)) (Rd.basisVec j)
    rw [hb, mul_one] at h1
    exact h1.trans ((H z).le_opNorm _ |>.trans (by rw [hb, mul_one]))
  -- the mollified functions
  set F : ℕ → Rd d → ℝ := fun n x => ∫ y, f y * ψ n (x - y) with hFdef
  have hF2 := fun n => hessian_convolution hG hH (hψ n) (hψc n)
  have hFc : ∀ n, ContDiff ℝ 1 (F n) := fun n => (theorem_2_1_first.contDiff_convolution hG (hψ n) (hψc n)).1
  have hgradc : ∀ n, Continuous (gradient (F n)) := fun n =>
    (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp ((hFc n).continuous_fderiv one_ne_zero)
  set cv : ℕ → Fin d → Fin d → Rd d → ℝ := fun n i j z => ∫ y, Hc i j y * ψ n (z - y) with hcvdef
  have hcvc : ∀ n i j, Continuous (cv n i j) := by
    intro n i j
    have : cv n i j = convolution (Hc i j) (ψ n) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext z; simp [hcvdef, convolution_def, smul_eq_mul]
    rw [this]
    exact (hψc n).continuous_convolution_right _ (hHi i j).locallyIntegrable (hψ n).continuous
  set T : ℕ → Rd d → ℝ := fun n z => ∑ i, ∑ j, |cv n i j z - Hc' i j z| with hTdef
  have hT0 : ∀ n z, 0 ≤ T n z := fun n z =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hTm : ∀ n, Measurable (T n) := fun n =>
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (((hcvc n i j).measurable.sub (hHc'm i j))).abs
  set e : ℝ := (d : ℝ) - 2 with he
  set P : ℕ → Rd d → ℝ≥0∞ := fun n y => ∫⁻ z in Q, ‖T n z‖ₑ / edist y z ^ e with hPdef
  have hPm : ∀ n, Measurable (P n) := by
    intro n
    have hm : Measurable fun p : Rd d × Rd d => ‖T n p.2‖ₑ / edist p.1 p.2 ^ e :=
      (((hTm n).enorm).comp measurable_snd).div ((continuous_edist.measurable).pow_const _)
    exact hm.lintegral_prod_right'
  set S : ℕ → Rd d → ℝ≥0∞ := fun n y => ‖F n y - f y‖ₑ + P n y with hSdef
  have hSm : ∀ n, AEMeasurable (S n) (volume.restrict Q) := fun n =>
    ((((hFc n).continuous.measurable.aemeasurable.sub hfi.aemeasurable).enorm).add
      (hPm n).aemeasurable).restrict
  -- `L¹` convergence
  obtain ⟨CQ, hCQ⟩ := lintegral_potential2_le hd hQb hQm
  have hA := theorem_2_1_first.tendsto_convolution hfi hψ0 (fun n => (hψ n).continuous) hψ1 hψs
  have hB := theorem_2_1_first.tendsto_lintegral_gradient hf1 hG hψ hψc hψ0 hψ1 hψs
  have hTlim : Tendsto (fun n => ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc i j z‖ₑ) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
        theorem_2_1_first.tendsto_convolution (hHi i j) hψ0 (fun n => (hψ n).continuous) hψ1 hψs
    simpa [hcvdef] using this
  have hTle : ∀ n, ∫⁻ z, ‖T n z‖ₑ ≤ ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc i j z‖ₑ := by
    intro n
    calc ∫⁻ z, ‖T n z‖ₑ ≤ ∫⁻ z, ∑ i, ∑ j, ‖cv n i j z - Hc' i j z‖ₑ := by
          refine lintegral_mono fun z => ?_
          refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (enorm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          simp [Real.enorm_eq_ofReal_abs]
      _ = ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc' i j z‖ₑ := by
          rw [lintegral_finsetSum' Finset.univ (f := fun i z => ∑ j, ‖cv n i j z - Hc' i j z‖ₑ)
            fun i _ => (Finset.measurable_sum _ fun j _ =>
              (((hcvc n i j).measurable.sub (hHc'm i j)).enorm)).aemeasurable]
          refine Finset.sum_congr rfl fun i _ => ?_
          exact lintegral_finsetSum' _ fun j _ =>
            (((hcvc n i j).measurable.sub (hHc'm i j)).enorm).aemeasurable
      _ = ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc i j z‖ₑ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          refine lintegral_congr_ae (hHcae.mono fun z hz => ?_)
          simp only [hz]
  have hSint : Tendsto (fun n => ∫⁻ y in Q, S n y) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => (∫⁻ x, ‖F n x - f x‖ₑ) +
        CQ * ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc i j z‖ₑ) atTop (𝓝 (0 + (CQ : ℝ≥0∞) * 0)) :=
      hA.add (ENNReal.Tendsto.const_mul hTlim (Or.inr ENNReal.coe_ne_top))
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => zero_le)
      fun n => ?_
    have hpot := hCQ (T n) (hTm n).aestronglyMeasurable
    calc ∫⁻ y in Q, S n y
        = (∫⁻ y in Q, ‖F n y - f y‖ₑ) + ∫⁻ y in Q, P n y := by
          have hm1 : AEMeasurable (fun y => ‖F n y - f y‖ₑ) (volume.restrict Q) :=
            (((hFc n).continuous.measurable.aemeasurable.sub hfi.aemeasurable).enorm).restrict
          simp only [hSdef]
          rw [lintegral_add_left' hm1]
      _ ≤ (∫⁻ x, ‖F n x - f x‖ₑ) + CQ * ∑ i, ∑ j, ∫⁻ z, ‖cv n i j z - Hc i j z‖ₑ := by
          refine add_le_add (setLIntegral_le_lintegral _ _) ?_
          exact hpot.trans (mul_le_mul' le_rfl ((setLIntegral_le_lintegral _ _).trans (hTle n)))
  obtain ⟨φ, hφmono, hφ⟩ := theorem_2_1_first.exists_subseq_ae_tendsto_zero hSm hSint
  -- convergence of the averaged Taylor polynomials
  set D : ℝ := Metric.diam Q with hDdef
  have hDQ : ∀ y ∈ Q, ∀ z ∈ Q, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hQb hy hz
  have hinnerG : ∀ y ∈ Q, IntegrableOn (fun z => ⟪G z, y - z⟫) Q := by
    intro y hy
    refine Integrable.mono' (hGint.integrableOn.norm.mul_const D)
      ((hGint.aestronglyMeasurable.inner
        (continuous_const.sub continuous_id).aestronglyMeasurable).restrict) ?_
    refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hDQ y hy z hz) (norm_nonneg _))
  have hFi : ∀ n y, IntegrableOn (fun z => F n z + ⟪gradient (F n) z, y - z⟫) Q := by
    intro n y
    have hc : Continuous fun z => F n z + ⟪gradient (F n) z, y - z⟫ :=
      (hFc n).continuous.add ((hgradc n).inner (continuous_const.sub continuous_id))
    exact (hc.continuousOn.integrableOn_compact hQb.isCompact_closure).mono_set subset_closure
  have hav : ∀ y ∈ Q, Tendsto (fun n => ⨍ z in Q, (F n z + ⟪gradient (F n) z, y - z⟫)) atTop
      (𝓝 (⨍ z in Q, (f z + ⟪G z, y - z⟫))) := by
    intro y hy
    have hgi : IntegrableOn (fun z => f z + ⟪G z, y - z⟫) Q := hfi.integrableOn.add (hinnerG y hy)
    rw [tendsto_iff_edist_tendsto_0]
    have hlim : Tendsto (fun n => (volume Q)⁻¹ * ((∫⁻ x, ‖F n x - f x‖ₑ) +
        ENNReal.ofReal D * ∫⁻ z, ‖gradient (F n) z - G z‖ₑ)) atTop
        (𝓝 ((volume Q)⁻¹ * (0 + ENNReal.ofReal D * 0))) :=
      ENNReal.Tendsto.const_mul (hA.add (ENNReal.Tendsto.const_mul hB (Or.inr ENNReal.ofReal_ne_top)))
        (Or.inr (ENNReal.inv_ne_top.2 hQ0))
    rw [mul_zero, add_zero, mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      fun n => ?_
    rw [edist_dist, Real.dist_eq, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub,
      ← integral_sub (hFi n y) hgi, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg,
      ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg), measureReal_def,
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hQ0 hQt), ENNReal.ofReal_toReal hQt]
    refine mul_le_mul' le_rfl ?_
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hm1 : AEMeasurable (fun x => ‖F n x - f x‖ₑ) (volume.restrict Q) :=
      (((hFc n).continuous.measurable.aemeasurable.sub hfi.aemeasurable).enorm).restrict
    calc ∫⁻ z in Q, ‖F n z + ⟪gradient (F n) z, y - z⟫ - (f z + ⟪G z, y - z⟫)‖ₑ
        ≤ ∫⁻ z in Q, (‖F n z - f z‖ₑ + ENNReal.ofReal D * ‖gradient (F n) z - G z‖ₑ) := by
          refine setLIntegral_mono_ae' hQm (Eventually.of_forall fun z hz => ?_)
          have hsplit : F n z + ⟪gradient (F n) z, y - z⟫ - (f z + ⟪G z, y - z⟫) =
              (F n z - f z) + ⟪gradient (F n) z - G z, y - z⟫ := by
            rw [inner_sub_left]; ring
          rw [hsplit]
          refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by
            exact Metric.diam_nonneg), mul_comm D]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hDQ y hy z hz) (norm_nonneg _))
      _ = (∫⁻ z in Q, ‖F n z - f z‖ₑ) + ENNReal.ofReal D * ∫⁻ z in Q, ‖gradient (F n) z - G z‖ₑ := by
          rw [lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _)
          (mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _))
  -- the constant of `poincare2_of_contDiff`
  have hcQ : Metric.ediam Q ^ (d : ℝ) / (d * volume Q) ≤ K0 := by
    refine ENNReal.div_le_of_le_mul (hQK.trans ?_)
    rw [mul_comm (d : ℝ≥0∞), ← mul_assoc]
    refine le_mul_of_one_le_right' ?_
    exact_mod_cast hd
  -- pointwise Hessian bound
  have hHess : ∀ n z, (∀ i j, Hc i j z = Hc' i j z) →
      ‖fderiv ℝ (fderiv ℝ (F n)) z‖ₑ ≤ (d : ℝ≥0∞) ^ 2 * ‖H z‖ₑ + ‖T n z‖ₑ := by
    intro n z hz
    have hreal : ‖fderiv ℝ (fderiv ℝ (F n)) z‖ ≤ (d : ℝ) ^ 2 * ‖H z‖ + T n z := by
      refine (norm_le_sum_entries _).trans ?_
      calc ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ (F n)) z (Rd.basisVec i) (Rd.basisVec j)|
          = ∑ i, ∑ j, |cv n i j z| := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [(hF2 n).2 z i j]
        _ ≤ ∑ i, ∑ j, (‖H z‖ + |cv n i j z - Hc' i j z|) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            have h1 := hHnorm i j z
            rw [hz i j] at h1
            calc |cv n i j z| = |Hc' i j z + (cv n i j z - Hc' i j z)| := by ring_nf
              _ ≤ |Hc' i j z| + |cv n i j z - Hc' i j z| := abs_add_le _ _
              _ ≤ _ := add_le_add h1 le_rfl
        _ = (d : ℝ) ^ 2 * ‖H z‖ + T n z := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, hTdef]
            ring
    rw [← ofReal_norm, Real.enorm_of_nonneg (hT0 n z), ← ofReal_norm (H z)]
    refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (hT0 n z), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  -- conclude
  rw [ae_restrict_iff' hQm] at hφ
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
  have hav' := (hav y hyQ).comp hφmono.tendsto_atTop
  set A : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e with hA
  have hlhs : Tendsto (fun k => ENNReal.ofReal |F (φ k) y -
      ⨍ z in Q, (F (φ k) z + ⟪gradient (F (φ k)) z, y - z⟫)|) atTop
      (𝓝 (ENNReal.ofReal |f y - ⨍ z in Q, (f z + ⟪G z, y - z⟫)|)) :=
    ENNReal.tendsto_ofReal ((hFy.sub hav').abs)
  have hrhs : Tendsto (fun k => (K0 : ℝ≥0∞) * ((d : ℝ≥0∞) ^ 2 * A + P (φ k) y)) atTop
      (𝓝 ((K0 : ℝ≥0∞) * ((d : ℝ≥0∞) ^ 2 * A + 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h2) (Or.inr ENNReal.coe_ne_top)
  rw [add_zero] at hrhs
  have hfin : (K0 : ℝ≥0∞) * ((d : ℝ≥0∞) ^ 2 * A) = ((K0 * (d : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) * A := by
    push_cast; ring
  rw [hfin] at hrhs
  refine le_of_tendsto_of_tendsto' hlhs hrhs fun k => ?_
  have hp := poincare2_of_contDiff hd (hF2 (φ k)).1 hQc hQm hQb hQ0 hyQ
  refine hp.trans (mul_le_mul' hcQ ?_)
  have hPm' : AEMeasurable (fun z => ‖T (φ k) z‖ₑ / edist y z ^ e) (volume.restrict Q) :=
    ((hTm (φ k)).enorm.div
      ((continuous_const.edist continuous_id).measurable.pow_const _)).aemeasurable
  calc ∫⁻ z in Q, ‖fderiv ℝ (fderiv ℝ (F (φ k))) z‖ₑ / edist y z ^ ((d : ℝ) - 2)
      ≤ ∫⁻ z in Q, ((d : ℝ≥0∞) ^ 2 * (‖H z‖ₑ / edist y z ^ e) + ‖T (φ k) z‖ₑ / edist y z ^ e) := by
        refine lintegral_mono_ae (ae_restrict_of_ae (hHcae.mono fun z hz => ?_))
        rw [mul_div_assoc', ← ENNReal.add_div]
        exact ENNReal.div_le_div_right (hHess (φ k) z hz) _
    _ = (d : ℝ≥0∞) ^ 2 * A + P (φ k) y := by
        rw [lintegral_add_right' _ hPm', lintegral_const_mul' _ _ (by simp)]

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Lemma 2] with `α = 2`, in the
unified form `⨍_{B(x,r)} |y - z|^{2-d} ≤ C (r + |x - z|)^{2-d}`). -/
theorem lintegral_ball_kernel2_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (x z : Rd d) {r : ℝ}, 0 < r →
    ∫⁻ y in Metric.ball x r, 1 / edist y z ^ ((d : ℝ) - 2) ≤
      C * volume (Metric.ball x r) / (ENNReal.ofReal r + edist x z) ^ ((d : ℝ) - 2) := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · -- `d = 1`: the kernel is `|y - z| ≤ r + |x - z|`
    have hd1' : d = 1 := by omega
    subst hd1'
    refine ⟨1, fun x z r hr => ?_⟩
    have he : ((1 : ℕ) : ℝ) - 2 = -1 := by norm_num
    simp only [he, ENNReal.rpow_neg_one, one_div, inv_inv, ENNReal.coe_one, one_mul]
    calc ∫⁻ y in Metric.ball x r, edist y z
        ≤ ∫⁻ y in Metric.ball x r, (ENNReal.ofReal r + edist x z) := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          refine (edist_triangle y x z).trans (add_le_add ?_ le_rfl)
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (Metric.mem_ball.1 hy).le
      _ = volume (Metric.ball x r) * (ENNReal.ofReal r + edist x z) := by
          rw [setLIntegral_const, mul_comm]
      _ = _ := by rw [div_eq_mul_inv, inv_inv]
  · obtain ⟨C0, -, hC0⟩ := lemma_2_2 d (α := 2) two_pos
    set e : ℝ := (d : ℝ) - 2 with he
    have he0 : 0 ≤ e := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      linarith
    set V := volume (Metric.ball (0 : Rd d) 1) with hV
    have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
    have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
    set Vr : ℝ := V.toReal with hVr
    have hVr0 : 0 < Vr := ENNReal.toReal_pos hV0 hVt
    set Cr : ℝ := (3 : ℝ) ^ e + C0 * 36 * (3 : ℝ) ^ e / Vr with hCr
    have h3e : 0 < (3 : ℝ) ^ e := by positivity
    have hCr0 : 0 ≤ Cr := by positivity
    refine ⟨Cr.toNNReal, fun x z r hr => ?_⟩
    have hCe : ((Cr.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cr := rfl
    have hvol : volume (Metric.ball x r) = ENNReal.ofReal (r ^ d) * V := by
      rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin]
    set ρ : ℝ := r + dist x z with hρ
    have hρ0 : 0 < ρ := by positivity
    have hE : (ENNReal.ofReal r + edist x z) ^ e = ENNReal.ofReal (ρ ^ e) := by
      rw [edist_dist, ← ENNReal.ofReal_add hr.le dist_nonneg,
        ENNReal.ofReal_rpow_of_nonneg hρ0.le he0]
    rw [hE]
    rcases le_or_gt (2 * r) (dist x z) with hfar | hnear
    · -- far case: `|y - z| ≥ (r + |x - z|) / 3` on the ball
      have hpt : ∀ y ∈ Metric.ball x r, 1 / edist y z ^ e ≤ ENNReal.ofReal ((3 : ℝ) ^ e / ρ ^ e) := by
        intro y hy
        have hyz : ρ / 3 ≤ dist y z := by
          have := dist_triangle x y z
          have hxy : dist x y < r := by rw [dist_comm]; exact Metric.mem_ball.1 hy
          rw [hρ]; linarith
        have hpos : 0 < ρ / 3 := by positivity
        rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg he0, one_div,
          ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (hpos.trans_le hyz) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (dist y z ^ e)⁻¹ ≤ ((ρ / 3) ^ e)⁻¹ :=
              inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hyz he0)
          _ = (3 : ℝ) ^ e / ρ ^ e := by
              rw [Real.div_rpow hρ0.le (by norm_num), inv_div]
      calc ∫⁻ y in Metric.ball x r, 1 / edist y z ^ e
          ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal ((3 : ℝ) ^ e / ρ ^ e) :=
            setLIntegral_mono' measurableSet_ball hpt
        _ = ENNReal.ofReal ((3 : ℝ) ^ e / ρ ^ e) * volume (Metric.ball x r) :=
            setLIntegral_const _ _
        _ ≤ ENNReal.ofReal Cr * volume (Metric.ball x r) / ENNReal.ofReal (ρ ^ e) := by
            rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hρ0 _), div_eq_mul_inv,
              div_eq_mul_inv, mul_right_comm]
            refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
            rw [hCr]; have : 0 ≤ C0 * 36 * (3 : ℝ) ^ e / Vr := by positivity
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
      have hρ3 : ρ ≤ 3 * r := by rw [hρ]; linarith
      have hE3 : ENNReal.ofReal (ρ ^ e) ≤ ENNReal.ofReal ((3 * r) ^ e) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hρ0.le hρ3 he0)
      have h3r : 0 < (3 * r) ^ e := by positivity
      calc ∫⁻ y in Metric.ball x r, 1 / edist y z ^ e
          ≤ ∫⁻ y in Metric.closedBall z (3 * r), 1 / edist y z ^ e := lintegral_mono_set hsub
        _ = ∫⁻ y in Metric.closedBall z (3 * r),
              ‖(fun _ : Rd d => (1 : ℝ)) y‖ₑ / edist z y ^ ((d : ℝ) - 2) := by
            simp only [enorm_one, edist_comm, he]
        _ ≤ C0 * Metric.ediam (Metric.closedBall z (3 * r)) ^ (2 : ℝ) *
              localMaximalFunction (Metric.ediam (Metric.closedBall z (3 * r)))
                (fun _ => (1 : ℝ)) z := hlem
        _ ≤ C0 * ENNReal.ofReal (2 * (3 * r)) ^ (2 : ℝ) * 1 := by gcongr
        _ = ENNReal.ofReal (C0 * 36 * r ^ 2) := by
            rw [mul_one, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [Real.rpow_two]; ring
        _ ≤ ENNReal.ofReal (Cr * r ^ d * Vr / (3 * r) ^ e) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hrd : r ^ d / (3 * r) ^ e = r ^ 2 / (3 : ℝ) ^ e := by
              rw [Real.mul_rpow (by norm_num) hr.le, he, Real.rpow_sub hr, Real.rpow_natCast,
                Real.rpow_two]
              field_simp
            rw [show Cr * r ^ d * Vr / (3 * r) ^ e = Cr * Vr * (r ^ d / (3 * r) ^ e) by ring, hrd,
              hCr, add_mul, add_mul]
            have : 0 ≤ (3 : ℝ) ^ e * Vr * (r ^ 2 / (3 : ℝ) ^ e) := by positivity
            have key : C0 * 36 * (3 : ℝ) ^ e / Vr * Vr * (r ^ 2 / (3 : ℝ) ^ e) = C0 * 36 * r ^ 2 := by
              field_simp
            linarith [key, this]
        _ = ENNReal.ofReal Cr * (ENNReal.ofReal (r ^ d) * V) / ENNReal.ofReal ((3 * r) ^ e) := by
            rw [ENNReal.ofReal_div_of_pos h3r, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul hCr0, hVr, ENNReal.ofReal_toReal hVt, mul_assoc]
        _ ≤ ENNReal.ofReal Cr * volume (Metric.ball x r) / ENNReal.ofReal (ρ ^ e) := by
            rw [hvol]; exact ENNReal.div_le_div_left hE3 _
        _ = _ := by rw [hCe]

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Thm 1, (5)] with `m = 2` at a
Lebesgue point). -/
theorem abs_sub_taylorAverage_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)) (Q : Set (Rd d)) (x : Rd d) (c : ℝ), MemW 2 1 f →
      IsWeakGradient f G → IsWeakHessian f H → IsCubeOrBall Q → x ∈ Q →
        Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0) →
          ENNReal.ofReal |c - ⨍ z in Q, (f z + ⟪G z, x - z⟫)| ≤
            C * ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
  obtain ⟨K, hK⟩ := poincare2_ae hd
  obtain ⟨κ, hκ0, hκ⟩ := theorem_2_1_first.volume_inter_ball_ge hd
  obtain ⟨C, hC⟩ := lintegral_ball_kernel2_le hd
  obtain ⟨K0, hK0⟩ := theorem_2_1_first.isCubeOrBall_props hd
  refine ⟨κ⁻¹ * K * C, fun f G H Q x c hf hG hH hQ hx hc => ?_⟩
  obtain ⟨-, hQm, hQb, hQ0, -⟩ := hK0 Q hQ
  have hQt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hf1 : MemW 1 1 f := ⟨hf.1, fun α h => hf.2 α (h.trans (by norm_num))⟩
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) :=
    theorem_2_1_first.coord_integrable hf1 hG
  have hGint : Integrable G := by
    have hexpG : ∀ z, G z = ∑ i, Rd.coord i (G z) • Rd.basisVec i := by
      intro z
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' (G z)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Rd.coord, Rd.basisVec, real_inner_comm]
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext hexpG
    rw [this]
    exact integrable_finset_sum _ fun i _ => (hGi i).smul_const _
  have hHint := integrable_hessian hf hH
  have hHm := hHint.aestronglyMeasurable
  set J : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ with hJdef
  have hJ : J ≠ ⊤ := hHint.integrableOn.2.ne
  obtain ⟨R, hR⟩ := hQb.subset_closedBall (0 : Rd d)
  have hTi : ∀ w : Rd d, IntegrableOn (fun z => f z + ⟪G z, w - z⟫) Q := by
    intro w
    refine hfi.integrableOn.add (Integrable.mono' (hGint.integrableOn.norm.mul_const (‖w‖ + R))
      ((hGint.aestronglyMeasurable.inner
        (continuous_const.sub continuous_id).aestronglyMeasurable).restrict) ?_)
    refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs]
    have hz : ‖z‖ ≤ R := by simpa using hR hz
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (norm_sub_le _ _).trans (by linarith)
  set T : Rd d → ℝ := fun w => ⨍ z in Q, (f z + ⟪G z, w - z⟫) with hTdef
  set M : ℝ := (volume.real Q)⁻¹ * ∫ z in Q, ‖G z‖ with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (inv_nonneg.2 measureReal_nonneg)
    (integral_nonneg fun _ => norm_nonneg _)
  have hTdiff : ∀ y, |T y - T x| ≤ M * ‖y - x‖ := by
    intro y
    have e1 : T y - T x = (volume.real Q)⁻¹ * ∫ z in Q, ⟪G z, y - x⟫ := by
      simp only [hTdef]
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub,
        ← integral_sub (hTi y) (hTi x)]
      congr 2
      funext z
      simp only [inner_sub_right]
      ring
    rw [e1, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg, hMdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 measureReal_nonneg)
    rw [← integral_mul_const]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _)
      (hGint.integrableOn.norm.mul_const _) (Eventually.of_forall fun z => ?_))
    exact abs_real_inner_le_norm _ _
  set e : ℝ := (d : ℝ) - 2 with he
  set L : ℝ≥0∞ := ENNReal.ofReal |c - T x| with hL
  set I : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ e with hI
  have hκ0' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0.ne'
  -- the shifted kernel
  have hker : ∀ z r, 0 < r → 1 / (ENNReal.ofReal r + edist x z) ^ e ≤
      1 / edist x z ^ e + ENNReal.ofReal r := by
    intro z r hr
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · have hd1' : d = 1 := by omega
      have he1 : e = -1 := by rw [he, hd1']; norm_num
      rw [he1]
      simp only [ENNReal.rpow_neg_one, one_div, inv_inv]
      rw [add_comm]
    · have he0 : 0 ≤ e := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
        rw [he]; linarith
      refine le_trans ?_ le_self_add
      exact ENNReal.div_le_div_left (ENNReal.rpow_le_rpow le_add_self he0) _
  have key : ∀ᶠ r in 𝓝[>] (0 : ℝ), (κ : ℝ≥0∞) * L ≤
      ENNReal.ofReal (⨍ y in Metric.ball x r, |f y - c|) + ENNReal.ofReal (M * r) +
        K * C * (I + ENNReal.ofReal r * J) := by
    filter_upwards [hκ Q hQ x hx, self_mem_nhdsWithin] with r hr hr0
    have hr0 : (0 : ℝ) < r := hr0
    set B := Metric.ball x r with hB
    set A := Q ∩ B with hA
    have hAm : MeasurableSet A := hQm.inter measurableSet_ball
    have hVB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume x hr0).ne'
    have hVBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
    -- pointwise on `A`
    have hpt : ∀ᵐ y ∂(volume.restrict A), L ≤ ENNReal.ofReal |f y - c| + ENNReal.ofReal (M * r) +
        K * ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e := by
      have h1 := ae_restrict_of_ae (μ := volume) (s := A) (hK f G H hf hG hH Q hQ)
      filter_upwards [h1, ae_restrict_mem hAm] with y hy hyA
      refine le_trans ?_ (add_le_add le_rfl (hy hyA.1))
      have hyx : ‖y - x‖ ≤ r := by
        rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hyA.2).le
      rw [hL, ← ENNReal.ofReal_add (abs_nonneg _) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 := (hTdiff y).trans (mul_le_mul_of_nonneg_left hyx hM0)
      calc |c - T x| ≤ |c - f y| + |f y - T y| + |T y - T x| := by
            have := abs_sub_le c (f y) (T x)
            have := abs_sub_le (f y) (T y) (T x)
            linarith
        _ ≤ |f y - c| + M * r + |f y - T y| := by rw [abs_sub_comm c]; linarith
    -- the kernel term
    have hm : AEMeasurable (Function.uncurry fun (y z : Rd d) => ‖H z‖ₑ / edist y z ^ e)
        ((volume.restrict A).prod (volume.restrict Q)) := by
      have h1 : AEMeasurable (fun p : Rd d × Rd d => ‖H p.2‖ₑ)
          ((volume.restrict A).prod (volume.restrict Q)) :=
        hHm.restrict.aemeasurable.enorm.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      have h2 : Measurable fun p : Rd d × Rd d => edist p.1 p.2 ^ e :=
        (continuous_edist.measurable).pow_const _
      exact h1.div h2.aemeasurable
    have hJ' : ∫⁻ y in A, ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e ≤
        C * volume B * (I + ENNReal.ofReal r * J) := by
      have hHmQ : AEMeasurable (fun z => ‖H z‖ₑ) (volume.restrict Q) :=
        hHm.restrict.aemeasurable.enorm
      calc ∫⁻ y in A, ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e
          = ∫⁻ z in Q, ∫⁻ y in A, ‖H z‖ₑ / edist y z ^ e := lintegral_lintegral_swap hm
        _ = ∫⁻ z in Q, ‖H z‖ₑ * ∫⁻ y in A, 1 / edist y z ^ e := by
            refine lintegral_congr fun z => ?_
            rw [← lintegral_const_mul' _ _ enorm_ne_top]
            refine lintegral_congr fun y => ?_
            rw [div_eq_mul_inv, one_div]
        _ ≤ ∫⁻ z in Q, ‖H z‖ₑ * (C * volume B * (1 / edist x z ^ e + ENNReal.ofReal r)) := by
            refine lintegral_mono fun z => mul_le_mul' le_rfl ?_
            refine (lintegral_mono_set Set.inter_subset_right).trans ((hC x z hr0).trans ?_)
            rw [← mul_one_div]
            exact mul_le_mul' le_rfl (hker z r hr0)
        _ = ∫⁻ z in Q, ((C * volume B) * (‖H z‖ₑ / edist x z ^ e) +
              (C * volume B * ENNReal.ofReal r) * ‖H z‖ₑ) := by
            refine lintegral_congr fun z => ?_
            simp only [div_eq_mul_inv, one_mul]; ring
        _ = C * volume B * (I + ENNReal.ofReal r * J) := by
            rw [lintegral_add_right' _ (hHmQ.const_mul _),
              lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hVBt),
              lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hVBt)
                ENNReal.ofReal_ne_top)]
            ring
    have hfB : IntegrableOn (fun y => |f y - c|) B :=
      (hfi.integrableOn.sub (integrableOn_const hVBt)).abs
    have havg : ENNReal.ofReal (⨍ y in B, |f y - c|) =
        (volume B)⁻¹ * ∫⁻ y in B, ENNReal.ofReal |f y - c| := by
      rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.2 measureReal_nonneg),
        ofReal_integral_eq_lintegral_ofReal hfB (Eventually.of_forall fun _ => abs_nonneg _),
        measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hVB0 hVBt),
        ENNReal.ofReal_toReal hVBt]
    have hint : (κ : ℝ≥0∞) * volume B * L ≤ (∫⁻ y in B, ENNReal.ofReal |f y - c|) +
        volume B * ENNReal.ofReal (M * r) + K * (C * volume B * (I + ENNReal.ofReal r * J)) := by
      have hm1 : AEMeasurable (fun y => ENNReal.ofReal |f y - c|) (volume.restrict A) :=
        (hfi.aemeasurable.sub aemeasurable_const).abs.ennreal_ofReal.restrict
      calc (κ : ℝ≥0∞) * volume B * L ≤ volume A * L := mul_le_mul' hr le_rfl
        _ = ∫⁻ y in A, L := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in A, (ENNReal.ofReal |f y - c| + ENNReal.ofReal (M * r) +
              K * ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e) := lintegral_mono_ae hpt
        _ = (∫⁻ y in A, ENNReal.ofReal |f y - c|) + volume A * ENNReal.ofReal (M * r) +
              K * ∫⁻ y in A, ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ e := by
            rw [lintegral_add_left' (f := fun y => ENNReal.ofReal |f y - c| + ENNReal.ofReal (M * r))
              (by exact hm1.add aemeasurable_const), lintegral_add_left' hm1,
              setLIntegral_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top, mul_comm (volume A)]
        _ ≤ _ := add_le_add (add_le_add (lintegral_mono_set Set.inter_subset_right)
              (mul_le_mul' (measure_mono Set.inter_subset_right) le_rfl)) (mul_le_mul' le_rfl hJ')
    calc (κ : ℝ≥0∞) * L = (volume B)⁻¹ * ((κ : ℝ≥0∞) * volume B * L) := by
          rw [show (κ : ℝ≥0∞) * volume B * L = volume B * (κ * L) by ring, ← mul_assoc,
            ENNReal.inv_mul_cancel hVB0 hVBt, one_mul]
      _ ≤ (volume B)⁻¹ * ((∫⁻ y in B, ENNReal.ofReal |f y - c|) +
            volume B * ENNReal.ofReal (M * r) + K * (C * volume B * (I + ENNReal.ofReal r * J))) :=
          mul_le_mul' le_rfl hint
      _ = ENNReal.ofReal (⨍ y in B, |f y - c|) + ENNReal.ofReal (M * r) +
            K * C * (I + ENNReal.ofReal r * J) := by
          rw [mul_add, mul_add, havg]
          congr 1
          · congr 1
            rw [← mul_assoc, ENNReal.inv_mul_cancel hVB0 hVBt, one_mul]
          · rw [show (K : ℝ≥0∞) * (C * volume B * (I + ENNReal.ofReal r * J)) =
                volume B * (K * C * (I + ENNReal.ofReal r * J)) by ring, ← mul_assoc,
              ENNReal.inv_mul_cancel hVB0 hVBt, one_mul]
  have hlim : Tendsto (fun r => ENNReal.ofReal (⨍ y in Metric.ball x r, |f y - c|) +
      ENNReal.ofReal (M * r) + K * C * (I + ENNReal.ofReal r * J))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 + 0 + K * C * (I + 0 * J))) := by
    have h1 := ENNReal.tendsto_ofReal hc
    rw [ENNReal.ofReal_zero] at h1
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have h2 : Tendsto (fun r : ℝ => ENNReal.ofReal (M * r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hr.const_mul M)
      rwa [mul_zero, ENNReal.ofReal_zero] at this
    have h3 : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := ENNReal.tendsto_ofReal hr
      rwa [ENNReal.ofReal_zero] at this
    exact (h1.add h2).add (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add
      (ENNReal.Tendsto.mul_const h3 (Or.inr hJ))) (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)))
  simp only [zero_add, zero_mul, add_zero] at hlim
  have hκL : (κ : ℝ≥0∞) * L ≤ K * C * I := ge_of_tendsto hlim key
  calc L = (κ : ℝ≥0∞)⁻¹ * ((κ : ℝ≥0∞) * L) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hκ0' ENNReal.coe_ne_top, one_mul]
    _ ≤ (κ : ℝ≥0∞)⁻¹ * (K * C * I) := mul_le_mul' le_rfl hκL
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hκ0.ne']
        ring

end theorem_2_1_second

end WeakPathwiseIto
