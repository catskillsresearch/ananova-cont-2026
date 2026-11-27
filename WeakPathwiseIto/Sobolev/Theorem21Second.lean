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
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the mollification of a `W^{2,1}`
function is `C²`, with second derivatives the mollified weak Hessian entries). -/
theorem hessian_convolution {f : Rd d → ℝ} {G : Rd d → Rd d} {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hG : IsWeakGradient f G) (hH : IsWeakHessian f H) {ψ : Rd d → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiff ℝ 2 (fun x => ∫ y, f y * ψ (x - y)) ∧
      ∀ w i j, fderiv ℝ (fderiv ℝ (fun x => ∫ y, f y * ψ (x - y))) w (Rd.basisVec i)
          (Rd.basisVec j) = ∫ y, Rd.coord j (H y (Rd.basisVec i)) * ψ (w - y) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: a bilinear form is bounded by the sum of
its entries in the standard basis). -/
theorem norm_le_sum_entries (A : Rd d →L[ℝ] Rd d →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A (Rd.basisVec i) (Rd.basisVec j)| := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: the local Riesz potential of order `2`
is bounded on `L¹(Q)`). -/
theorem lintegral_potential2_le (hd : 0 < d) {Q : Set (Rd d)} (hQb : Bornology.IsBounded Q)
    (hQm : MeasurableSet Q) :
    ∃ C : ℝ≥0, ∀ h : Rd d → ℝ, AEStronglyMeasurable h →
      ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 2) ≤ C * ∫⁻ z in Q, ‖h z‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate, (5) for `m = 2` almost everywhere on `Q`
for `W^{2,1}` functions, by mollification). -/
theorem poincare2_ae (hd : 0 < d) : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)), MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H →
      ∀ Q : Set (Rd d), IsCubeOrBall Q →
        ∀ᵐ y ∂volume, y ∈ Q → ENNReal.ofReal |f y - ⨍ z in Q, (f z + ⟪G z, y - z⟫)| ≤
          K * ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Lemma 2] with `α = 2`, in the
unified form `⨍_{B(x,r)} |y - z|^{2-d} ≤ C (r + |x - z|)^{2-d}`). -/
theorem lintegral_ball_kernel2_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (x z : Rd d) {r : ℝ}, 0 < r →
    ∫⁻ y in Metric.ball x r, 1 / edist y z ^ ((d : ℝ) - 2) ≤
      C * volume (Metric.ball x r) / (ENNReal.ofReal r + edist x z) ^ ((d : ℝ) - 2) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, second estimate: [BH93, Thm 1, (5)] with `m = 2` at a
Lebesgue point). -/
theorem abs_sub_taylorAverage_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)) (Q : Set (Rd d)) (x : Rd d) (c : ℝ), MemW 2 1 f →
      IsWeakGradient f G → IsWeakHessian f H → IsCubeOrBall Q → x ∈ Q →
        Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0) →
          ENNReal.ofReal |c - ⨍ z in Q, (f z + ⟪G z, x - z⟫)| ≤
            C * ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2) := by
  sorry

end theorem_2_1_second

end WeakPathwiseIto
