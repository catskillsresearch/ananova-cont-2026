/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Bessel.Theorem29
public import WeakPathwiseIto.Sobolev.MemW2Plus
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Sobolev.HardyLittlewood
public import Carleson.ToMathlib.RealInterpolation.Minkowski
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.Theorem21Second
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Bessel.WienerLawExists
public import WeakPathwiseIto.Main.Theorem51Steps
public import WeakPathwiseIto.Main.Theorem52Mollify

/-! # Steps of the proof of Theorem 5.2 (Appendix C)

Appendix C: mollify `F_m := η_m ⋆ F`; the non-Lebesgue points `E₁` of `F` are polar
(Theorem 2.9, [AM71], [Fuk93]); `u_m := ‖∇²F_m - ∇²F‖ → 0` in `L^p` and `W^{s,p}`; the truncated
maximal operator `M_1` is bounded on `L^p` and `W^{s,p}`; `h_m := (M_1 u_m)^p` satisfies the
hypotheses of Lemma B.2; Brownian motion avoids Lebesgue-null sets at the (countably many)
positive partition times; the first partition interval is treated with Lemma B.1; then (10),
Hölder and Lemma A.1 give `‖u_m‖_{W⁰_{B,π}} ≤ C limsup_n ‖h_m‖_{n,1,B}^{1/p}`. Only the first
steps are stubbed here; the path-side steps are stubbed after the plan is approved. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace Convolution

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: `|⨍_s f - c| ≤ ⨍_s |f - c|`). -/
theorem abs_setAverage_sub_le {f : Rd d → ℝ} {s : Set (Rd d)} (hf : IntegrableOn f s)
    (hs0 : volume s ≠ 0) (hst : volume s ≠ ∞) (c : ℝ) :
    |(⨍ y in s, f y) - c| ≤ ⨍ y in s, |f y - c| := by
  have hm : 0 < volume.real s := ENNReal.toReal_pos hs0 hst
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have h : (volume.real s)⁻¹ * (∫ y in s, f y) - c =
      (volume.real s)⁻¹ * ∫ y in s, (f y - c) := by
    rw [integral_sub hf (integrableOn_const hst), setIntegral_const, smul_eq_mul, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
  rw [h, abs_mul, abs_of_pos (inv_pos.2 hm)]
  gcongr
  exact abs_integral_le_integral_abs

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: at a Lebesgue point with value `c`, `F̃(x) = c`). -/
theorem preciseRepresentative_eq_of_tendsto {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {x : Rd d} {c : ℝ}
    (hc : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |F y - c|) (𝓝[>] 0) (𝓝 0)) :
    preciseRepresentative F x = c := by
  unfold preciseRepresentative
  apply Tendsto.limsup_eq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hc
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.norm_eq_abs]
  exact abs_setAverage_sub_le ((hF.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
    Metric.ball_subset_closedBall) (Metric.measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne c

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: `|F * ψ(x) - c| ≤ K ∫_{B(x,r)} |F - c|` for a mollifier `0 ≤ ψ ≤ K`, `∫ ψ = 1`, `supp ψ ⊆ B(0,r)`). -/
theorem abs_mollify_sub_le {F : Rd d → ℝ} (hF : LocallyIntegrable F) {ψ : Rd d → ℝ}
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x = 1) {r K : ℝ}
    (hψs : Function.support ψ ⊆ Metric.ball 0 r) (hψb : ∀ x, ψ x ≤ K) (x : Rd d) (c : ℝ) :
    |(∫ y, F y * ψ (x - y)) - c| ≤ K * ∫ y in Metric.ball x r, |F y - c| := by
  have hψi : Integrable ψ := Integrable.of_integral_ne_zero (by rw [hψ1]; norm_num)
  have hψx : Integrable (fun y => ψ (x - y)) := hψi.comp_sub_left x
  have hψx1 : ∫ y, ψ (x - y) = 1 := by rw [integral_sub_left_eq_self]; exact hψ1
  have hK : 0 ≤ K := (hψ0 0).trans (hψb 0)
  have hsupp : ∀ y, y ∉ Metric.ball x r → ψ (x - y) = 0 := fun y hy => by
    by_contra h
    apply hy
    have := hψs h
    rw [mem_ball_zero_iff] at this
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact this
  have hFb : IntegrableOn F (Metric.ball x r) :=
    (hF.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hG : ∀ c' : ℝ, Integrable ((Metric.ball x r).indicator fun y => |F y - c'|) := fun c' =>
    (show IntegrableOn (fun y => |F y - c'|) (Metric.ball x r) volume from
      (hFb.sub (integrableOn_const (C := c') measure_ball_lt_top.ne (by simp))).abs).integrable_indicator
      measurableSet_ball
  have hpt : ∀ c' y, ‖(F y - c') * ψ (x - y)‖ ≤
      K * (Metric.ball x r).indicator (fun y => |F y - c'|) y := fun c' y => by
    by_cases hy : y ∈ Metric.ball x r
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 _), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hψb _) (abs_nonneg _)
    · rw [indicator_of_notMem hy, hsupp y hy]; simp
  have hFψ : Integrable (fun y => F y * ψ (x - y)) := by
    refine Integrable.mono' ((hG 0).const_mul K)
      (hF.aestronglyMeasurable.mul hψx.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    simpa using hpt 0 y
  have heq : (∫ y, F y * ψ (x - y)) - c = ∫ y, (F y - c) * ψ (x - y) := by
    have : (∫ y, F y * ψ (x - y)) - c = (∫ y, F y * ψ (x - y)) - ∫ y, c * ψ (x - y) := by
      rw [integral_const_mul, hψx1, mul_one]
    rw [this, ← integral_sub hFψ (hψx.const_mul c)]
    simp_rw [sub_mul]
  rw [heq, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((hG c).const_mul K) (ae_of_all _ (hpt c))).trans
    (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator measurableSet_ball]

/-- **Subgoal** (Appendix C, mollification: `F_m(x) → F̃(x)` at every Lebesgue point). -/
theorem tendsto_mollify_of_isLebesguePoint {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)))
    (hψb : ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d) {x : Rd d}
    (hx : IsLebesguePoint F x) :
    Tendsto (fun n => ∫ y, F y * ψ n (x - y)) atTop (𝓝 (preciseRepresentative F x)) := by
  obtain ⟨c, hc⟩ := hx
  rw [preciseRepresentative_eq_of_tendsto hF hc]
  obtain ⟨C, hC⟩ := hψb
  set V : ℝ := volume.real (Metric.ball (0 : Rd d) 1)
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have hlim := (hc.comp hr).const_mul (C * V)
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  have hrn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hvol : volume.real (Metric.ball x (1 / ((n : ℝ) + 1))) =
      (1 / ((n : ℝ) + 1)) ^ d * V := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos _ _ hrn, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hint : ∫ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| =
      volume.real (Metric.ball x (1 / ((n : ℝ) + 1))) *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact (ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hrn).ne' measure_ball_lt_top.ne).ne'
  rw [Real.norm_eq_abs]
  refine (abs_mollify_sub_le hF (hψ0 n) (hψ1 n) (hψs n) (hC n) x c).trans (le_of_eq ?_)
  rw [hint, hvol, Function.comp_apply]
  have h1 : ((n : ℝ) + 1) ^ d * (1 / ((n : ℝ) + 1)) ^ d = 1 := by
    rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]
  calc C * ((n : ℝ) + 1) ^ d * ((1 / ((n : ℝ) + 1)) ^ d * V *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c|)
      = C * (((n : ℝ) + 1) ^ d * (1 / ((n : ℝ) + 1)) ^ d) * V *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| := by ring
    _ = _ := by rw [h1, mul_one]

/-- **Subgoal** (Appendix C, `E₁` is polar: Theorem 2.9, [AM71, Thm. 1], [Fuk93]). -/
theorem isBrownianPolar_nonLebesgue (hT : 0 < T) {p : ℝ} (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2Plus p F) : IsBrownianPolar d T {x | ¬ IsLebesguePoint F x} := by
  obtain ⟨_, _, hFs⟩ := hF
  have h29 := theorem_2_9 d 2 hp hFs.1
  rw [Nat.cast_ofNat] at h29
  exact (IsBrownianPolar.iff_isNull hT _).2 (besselCapacity.IsNull.one_two_of_two_p hp h29)

/-- **Subgoal** (Appendix C, Brownian motion does not enter a polar set at positive times). -/
theorem ae_forall_path_not_mem {E : Set (Rd d)} (hE : IsBrownianPolar d T E) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ Ioc 0 T,
      CanonicalWienerSpace.path ω t ∉ E := by
  refine measure_eq_zero_iff_ae_notMem.1 (hE x₀) |>.mono fun ω hω t ht hmem => hω ?_
  refine ⟨⟨t, ht.1.le, ht.2⟩, ht.1, ?_⟩
  simpa [CanonicalWienerSpace.path, CanonicalWienerSpace.B, ht.1.le, ht.2] using hmem

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: Tonelli in difference coordinates
for a.e.-measurable integrands, `∫∫ Φ(x, y) dy dx = ∫∫ Φ(x, x + h) dx dh`). -/
theorem lintegral_lintegral_eq_add' {Φ : Rd d → Rd d → ℝ≥0∞}
    (hΦ : AEMeasurable (fun q : Rd d × Rd d => Φ q.1 (q.1 + q.2)) (volume.prod volume)) :
    ∫⁻ x, ∫⁻ y, Φ x y = ∫⁻ h, ∫⁻ x, Φ x (x + h) := by
  have h1 : ∀ x, ∫⁻ y, Φ x y = ∫⁻ h, Φ x (x + h) := fun x =>
    (lintegral_add_left_eq_self (fun y => Φ x y) x).symm
  simp_rw [h1]
  exact lintegral_lintegral_swap hΦ

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: for a fixed shift `h`, the
difference `a_n(x + h) - a_n(x)` of `a_n := ψ_n ⋆ f - f` tends to `0` in `L^p`). -/
theorem tendsto_lintegral_shift_mollify_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p))
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) (h : Rd d) :
    Tendsto (fun n => ∫⁻ x, ‖((∫ y, ψ n (x + h - y) • f y) - f (x + h)) -
      ((∫ y, ψ n (x - y) • f y) - f x)‖ₑ ^ p) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  set a : ℕ → Rd d → E := fun n x => (∫ y, ψ n (x - y) • f y) - f x
  set e : ℕ → ℝ≥0∞ := fun n => eLpNorm (a n) (ENNReal.ofReal p) volume
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have ham : ∀ n, AEStronglyMeasurable (a n) volume := by
    intro n
    have hψk : HasCompactSupport (ψ n) :=
      (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
        (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
    have hconv : (fun x => ∫ y, ψ n (x - y) • f y) =
        (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
      funext x; rw [convolution_lsmul_swap]
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • f y := by
      rw [hconv]; exact hψk.continuous_convolution_left _ (hψc n) hfl
    exact hc.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hbound : ∀ n, ∫⁻ x, ‖a n (x + h) - a n x‖ₑ ^ p ≤ (2 * e n) ^ p := by
    intro n
    have hm : AEStronglyMeasurable (fun x => a n (x + h) - a n x) volume :=
      ((ham n).comp_measurePreserving (measurePreserving_add_right volume h)).sub (ham n)
    have hle : eLpNorm (fun x => a n (x + h) - a n x) (ENNReal.ofReal p) volume ≤ 2 * e n := by
      have hsub : (fun x => a n (x + h) - a n x) = (fun x => a n (x + h)) + fun x => -a n x := by
        funext x; simp [sub_eq_add_neg]
      rw [hsub, two_mul]
      refine (eLpNorm_add_le hp1).trans ?_
      have h1 : eLpNorm (fun x => a n (x + h)) (ENNReal.ofReal p) volume = e n :=
        eLpNorm_comp_measurePreserving (ham n) (measurePreserving_add_right volume h)
      rw [h1, show (fun x => -a n x) = -a n from rfl, eLpNorm_neg]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hm, hpr] at hle
    have := ENNReal.rpow_le_rpow hle hp0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at this
  have hlim : Tendsto (fun n => (2 * e n) ^ p) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_mollify_sub hp hf hψc hψ0 hψ1 hψs) (Or.inr (ENNReal.ofNat_ne_top (n := 2)))
      simpa using this
    have := (ENNReal.continuous_rpow_const (y := p)).tendsto 0 |>.comp h2
    rw [ENNReal.zero_rpow_of_pos hp0] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) hbound

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: domination,
`‖a_n(· + h) - a_n‖_p^p ≤ 2^p ‖f(· + h) - f‖_p^p`). -/
theorem lintegral_shift_mollify_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p))
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) (n : ℕ) (h : Rd d) :
    ∫⁻ x, ‖((∫ y, ψ n (x + h - y) • f y) - f (x + h)) - ((∫ y, ψ n (x - y) • f y) - f x)‖ₑ ^ p ≤
      2 ^ p * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  set g : Rd d → E := fun x => f (x + h) - f x
  have hfh : MemLp (fun x => f (x + h)) (ENNReal.ofReal p) :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have hg : MemLp g (ENNReal.ofReal p) := hfh.sub hf
  have hgm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  -- the shifted difference is the mollifier defect of `g`
  have hshift : ∀ x, ∫ y, ψ n (x + h - y) • f y = ∫ y, ψ n (x - y) • f (y + h) := by
    intro x
    rw [← integral_add_right_eq_self (fun y => ψ n (x + h - y) • f y) h]
    congr 1; funext y; congr 2; abel
  have hψk : HasCompactSupport (ψ n) :=
    (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
      (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hfhl : LocallyIntegrable (fun x => f (x + h)) volume := hfh.locallyIntegrable hp1
  have hI1 : ∀ x, Integrable (fun y => ψ n (x - y) • f (y + h)) := fun x =>
    hfhl.integrable_smul_left_of_hasCompactSupport ((hψc n).comp (continuous_sub_left x))
      (hψk.comp_homeomorph (Homeomorph.subLeft x))
  have hI2 : ∀ x, Integrable (fun y => ψ n (x - y) • f y) := fun x =>
    hfl.integrable_smul_left_of_hasCompactSupport ((hψc n).comp (continuous_sub_left x))
      (hψk.comp_homeomorph (Homeomorph.subLeft x))
  have hfun : ∀ x, ((∫ y, ψ n (x + h - y) • f y) - f (x + h)) -
      ((∫ y, ψ n (x - y) • f y) - f x) = (∫ y, ψ n (x - y) • g y) - g x := by
    intro x
    rw [hshift x]
    simp only [g, smul_sub]
    rw [integral_sub (hI1 x) (hI2 x)]
    abel
  simp_rw [hfun]
  -- measurability of the mollifier defect of `g`
  have hconv : (fun x => ∫ y, ψ n (x - y) • g y) =
      (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
    funext x; rw [convolution_lsmul_swap]
  have hLm : AEStronglyMeasurable (fun x => (∫ y, ψ n (x - y) • g y) - g x) volume := by
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • g y := by
      rw [hconv]; exact hψk.continuous_convolution_left _ (hψc n) (hg.locallyIntegrable hp1)
    exact hc.aestronglyMeasurable.sub hgm
  have hsup : ⨆ z ∈ Metric.ball (0 : Rd d) (1 / ((n : ℝ) + 1)),
      eLpNorm (fun x => g (x - z) - g x) (ENNReal.ofReal p) volume ≤
        2 * eLpNorm g (ENNReal.ofReal p) volume := by
    refine iSup₂_le fun z _ => ?_
    have hsub : (fun x => g (x - z) - g x) = (fun x => g (x - z)) + fun x => -g x := by
      funext x; simp [sub_eq_add_neg]
    rw [hsub, two_mul]
    refine (eLpNorm_add_le hp1).trans ?_
    have h1 : eLpNorm (fun x => g (x - z)) (ENNReal.ofReal p) volume =
        eLpNorm g (ENNReal.ofReal p) volume :=
      eLpNorm_comp_measurePreserving hgm (measurePreserving_sub_right volume z)
    rw [h1, show (fun x => -g x) = -g from rfl, eLpNorm_neg]
  have hle := (eLpNorm_mollify_sub_le hp hg (hψc n) (hψ0 n) (hψ1 n) (hψs n)).trans hsup
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hLm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hgm, hpr] at hle
  have := ENNReal.rpow_le_rpow hle hp0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne',
    ENNReal.rpow_one] at this
  exact this

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: the weak Hessian is unique a.e.,
entrywise by uniqueness of weak derivatives). -/
theorem ae_eq_of_isWeakHessian {F : Rd d → ℝ} {H H' : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H') : H =ᵐ[volume] H' := by
  set M : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j =>
    (EuclideanSpace.proj j : Rd d →L[ℝ] ℝ).smulRight (Rd.basisVec i)
  have hrep : ∀ A : Rd d →L[ℝ] Rd d, A = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) • M i j := by
    intro A
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun k => ?_
    ext l
    simp [M, Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Pi.single_apply]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    theorem_5_1.isWeakDerivative_ae_unique (hH i j) (hH' i j)] with x hx
  rw [hrep (H x), hrep (H' x)]
  simp_rw [hx]

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: the Gagliardo double integral in
difference coordinates, `∫∫ ‖A x - A y‖^p / |x - y|^r = ∫ (∫ ‖A(x + h) - A x‖^p dx) / |h|^r dh`). -/
theorem lintegral_gagliardo_eq_shift {E : Type*} [NormedAddCommGroup E] {A : Rd d → E}
    (hA : AEStronglyMeasurable A volume) (p r : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖A x - A y‖ₑ ^ p / edist x y ^ r =
      ∫⁻ h, (∫⁻ x, ‖A (x + h) - A x‖ₑ ^ p) / ‖h‖ₑ ^ r := by
  have hsh : AEStronglyMeasurable (fun q : Rd d × Rd d => A (q.1 + q.2)) (volume.prod volume) :=
    hA.comp_snd.comp_measurePreserving (measurePreserving_prod_add volume volume)
  have hΦ : AEMeasurable (fun q : Rd d × Rd d =>
      ‖A q.1 - A (q.1 + q.2)‖ₑ ^ p / edist q.1 (q.1 + q.2) ^ r) (volume.prod volume) := by
    refine ((hA.comp_fst.sub hsh).enorm.pow_const p).div ?_
    exact ((continuous_fst.edist (continuous_fst.add continuous_snd)).measurable.pow_const
      r).aemeasurable
  rw [theorem_5_2.lintegral_lintegral_eq_add' (Φ := fun x y => ‖A x - A y‖ₑ ^ p / edist x y ^ r) hΦ]
  refine lintegral_congr fun h => ?_
  have he : ∀ x : Rd d, edist x (x + h) = ‖h‖ₑ := by
    intro x; rw [edist_comm, edist_eq_enorm_sub, add_sub_cancel_left]
  simp_rw [he, div_eq_mul_inv]
  have hm : AEMeasurable (fun x => ‖A (x + h) - A x‖ₑ ^ p) volume :=
    ((hA.comp_measurePreserving (measurePreserving_add_right volume h)).sub hA).enorm.pow_const p
  rw [← lintegral_mul_const'' _ hm]
  refine lintegral_congr fun x => ?_
  rw [enorm_sub_rev]

/-- **Subgoal** (Appendix C, mollification converges in `W^{2+s,p}`: `u_m → 0` in `L^p` and in
the Gagliardo seminorm `[·]_{W^{s,p}}`). -/
theorem tendsto_mollify_hessian {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2PlusS s p F) {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H)
    {ψ : ℕ → Rd d → ℝ} (hψ : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n))
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => eLpNorm (fun x => smoothHessian (fun z => ∫ y, F y * ψ n (z - y)) x - H x)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x, ∫⁻ y,
        ‖‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) x - H x‖ -
          ‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) y - H y‖‖ₑ ^ p /
            edist x y ^ (s * p + d)) atTop (𝓝 0) := by
  have : CompleteSpace (Rd d →L[ℝ] Rd d) := FiniteDimensional.complete ℝ _
  have hp1 : 1 ≤ p := hp.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) < s * p + d := by positivity
  obtain ⟨G, hG⟩ := exists_isWeakGradient_of_memW (k := 2) (by norm_num) hF.1
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).continuous
  have hψk : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
      (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hsH : ∀ n x, smoothHessian (fun z => ∫ y, F y * ψ n (z - y)) x =
      ∫ y, ψ n (x - y) • H y := fun n x =>
    smoothHessian_convolution hG hH (hψ n) (hψk n) x
  have hHL : MemLp H (ENNReal.ofReal p) := memLp_of_isWeakHessian hF.1 hH
  have hHm : AEStronglyMeasurable H volume := hHL.aestronglyMeasurable
  simp_rw [hsH]
  refine ⟨tendsto_eLpNorm_mollify_sub hp1 hHL hψc hψ0 hψ1 hψs, ?_⟩
  -- the mollifier defect `A n` of `H`
  set A : ℕ → Rd d → (Rd d →L[ℝ] Rd d) := fun n x => (∫ y, ψ n (x - y) • H y) - H x
  have hAm : ∀ n, AEStronglyMeasurable (A n) volume := by
    intro n
    have hconv : (fun x => ∫ y, ψ n (x - y) • H y) =
        (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) := by
      funext x; rw [convolution_lsmul_swap]
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • H y := by
      rw [hconv]
      exact (hψk n).continuous_convolution_left _ (hψc n)
        (hHL.locallyIntegrable (ENNReal.one_le_ofReal.2 hp1))
    exact hc.aestronglyMeasurable.sub hHm
  set r : ℝ := s * p + d
  -- reverse triangle inequality, then difference coordinates
  have hle : ∀ n, ∫⁻ x, ∫⁻ y, ‖‖A n x‖ - ‖A n y‖‖ₑ ^ p / edist x y ^ r ≤
      ∫⁻ h, (∫⁻ x, ‖A n (x + h) - A n x‖ₑ ^ p) / ‖h‖ₑ ^ r := by
    intro n
    rw [← lintegral_gagliardo_eq_shift (hAm n) p r]
    refine lintegral_mono fun x => lintegral_mono fun y => ?_
    gcongr
    exact enorm_le_iff_norm_le.2 (by simpa [Real.norm_eq_abs] using abs_norm_sub_norm_le _ _)
  -- dominated convergence in the shift `h`
  have hbound_eq : ∫⁻ h, 2 ^ p * (∫⁻ x, ‖H (x + h) - H x‖ₑ ^ p) / ‖h‖ₑ ^ r =
      2 ^ p * ∫⁻ x, ∫⁻ y, ‖H x - H y‖ₑ ^ p / edist x y ^ r := by
    rw [lintegral_gagliardo_eq_shift hHm p r, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofNat_ne_top)]
    simp_rw [mul_div_assoc]
  obtain ⟨H', hH', hfin⟩ := hF.2
  have hae := ae_eq_of_isWeakHessian hH hH'
  have hcongr : ∫⁻ x, ∫⁻ y, ‖H x - H y‖ₑ ^ p / edist x y ^ r =
      ∫⁻ x, ∫⁻ y, ‖H' x - H' y‖ₑ ^ p / edist x y ^ r := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hx, hy]
  have hdom : Tendsto (fun n => ∫⁻ h, (∫⁻ x, ‖A n (x + h) - A n x‖ₑ ^ p) / ‖h‖ₑ ^ r)
      atTop (𝓝 0) := by
    have h0 : (∫⁻ _h : Rd d, (0 : ℝ≥0∞)) = 0 := lintegral_zero
    rw [← h0]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun h => 2 ^ p * (∫⁻ x, ‖H (x + h) - H x‖ₑ ^ p) / ‖h‖ₑ ^ r) (fun n => ?_)
      (fun n => Eventually.of_forall fun h => ?_) ?_ ?_
    · have hj : AEMeasurable (fun q : Rd d × Rd d => ‖A n (q.1 + q.2) - A n q.1‖ₑ ^ p)
          (volume.prod volume) :=
        ((((hAm n).comp_snd.comp_measurePreserving (measurePreserving_prod_add volume volume)).sub
          (hAm n).comp_fst).enorm.pow_const p)
      exact hj.lintegral_prod_left'.div (continuous_enorm.measurable.pow_const r).aemeasurable
    · dsimp only
      exact ENNReal.div_le_div_right (lintegral_shift_mollify_sub_le hp1 hHL hψc hψ0 hψ1 hψs n h) _
    · rw [hbound_eq, hcongr]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofNat_ne_top)
        hfin.ne
    · refine Eventually.of_forall fun h => ?_
      by_cases hh : h = 0
      · subst hh
        simp [hp0]
        exact Or.inl (Or.inl (by rw [enorm_eq_nnnorm]; simp))
      have hb : ‖h‖ₑ ^ r ≠ 0 :=
        (ENNReal.rpow_pos (enorm_pos.2 hh) enorm_ne_top).ne'
      have := ENNReal.Tendsto.div_const
        (tendsto_lintegral_shift_mollify_sub hp1 hHL hψc hψ0 hψ1 hψs h) (Or.inr hb)
      rwa [ENNReal.zero_div] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom
    (fun n => bot_le) hle

/-- **Subgoal** (Appendix C, Hardy–Littlewood: `M_1` is bounded on `L^p`, `p > 1`). -/
theorem eLpNorm_maximal_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    eLpNorm (localMaximalFunction 1 f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  set K : ℝ≥0∞ := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) *
    (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hp0 : (0 : ℝ) < p := by linarith
  have hKp : K ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK
  refine ⟨(K ^ (1 / p)).toNNReal + 1, fun f => ?_⟩
  have hC0 : (((K ^ (1 / p)).toNNReal + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp
  have hKC : K ^ (1 / p) ≤ (((K ^ (1 / p)).toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hKp]; exact le_self_add
  by_cases hf : AEStronglyMeasurable f volume
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]; exact le_top
  set g := hf.mk f
  have hg : Measurable g := hf.stronglyMeasurable_mk.measurable
  rw [localMaximalFunction.congr_ae hf.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  have hp1 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  simp_rw [enorm_eq_self]
  calc (∫⁻ x, localMaximalFunction 1 g x ^ p) ^ (1 / p)
      ≤ (K * ∫⁻ y, ‖g y‖ₑ ^ p) ^ (1 / p) := by
        gcongr; exact hardyLittlewood.lintegral_rpow_le hg hp
    _ = K ^ (1 / p) * (∫⁻ y, ‖g y‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ _ := by gcongr
  all_goals first
    | exact hg.aestronglyMeasurable
    | exact (localMaximalFunction.measurable g).aestronglyMeasurable

/-- **Subgoal** (Appendix C, `M_1` commutes with translations: `M_1(f(· + h))(x) = M_1 f(x + h)`). -/
theorem localMaximalFunction_comp_add (f : Rd d → ℝ) (h x : Rd d) :
    localMaximalFunction 1 (fun z => f (z + h)) x = localMaximalFunction 1 f (x + h) := by
  unfold localMaximalFunction
  congr 1; funext r; congr 1; funext hr; congr 1; funext _
  have hpre : (· + h) ⁻¹' Metric.ball (x + h) r = Metric.ball x r := by
    rw [Metric.preimage_add_right_ball, add_sub_cancel_right]
  have hint : ∫⁻ z in Metric.ball x r, ‖f (z + h)‖ₑ = ∫⁻ z in Metric.ball (x + h) r, ‖f z‖ₑ := by
    rw [← hpre]
    exact (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight h) (fun z => ‖f z‖ₑ) _
  rw [laverage_eq, laverage_eq, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hint,
    Measure.addHaar_ball_center volume x r, Measure.addHaar_ball_center volume (x + h) r]

/-- **Subgoal** (Appendix C, sublinearity of `M_1` at two points:
`|M_1 f(x) - M_1 f(x + h)| ≤ M_1(f - f(· + h))(x)` where both values are finite). -/
theorem enorm_toReal_sub_le {f : Rd d → ℝ} (hf : Measurable f) {x h : Rd d}
    (hx : localMaximalFunction 1 f x ≠ ⊤) (hxh : localMaximalFunction 1 f (x + h) ≠ ⊤) :
    ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f (x + h)).toReal‖ₑ ≤
      localMaximalFunction 1 (fun z => f z - f (z + h)) x := by
  set a := localMaximalFunction 1 f x
  set b := localMaximalFunction 1 f (x + h)
  set c := localMaximalFunction 1 (fun z => f z - f (z + h)) x
  have hb : localMaximalFunction 1 (fun z => f (z + h)) x = b := localMaximalFunction_comp_add f h x
  have h1 : a ≤ b + c := by
    rw [← hb]
    refine localMaximalFunction.le_add (hf.comp (measurable_add_const h)) (fun z => ?_) x
    calc ‖f z‖ₑ = ‖f (z + h) + (f z - f (z + h))‖ₑ := by ring_nf
      _ ≤ _ := enorm_add_le _ _
  have h2 : b ≤ a + c := by
    rw [← hb]
    refine localMaximalFunction.le_add hf (fun z => ?_) x
    calc ‖f (z + h)‖ₑ = ‖f z - (f z - f (z + h))‖ₑ := by ring_nf
      _ ≤ _ := enorm_sub_le
  rcases eq_or_ne c ⊤ with hc | hc
  · rw [hc]; exact le_top
  have h1' : a.toReal ≤ b.toReal + c.toReal := by
    rw [← ENNReal.toReal_add hxh hc]; exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxh, hc⟩) h1
  have h2' : b.toReal ≤ a.toReal + c.toReal := by
    rw [← ENNReal.toReal_add hx hc]; exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hx, hc⟩) h2
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal hc]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)

/-- **Subgoal** (Appendix C, `M_1 f < ∞` a.e. for `f ∈ L^p`, `p > 1`). -/
theorem ae_localMaximalFunction_ne_top {p : ℝ} (hp : 1 < p) {f : Rd d → ℝ} (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p)) : ∀ᵐ x, localMaximalFunction 1 f x ≠ ⊤ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hI : ∫⁻ y, ‖f y‖ₑ ^ p < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hfp.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  have hK : ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hM : ∫⁻ x, localMaximalFunction 1 f x ^ p ≠ ⊤ :=
    ((hardyLittlewood.lintegral_rpow_le hf hp).trans_lt (ENNReal.mul_lt_top hK.lt_top hI)).ne
  filter_upwards [ae_lt_top ((localMaximalFunction.measurable f).pow_const p) hM]
    with x hx hxt
  rw [hxt, ENNReal.top_rpow_of_pos hp0] at hx
  exact lt_irrefl _ hx

/-- **Subgoal** (Appendix C, Tonelli in difference coordinates:
`∫∫ Φ(x, y) dy dx = ∫∫ Φ(x, x + h) dx dh`). -/
theorem lintegral_lintegral_eq_add {Φ : Rd d → Rd d → ℝ≥0∞}
    (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ x, ∫⁻ y, Φ x y = ∫⁻ h, ∫⁻ x, Φ x (x + h) := by
  have h1 : ∀ x, ∫⁻ y, Φ x y = ∫⁻ h, Φ x (x + h) := fun x =>
    (lintegral_add_left_eq_self (fun y => Φ x y) x).symm
  simp_rw [h1]
  have hm : Measurable (Function.uncurry fun x h : Rd d => Φ x (x + h)) :=
    hΦ.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  exact lintegral_lintegral_swap hm.aemeasurable

/-- **Subgoal** (Appendix C, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}` for measurable `f ∈ L^p`, with
the Hardy–Littlewood constant of `hardyLittlewood.lintegral_rpow_le`). -/
theorem gagliardo_maximal_le_of_measurable {s p : ℝ} (hp : 1 < p) {f : Rd d → ℝ}
    (hf : Measurable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
        edist x y ^ (s * p + d) ≤
      ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
        ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  set K := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  set e : ℝ := s * p + d
  have hM := localMaximalFunction.measurable f
  have hed : Measurable fun z : Rd d × Rd d => edist z.1 z.2 ^ e :=
    (measurable_fst.edist measurable_snd).pow_const e
  have hΦ : Measurable (Function.uncurry fun x y : Rd d =>
      ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
        edist x y ^ e) :=
    ((((hM.comp measurable_fst).ennreal_toReal.sub
      (hM.comp measurable_snd).ennreal_toReal).enorm).pow_const p).div hed
  have hΨ : Measurable (Function.uncurry fun x y : Rd d => ‖f x - f y‖ₑ ^ p / edist x y ^ e) :=
    ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).enorm).pow_const p).div hed
  rw [lintegral_lintegral_eq_add hΦ, lintegral_lintegral_eq_add hΨ, ← lintegral_const_mul' _ _ hK]
  refine lintegral_mono fun h => ?_
  have hedh : ∀ x : Rd d, edist x (x + h) = ‖h‖ₑ := fun x => by
    rw [edist_eq_enorm_sub, sub_add_cancel_left, enorm_neg]
  simp_rw [hedh, div_eq_mul_inv]
  set c := (‖h‖ₑ ^ e)⁻¹
  have hD : Measurable fun z => f z - f (z + h) := hf.sub (hf.comp (measurable_add_const h))
  have hfin := ae_localMaximalFunction_ne_top hp hf hfp
  have hfin' : ∀ᵐ x, localMaximalFunction 1 f (x + h) ≠ ⊤ :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hfin
  calc ∫⁻ x, ‖(localMaximalFunction 1 f x).toReal -
          (localMaximalFunction 1 f (x + h)).toReal‖ₑ ^ p * c
      ≤ ∫⁻ x, localMaximalFunction 1 (fun z => f z - f (z + h)) x ^ p * c := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfin, hfin'] with x hx hxh
        gcongr
        exact enorm_toReal_sub_le hf hx hxh
    _ = (∫⁻ x, localMaximalFunction 1 (fun z => f z - f (z + h)) x ^ p) * c :=
        lintegral_mul_const _ ((localMaximalFunction.measurable _).pow_const p)
    _ ≤ (K * ∫⁻ x, ‖f x - f (x + h)‖ₑ ^ p) * c := by
        gcongr; exact hardyLittlewood.lintegral_rpow_le hD hp
    _ = K * ∫⁻ x, ‖f x - f (x + h)‖ₑ ^ p * c := by
        rw [mul_assoc, lintegral_mul_const _ (hD.enorm.pow_const p)]

/-- **Subgoal** (Appendix C, `M_1` is bounded on `W^{s,p}`: translation invariance and
sublinearity, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}`). -/
theorem gagliardo_maximal_le {s p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    MemLp f (ENNReal.ofReal p) →
      ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
          edist x y ^ (s * p + d) ≤
        C * ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  set K := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  refine ⟨K.toNNReal, fun f hfp => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  set g := hfp.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hfp.aestronglyMeasurable.ae_eq_mk
  have hg : Measurable g := hfp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgp : MemLp g (ENNReal.ofReal p) := hfp.ae_eq hfg
  rw [localMaximalFunction.congr_ae hfg]
  have hR : ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) =
      ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) :=
    lintegral_congr_ae (hfg.mono fun x hx => lintegral_congr_ae (hfg.mono fun y hy => by
      simp only [hx, hy]))
  rw [hR]
  exact gagliardo_maximal_le_of_measurable hp hg hgp

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: mean value bound
`|a^p - b^p| ≤ p |a - b| (a^{p-1} + b^{p-1})` for `a, b ≥ 0`, `p ≥ 1`). -/
theorem enorm_rpow_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a ^ p - b ^ p‖ₑ ≤ ENNReal.ofReal p * ‖a - b‖ₑ * (‖a‖ₑ ^ (p - 1) + ‖b‖ₑ ^ (p - 1)) := by
  have key : ∀ {x y : ℝ}, 0 ≤ y → y ≤ x → x ^ p - y ^ p ≤ p * x ^ (p - 1) * (x - y) := by
    intro x y hy hyx
    rcases (hy.trans hyx).eq_or_lt with hx0 | hx0
    · have : y = 0 := le_antisymm (hx0 ▸ hyx) hy
      subst this; rw [← hx0]; simp
    have hB := one_add_mul_self_le_rpow_one_add (s := y / x - 1)
      (by have := div_nonneg hy hx0.le; linarith) hp
    rw [add_sub_cancel, Real.div_rpow hy hx0.le, le_div_iff₀ (by positivity)] at hB
    have hxp : x ^ p = x ^ (p - 1) * x := by rw [Real.rpow_sub_one hx0.ne']; field_simp
    have : (1 + p * (y / x - 1)) * x ^ p = x ^ p + p * x ^ (p - 1) * (y - x) := by
      rw [hxp]; field_simp
    nlinarith
  have hpp : 0 ≤ p - 1 := by linarith
  have hpos : 0 ≤ p := by linarith
  have hR : |a ^ p - b ^ p| ≤ p * |a - b| * (a ^ (p - 1) + b ^ (p - 1)) := by
    have h1 := Real.rpow_nonneg ha (p - 1)
    have h2 := Real.rpow_nonneg hb (p - 1)
    rcases le_total b a with hba | hab
    · have := key hb hba
      have hm : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb hba (by linarith)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hpos (sub_nonneg.2 hba)) h2]
    · have := key ha hab
      have hm : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha hab (by linarith)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hpos (sub_nonneg.2 hab)) h1]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    ENNReal.ofReal_rpow_of_nonneg ha hpp, ENNReal.ofReal_rpow_of_nonneg hb hpp,
    ← ENNReal.ofReal_add (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _),
    ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hR

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the kernel `|x - y|^{-β}`, `β < d`, has
uniformly bounded integrals over a compact set `K`). -/
theorem exists_lintegral_edist_rpow_le {β : ℝ} (hβ : β < d) {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x ∈ K, ∫⁻ y in K, edist x y ^ (-β) ≤ C := by
  obtain ⟨R, hR0, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hdist : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := fun x hx y hy => by
    have := dist_triangle x 0 y
    have h1 := Metric.mem_closedBall.1 (hKR hx); have h2 := Metric.mem_closedBall.1 (hKR hy)
    rw [dist_comm 0 y] at this; linarith
  have hKf : volume K ≠ ⊤ := hK.measure_lt_top.ne
  rcases le_or_gt β 0 with hb | hb
  · refine ⟨ENNReal.ofReal (2 * R) ^ (-β) * volume K,
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hKf,
      fun x hx => ?_⟩
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun y hy => ?_
    refine ENNReal.rpow_le_rpow ?_ (by linarith)
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (hdist x hx y hy)
  · have hd : 1 ≤ Module.finrank ℝ (Rd d) := by
      rw [finrank_euclideanSpace_fin]; exact_mod_cast (show (0 : ℝ) < d by linarith)
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Rd d) (lt_of_lt_of_le zero_lt_one hd)
    set r : ℝ := 2 * R + 1
    set G : Rd d → ℝ≥0∞ := fun z => ‖z‖ₑ ^ (-β)
    refine ⟨∫⁻ z in Metric.ball 0 r, G z, ?_, fun x hx => ?_⟩
    · have hI : IntegrableOn (fun z : Rd d => ‖z‖ ^ (-β)) (Metric.ball 0 r) volume :=
        integrableOn_ball_of_norm_le_rpow (C := 1) hd (by rwa [finrank_euclideanSpace_fin])
          (Filter.Eventually.of_forall fun z => by
            rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
          (continuous_norm.measurable.pow_const (-β)).aestronglyMeasurable
      refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr_ae ?_) hI.2)
      have hne : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : Rd d) r)), z ≠ 0 :=
        ae_restrict_of_ae (ae_iff.2 (by simp))
      filter_upwards [hne] with z hz
      rw [Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hz), ofReal_norm]
    · calc ∫⁻ y in K, edist x y ^ (-β)
          ≤ ∫⁻ y, (Metric.ball 0 r).indicator G (x - y) := by
            rw [← lintegral_indicator hK.measurableSet]
            refine lintegral_mono fun y => ?_
            by_cases hy : y ∈ K
            · rw [indicator_of_mem hy, indicator_of_mem, edist_eq_enorm_sub]
              rw [mem_ball_zero_iff, ← dist_eq_norm]; linarith [hdist x hx y hy]
            · rw [indicator_of_notMem hy]; exact bot_le
        _ = ∫⁻ z in Metric.ball 0 r, G z := by
            rw [lintegral_sub_left_eq_self, lintegral_indicator measurableSet_ball]

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: Young's inequality off the diagonal,
`a c^{p-1} / e^d ≤ a^p / e^{sp+d} + c^p / e^{d - sp/(p-1)}`). -/
theorem mul_rpow_div_le_add {s p : ℝ} (hp : 1 < p) {a c e : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ⊤) :
    a * c ^ (p - 1) / e ^ (d : ℝ) ≤
      a ^ p / e ^ (s * p + d) + c ^ p / e ^ ((d : ℝ) - s * p / (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set u : ℝ := (s * p + d) / p
  set v : ℝ := (d : ℝ) - u
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hY := ENNReal.young_inequality (a / e ^ u) (c ^ (p - 1) / e ^ v) hpq
  have hed : e ^ (d : ℝ) = e ^ u * e ^ v := by
    rw [← ENNReal.rpow_add _ _ he0 het]; congr 1; simp [v]
  have hu0 : e ^ u ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 he0) het).ne'
  have hut : e ^ u ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero he0 het
  have hL : a * c ^ (p - 1) / e ^ (d : ℝ) = a / e ^ u * (c ^ (p - 1) / e ^ v) := by
    rw [hed, ENNReal.mul_div_mul_comm (Or.inl hu0) (Or.inl hut)]
  have hA : (a / e ^ u) ^ p = a ^ p / e ^ (s * p + d) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
    congr 2; simp only [u]; field_simp
  have hB : (c ^ (p - 1) / e ^ v) ^ (p / (p - 1)) = c ^ p / e ^ ((d : ℝ) - s * p / (p - 1)) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 2
    · field_simp
    · simp only [v, u]; field_simp; ring
  rw [hL]
  refine hY.trans (add_le_add ?_ ?_)
  · rw [hA]
    exact ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by simp [hp.le]))
  · rw [hB]
    refine ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' ?_)
    rw [ENNReal.one_le_ofReal, one_le_div hp1]; linarith

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the piece with `g(x)^{p-1}` is finite). -/
theorem lintegral_mul_rpow_div_lt_top {s p : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (hp : 1 < p)
    {g : Rd d → ℝ} (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) < ⊤ := by
  have hp1 : 0 < p - 1 := by linarith
  set β : ℝ := (d : ℝ) - s * p / (p - 1)
  have hβ : β < d := by
    have : 0 < s * p / (p - 1) := by positivity
    simp only [β]; linarith
  obtain ⟨C, hCt, hC⟩ := exists_lintegral_edist_rpow_le hβ hK
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Rd d)
    (by rw [finrank_euclideanSpace_fin]; omega)
  set A : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d)
  have hinner : ∀ x, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) ≤
      (∫⁻ y, A x y) + ‖g x‖ₑ ^ p * ∫⁻ y in K, edist x y ^ (-β) := by
    intro x
    calc _ ≤ ∫⁻ y in K, (A x y + ‖g x‖ₑ ^ p * edist x y ^ (-β)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae (ae_iff.2 (by simp) : ∀ᵐ y ∂volume, y ≠ x)] with y hy
          refine (mul_rpow_div_le_add (s := s) hp ((edist_pos.2 hy.symm).ne') (edist_ne_top x y)).trans_eq ?_
          rw [ENNReal.rpow_neg, div_eq_mul_inv _ (edist x y ^ β)]
      _ = (∫⁻ y in K, A x y) + ‖g x‖ₑ ^ p * ∫⁻ y in K, edist x y ^ (-β) := by
          rw [lintegral_add_right _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  have hLp : ∫⁻ x, ‖g x‖ₑ ^ p < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (by simp; linarith) ENNReal.ofReal_ne_top hgp
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  calc _ ≤ ∫⁻ x in K, ((∫⁻ y, A x y) + ‖g x‖ₑ ^ p * C) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact (hinner x).trans (by gcongr; exact hC x hx)
    _ = (∫⁻ x in K, ∫⁻ y, A x y) + (∫⁻ x in K, ‖g x‖ₑ ^ p) * C := by
        rw [lintegral_add_right _ (by fun_prop), lintegral_mul_const _ (by fun_prop)]
    _ ≤ (∫⁻ x, ∫⁻ y, A x y) + (∫⁻ x, ‖g x‖ₑ ^ p) * C := by
        gcongr <;> exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hgs, ENNReal.mul_lt_top hLp hCt.lt_top⟩

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the piece with `g(y)^{p-1}` is finite, by
symmetry and Tonelli). -/
theorem lintegral_mul_rpow_div_lt_top' {s p : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (hp : 1 < p)
    {g : Rd d → ℝ} (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g y‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) < ⊤ := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  convert lintegral_mul_rpow_div_lt_top hd hs hp hgm hgp hgs hK using 3 with x
  refine lintegral_congr fun y => ?_
  rw [enorm_sub_rev, edist_comm]

/-- **Subgoal** (Appendix C, second hypothesis of Lemma B.2 for `h = g^p`: Hölder on `K × K`). -/
theorem lintegral_rpow_sub_le {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {g : Rd d → ℝ}
    (hg0 : 0 ≤ g) (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) < ⊤ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h : ∀ x y : Rd 0, ‖g x ^ p - g y ^ p‖ₑ = 0 := fun x y => by
      rw [Subsingleton.elim x y, sub_self, enorm_zero]
    simp [h]
  set f₁ : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ)
  set f₂ : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ * ‖g y‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ)
  have hpt : ∀ x y, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) ≤
      ENNReal.ofReal p * (f₁ x y + f₂ x y) := fun x y => by
    calc _ ≤ ENNReal.ofReal p * ‖g x - g y‖ₑ * (‖g x‖ₑ ^ (p - 1) + ‖g y‖ₑ ^ (p - 1)) /
          edist x y ^ (d : ℝ) := by
          gcongr; exact enorm_rpow_sub_rpow_le hp.le (hg0 x) (hg0 y)
      _ = _ := by simp only [f₁, f₂]; rw [← ENNReal.add_div, ← mul_div_assoc, mul_assoc, mul_add]
  have hm₁ : Measurable (Function.uncurry f₁) := by fun_prop
  have hm₂ : Measurable (Function.uncurry f₂) := by fun_prop
  calc _ ≤ ∫⁻ x in K, ∫⁻ y in K, ENNReal.ofReal p * (f₁ x y + f₂ x y) := by
        gcongr with x y; exact hpt x y
    _ = ∫⁻ x in K, ENNReal.ofReal p * ((∫⁻ y in K, f₁ x y) + ∫⁻ y in K, f₂ x y) :=
        lintegral_congr fun x => by
          rw [← lintegral_add_left (by fun_prop : Measurable (f₁ x)),
            ← lintegral_const_mul _ (by fun_prop : Measurable fun y => f₁ x y + f₂ x y)]
    _ = ENNReal.ofReal p * ((∫⁻ x in K, ∫⁻ y in K, f₁ x y) + ∫⁻ x in K, ∫⁻ y in K, f₂ x y) := by
        have h₁ : Measurable fun x => ∫⁻ y in K, f₁ x y := hm₁.lintegral_prod_right'
        have h₂ : Measurable fun x => ∫⁻ y in K, f₂ x y := hm₂.lintegral_prod_right'
        rw [← lintegral_add_left h₁]
        exact lintegral_const_mul _ (h₁.add h₂)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
        ⟨lintegral_mul_rpow_div_lt_top hd hs hp hgm hgp hgs hK,
          lintegral_mul_rpow_div_lt_top' hd hs hp hgm hgp hgs hK⟩)

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null`: a finite product of absolutely
continuous measures on `ℝ` is absolutely continuous with respect to the product). -/
theorem pi_absolutelyContinuous {n : ℕ} {μ ν : Fin n → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero => rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove μ 0).symm
    have hν := (measurePreserving_piFinSuccAbove ν 0).symm
    rw [← hμ.map_eq, ← hν.map_eq]
    exact ((h 0).prod (ih fun j => h _)).map (MeasurableEquiv.measurable _)

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null`: in coordinates, the preimage of a
Lebesgue-null set under `v ↦ x₀ + ∑_i v^i e_i` is Lebesgue-null in `ℝ^{Fin d}`). -/
theorem volume_coords_preimage_null (x₀ : Rd d) {N : Set (Rd d)} (hN : volume N = 0) :
    volume {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N} = 0 := by
  have hsum : ∀ v : Fin d → ℝ, ∑ i, v i • Rd.basisVec i = MeasurableEquiv.toLp 2 (Fin d → ℝ) v := by
    intro v; ext j; simp [Rd.basisVec, Pi.single_apply]
  have hset : {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N} =
      MeasurableEquiv.toLp 2 (Fin d → ℝ) ⁻¹' ((x₀ + ·) ⁻¹' N) := by
    ext v; simp [hsum]
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
    |>.measure_preimage_equiv ((x₀ + ·) ⁻¹' N)
  rw [MeasurableEquiv.symm_symm] at h
  rw [hset, h, measure_preimage_add, hN]

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null` at one time: for `0 < t ≤ T`,
`ℙ_{x₀}(B(t) ∈ N) = 0` for a Lebesgue-null `N`, since the coordinates of `B(t) - x₀` are
independent `N(0, t)`). -/
theorem measure_path_mem_null (x₀ : Rd d) {N : Set (Rd d)} (hN : volume N = 0) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) :
    CanonicalWienerSpace.P (T := T) x₀ {ω | CanonicalWienerSpace.path ω t ∈ N} = 0 := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x₀
  have htI : t ∈ Icc 0 T := ⟨ht.le, htT⟩
  set N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  refine measure_mono_null (t := {ω | CanonicalWienerSpace.path ω t ∈ N'})
    (fun ω hω => subset_toMeasurable volume N hω) ?_
  set g : Ω' → CanonicalWienerSpace d T := fun ω' =>
    CanonicalWienerSpace.ofCoords x₀ (fun i t => W i t ω') fun i => hW i ω' with hgdef
  have hg : AEMeasurable g Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [hgdef, CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  have hev : Measurable fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩ :=
    (continuous_eval_const (⟨t, htI⟩ : Icc (0 : ℝ) T)).measurable
  have hA : {ω : CanonicalWienerSpace d T | CanonicalWienerSpace.path ω t ∈ N'} =
      (fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩) ⁻¹' N' := by
    ext ω; simp [CanonicalWienerSpace.path, CanonicalWienerSpace.B, htI]
  rw [hA, hP, Measure.map_apply_of_aemeasurable hg (hev (measurableSet_toMeasurable _ _))]
  set V : Ω' → Fin d → ℝ := fun ω' i => W i t.toNNReal ω'
  have hpre : g ⁻¹' ((fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩) ⁻¹' N') =
      V ⁻¹' {v | x₀ + ∑ i, v i • Rd.basisVec i ∈ N'} := by
    ext ω'; simp [g, V, CanonicalWienerSpace.ofCoords]
  have hVlaw : ProbabilityTheory.HasLaw V
      (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 t.toNNReal) Q :=
    (hind.comp (fun _ (f : ℝ≥0 → ℝ) => f t.toNNReal) fun _ => measurable_pi_apply _).hasLaw_pi
      fun i => (hB i).toIsPreBrownianReal.hasLaw_eval _
  have hM : MeasurableSet {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N'} :=
    (measurableSet_toMeasurable _ _).preimage (by fun_prop)
  rw [hpre, ← Measure.map_apply_of_aemeasurable hVlaw.aemeasurable hM, hVlaw.map_eq]
  have hac : Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 t.toNNReal) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous fun _ =>
      ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (by simpa using ht)
  exact hac (volume_coords_preimage_null x₀ hN')

/-- **Subgoal** (Appendix C, Brownian motion has a density at positive times: it a.s. avoids a
Lebesgue-null set at countably many positive times, e.g. the partition points `t^n_i > 0`). -/
theorem ae_forall_mem_not_mem_null {N : Set (Rd d)} (hN : volume N = 0) {S : Set ℝ}
    (hS : S.Countable) (hpos : ∀ t ∈ S, 0 < t ∧ t ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ S, CanonicalWienerSpace.path ω t ∉ N :=
  (ae_ball_iff hS).2 fun t ht => measure_eq_zero_iff_ae_notMem.1
    (measure_path_mem_null x₀ hN (hpos t ht).1 (hpos t ht).2)

end theorem_5_2

end WeakPathwiseIto
