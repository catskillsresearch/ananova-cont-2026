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
    (hg : Measurable g) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ y in Q, g (x + s • (y - x)) * ‖y - x‖ₑ ≤
      ENNReal.ofReal (s ^ (-(d : ℝ) - 1)) *
        ∫⁻ z in Q, {z | dist z x ≤ s * D}.indicator (fun z => g z * ‖z - x‖ₑ) z := by
  sorry

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
  sorry

/-- **Subgoal** (Theorem 2.1 proof: cubes and balls): a cube or ball is convex, measurable,
bounded, of positive measure, and `(diam Q)^d ≤ K_d |Q|`. -/
theorem isCubeOrBall_props (hd : 0 < d) : ∃ K : ℝ≥0, ∀ Q : Set (Rd d), IsCubeOrBall Q →
    Convex ℝ Q ∧ MeasurableSet Q ∧ Bornology.IsBounded Q ∧ volume Q ≠ 0 ∧
      Metric.ediam Q ^ (d : ℝ) ≤ K * volume Q := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, mollification step 1): for `f` with weak gradient `G` and a
smooth compactly supported `ψ`, `f * ψ` is `C¹` with `∇(f * ψ) = G * ψ`. -/
theorem contDiff_convolution {f : Rd d → ℝ} {G : Rd d → Rd d} (hG : IsWeakGradient f G)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiff ℝ 1 (fun x => ∫ y, f y * ψ (x - y)) ∧
      ∀ x, gradient (fun x => ∫ y, f y * ψ (x - y)) x =
        ∑ i, (∫ y, Rd.coord i (G y) * ψ (x - y)) • Rd.basisVec i := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, mollification step 2: Young's inequality in `L¹`):
`‖h * ψ‖_1 ≤ ‖h‖_1 ‖ψ‖_1`. -/
theorem lintegral_convolution_le {h ψ : Rd d → ℝ} (hh : Integrable h) (hψ : Integrable ψ) :
    ∫⁻ x, ‖∫ y, h y * ψ (x - y)‖ₑ ≤ (∫⁻ y, ‖h y‖ₑ) * ∫⁻ y, ‖ψ y‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, mollification step 3: continuous compactly supported case):
for an approximate identity `ψ_n` (nonnegative, continuous, mass `1`, supported in
`B(0, 1/(n+1))`), `h * ψ_n → h` in `L¹` when `h` is continuous with compact support. -/
theorem tendsto_convolution_of_hasCompactSupport {h : Rd d → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψc : ∀ n, Continuous (ψ n)) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, mollification step 4): for `h ∈ L¹` and an approximate
identity `ψ_n` as above, `h * ψ_n → h` in `L¹`. -/
theorem tendsto_convolution {h : Rd d → ℝ} (hh : Integrable h) {ψ : ℕ → Rd d → ℝ}
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψc : ∀ n, Continuous (ψ n)) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => ∫⁻ x, ‖(∫ y, h y * ψ n (x - y)) - h x‖ₑ) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof: the Riesz potential `I¹_Q` is bounded on `L¹(Q)`):
`∫_Q ∫_Q |h(z)| / |y - z|^{d-1} dz dy ≤ C_Q ∫_Q |h|` for bounded `Q`. -/
theorem lintegral_potential_le (hd : 0 < d) {Q : Set (Rd d)} (hQb : Bornology.IsBounded Q) :
    ∃ C : ℝ≥0, ∀ h : Rd d → ℝ, AEStronglyMeasurable h →
      ∫⁻ y in Q, ∫⁻ z in Q, ‖h z‖ₑ / edist y z ^ ((d : ℝ) - 1) ≤ C * ∫⁻ z in Q, ‖h z‖ₑ := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, eq. (2) of [BH93] a.e. for `W^{1,1}`, by mollification): for
a cube or ball `Q`, for a.e. `y ∈ Q`, `|f(y) - f_Q| ≤ K ∫_Q |∇f(z)| / |y - z|^{d-1} dz`. -/
theorem poincare_ae (hd : 0 < d) : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G → ∀ Q : Set (Rd d), IsCubeOrBall Q →
      ∀ᵐ y ∂volume, y ∈ Q → ENNReal.ofReal |f y - ⨍ z in Q, f z| ≤
        K * ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1) := by
  sorry

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
  sorry

/-- **Subgoal** (Theorem 2.1 proof, [BH93, Lemma 2] with `α = 1`):
`∫_{B(x,r)} |y - z|^{1-d} dy ≤ C |B(x,r)| |x - z|^{1-d}`. -/
theorem lintegral_ball_kernel_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (x z : Rd d) {r : ℝ}, 0 < r →
    ∫⁻ y in Metric.ball x r, 1 / edist y z ^ ((d : ℝ) - 1) ≤
      C * volume (Metric.ball x r) / edist x z ^ ((d : ℝ) - 1) := by
  sorry

/-- **Subgoal** (Theorem 2.1 proof, the Lebesgue-point limit): if `x ∈ Q` is a Lebesgue point of
`f ∈ W^{1,1}` with value `c`, then `|c - f_Q| ≤ C ∫_Q |∇f(z)| / |x - z|^{d-1} dz` (average (2)
over `Q ∩ B(x,r)`, use [BH93, Lemma 2] and let `r → 0`). -/
theorem abs_sub_average_le (hd : 0 < d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (Q : Set (Rd d)) (x : Rd d) (c : ℝ), MemW 1 1 f → IsWeakGradient f G → IsCubeOrBall Q →
      x ∈ Q → Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |f y - c|) (𝓝[>] 0) (𝓝 0) →
        ENNReal.ofReal |c - ⨍ z in Q, f z| ≤
          C * ∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1) := by
  sorry

end theorem_2_1_first

end WeakPathwiseIto
