/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Basic.WeakLpTendsto
public import WeakPathwiseIto.Occupation.Lemma42
public import WeakPathwiseIto.Main.Theorem52Mollify
public import WeakPathwiseIto.Sobolev.Theorem21First

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace Convolution

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

/-- **Remark 4.4** (density of the occupation measure). Let `ω ∈ C([0,T]; ℝ^d) ∩ Q_π` with (6)
and `𝓛^{π_n}_ω ⇀ ℓ^{ω,π}_T` in `L^r(ℝ^d)`, `r ∈ (1, ∞]` (weak-* for `r = ∞`), `ℓ ≥ 0`. Then
`ℓ` is the density of the quadratic-variation occupation measure:
`∫ φ ℓ dx = ∫_0^T φ(ω(t)) d tr[ω]_π(t)` for `φ ∈ C_c(ℝ^d)`. -/
theorem remark_4_4_density (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (_hr : 1 < r) {ℓ : Rd d → ℝ} (_hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {φ : Rd d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x * ℓ x = ∫ t in Icc 0 T, φ (ω t) ∂hQV.traceMeasure := by
  have h1 := hweak.2.2 φ (hφ.memLp_of_hasCompactSupport hφc)
  have h2 := lemma_4_2 hω hQV hosc hφ hφc
  rw [weightedOccupationMeasure.integral_eq hω hQV hφ] at h2
  exact tendsto_nhds_unique h1 h2

/-- **Subgoal** (Remark 4.4, Hölder): for `1 < r`, `g ∈ L^{r'}` and `f ∈ L^r`, `g f` is
integrable. -/
theorem remark_4_4.integrable_mul_conj {r : ℝ≥0∞} (hr : 1 < r) {f g : Rd d → ℝ} (hf : MemLp f r)
    (hg : MemLp g r.conjExponent) : Integrable (fun x => g x * f x) := by
  have := ENNReal.HolderConjugate.conjExponent hr.le
  exact hg.integrable_mul hf

/-- **Subgoal** (Remark 4.4, lower vs. Bochner integral): for nonnegative `f, g` with `g f`
integrable, `∫⁻ g f = ∫ g f`. -/
theorem remark_4_4.lintegral_ofReal_mul_eq {f g : Rd d → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hi : Integrable (fun x => g x * f x)) :
    ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x, g x * f x) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => mul_nonneg (hg x) (hf x))]
  exact lintegral_congr fun x => (ENNReal.ofReal_mul (hg x)).symm

/-- **Remark 4.4** (explicit seminorm). Under the hypotheses of `remark_4_4_density`, for every
`h ∈ L^{r'}(ℝ^d)`, `‖h‖_{W^0_{ω,π}} = ∫ |h(x)| ℓ^{ω,π}_T(x) dx = ‖h‖_{L^1(μ^π_{ω,T})}`. -/
theorem remark_4_4_seminorm (_hω : ContinuousOn ω (Icc 0 T)) (_hQV : HasQuadraticVariation π ω)
    (_hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {E : Type*} [NormedAddCommGroup E] {h : Rd d → E} (hh : MemLp h r.conjExponent) :
    occupationSeminorm π ω h = ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (ℓ x) := by
  have hn : MemLp (fun x => ‖h x‖) r.conjExponent := hh.norm
  have hL0 : ∀ n, 0 ≤ discreteOccupationDensity (π n) ω := fun n x =>
    Finset.sum_nonneg fun i _ => discreteOccupationDensity.piece_nonneg _ _ _
  have henorm : ∀ x, ‖h x‖ₑ = ENNReal.ofReal ‖h x‖ := fun x => (ofReal_norm _).symm
  have hseq : ∀ n, ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x) =
      ENNReal.ofReal (∫ x, ‖h x‖ * discreteOccupationDensity (π n) ω x) := fun n => by
    simp_rw [henorm]
    exact remark_4_4.lintegral_ofReal_mul_eq (hL0 n) (fun x => norm_nonneg _)
      (remark_4_4.integrable_mul_conj hr (hweak.1 n) hn)
  have hlim : ∫⁻ x, ‖h x‖ₑ * ENNReal.ofReal (ℓ x) = ENNReal.ofReal (∫ x, ‖h x‖ * ℓ x) := by
    simp_rw [henorm]
    exact remark_4_4.lintegral_ofReal_mul_eq hℓ0 (fun x => norm_nonneg _)
      (remark_4_4.integrable_mul_conj hr hweak.2.1 hn)
  unfold occupationSeminorm
  simp_rw [hseq, hlim]
  exact ((ENNReal.continuous_ofReal.tendsto _).comp (hweak.2.2 _ hn)).limsup_eq

/-- **Subgoal** (Remark 4.4 inclusion, path convergence): mollifications `F ⋆ ψ_n` of a locally
integrable `F` converge to `F(x)` at every point of continuity `x`. -/
theorem remark_4_4.tendsto_mollify_of_continuousAt {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψk : ∀ n, HasCompactSupport (ψ n))
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) {x : Rd d}
    (hx : ContinuousAt F x) :
    Tendsto (fun n => ∫ y, F y * ψ n (x - y)) atTop (𝓝 (F x)) := by
  have hcs : ∀ n, Continuous fun y => ψ n (x - y) := fun n => (hψc n).comp (continuous_sub_left x)
  have hks : ∀ n, HasCompactSupport fun y => ψ n (x - y) := fun n =>
    (hψk n).comp_homeomorph (Homeomorph.subLeft x)
  have hint : ∀ n, Integrable fun y => F y * ψ n (x - y) := fun n =>
    hF.integrable_smul_right_of_hasCompactSupport (hcs n) (hks n)
  have hψi : ∀ n, Integrable fun y => ψ n (x - y) := fun n =>
    (hcs n).integrable_of_hasCompactSupport (hks n)
  have hone : ∀ n, ∫ y, ψ n (x - y) = 1 := fun n => by
    rw [integral_sub_left_eq_self (fun z => ψ n z) volume x, hψ1 n]
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn => ?_⟩
  have hsub : (∫ y, F y * ψ n (x - y)) - F x = ∫ y, (F y - F x) * ψ n (x - y) := by
    simp_rw [sub_mul]
    rw [integral_sub (hint n) ((hψi n).const_mul _), integral_const_mul, hone n, mul_one]
  rw [Real.dist_eq, hsub]
  have hbound : ∀ y, ‖(F y - F x) * ψ n (x - y)‖ ≤ ε / 2 * ψ n (x - y) := fun y => by
    rw [norm_mul, Real.norm_of_nonneg (hψ0 n _)]
    by_cases hy : ψ n (x - y) = 0
    · rw [hy]; simp
    · refine mul_le_mul_of_nonneg_right ?_ (hψ0 n _)
      have hm := hψs n (Function.mem_support.2 hy)
      rw [Metric.mem_ball, dist_zero_right, norm_sub_rev] at hm
      have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      exact (le_of_lt (hδF (by rw [dist_eq_norm]; linarith)))
  calc |∫ y, (F y - F x) * ψ n (x - y)|
      ≤ ∫ y, ε / 2 * ψ n (x - y) :=
        norm_integral_le_of_norm_le ((hψi n).const_mul _) (Eventually.of_forall hbound)
    _ = ε / 2 := by rw [integral_const_mul, hone n, mul_one]
    _ < ε := by linarith

/-- **Subgoal** (Remark 4.4 inclusion, Hölder): for `ℓ ≥ 0`,
`∫ |g| ℓ ≤ ‖g‖_{L^{r'}} ‖ℓ‖_{L^r}`. -/
theorem remark_4_4.lintegral_le_eLpNorm_mul {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓm : AEStronglyMeasurable ℓ) {E : Type*} [NormedAddCommGroup E] {g : Rd d → E}
    (hg : AEStronglyMeasurable g) :
    ∫⁻ x, ‖g x‖ₑ * ENNReal.ofReal (ℓ x) ≤ eLpNorm g r.conjExponent volume * eLpNorm ℓ r volume := by
  have := (ENNReal.HolderConjugate.conjExponent hr.le).symm
  have h := eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := volume) (φ := fun x => ‖g x‖) (f := ℓ)
    (p := r.conjExponent) (q := r) (r := 1) one_pos
  have hn : eLpNorm (fun x => ‖g x‖) r.conjExponent volume = eLpNorm g r.conjExponent volume :=
    eLpNorm_norm g hg
  rw [hn] at h
  refine le_trans (le_of_eq ?_) h
  rw [eLpNorm_one_eq_lintegral_enorm (hg.norm.smul hℓm)]
  refine lintegral_congr fun x => ?_
  change _ = ‖‖g x‖ * ℓ x‖ₑ
  rw [enorm_mul, enorm_norm, Real.enorm_of_nonneg (hℓ0 x)]

/-- **Subgoal** (Remark 4.4 inclusion, conjugate exponent): for `1 < r`, `r' = r/(r-1)` is finite,
`r' = ofReal r'.toReal` and `1 ≤ r'.toReal`. -/
theorem remark_4_4.conjExponent_facts {r : ℝ≥0∞} (hr : 1 < r) :
    r.conjExponent ≠ ∞ ∧ ENNReal.ofReal r.conjExponent.toReal = r.conjExponent ∧
      1 ≤ r.conjExponent.toReal := by
  have hne : r.conjExponent ≠ ∞ := by
    unfold ENNReal.conjExponent
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 ?_⟩
    exact (tsub_pos_of_lt hr).ne'
  refine ⟨hne, ENNReal.ofReal_toReal hne, ?_⟩
  have h1 : (1 : ℝ≥0∞) ≤ r.conjExponent := by unfold ENNReal.conjExponent; exact le_self_add
  simpa using ENNReal.toReal_mono hne h1

/-- **Subgoal** (Remark 4.4 inclusion, measurability): `ψ ⋆ H - H` is a.e. strongly measurable for
a continuous compactly supported `ψ` and a locally integrable `H`. -/
theorem remark_4_4.aestronglyMeasurable_mollify_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : Rd d → E} (hf : LocallyIntegrable f)
    (hfm : AEStronglyMeasurable f) {ψ : Rd d → ℝ} (hψc : Continuous ψ)
    (hψk : HasCompactSupport ψ) :
    AEStronglyMeasurable (fun x => (∫ y, ψ (x - y) • f y) - f x) := by
  have hconv : (fun x => ∫ y, ψ (x - y) • f y) =
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    funext x; rw [convolution_lsmul_swap]
  have hc : Continuous fun x => ∫ y, ψ (x - y) • f y := by
    rw [hconv]; exact hψk.continuous_convolution_left _ hψc hf
  exact hc.aestronglyMeasurable.sub hfm

/-- **Subgoal** (Remark 4.4 inclusion, Hessian convergence): for `H ∈ L^{r'}` and a mollifier
`ψ_n`, `‖ψ_n ⋆ H - H‖_{W^0_{ω,π}} → 0`. -/
theorem remark_4_4.tendsto_seminorm_mollify_sub (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞}
    (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Rd d → E}
    (hHr : MemLp H r.conjExponent) {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n))
    (hψk : ∀ n, HasCompactSupport (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => occupationSeminorm π ω (fun x => (∫ y, ψ n (x - y) • H y) - H x)) atTop
      (𝓝 0) := by
  obtain ⟨hne, hof, h1⟩ := remark_4_4.conjExponent_facts hr
  have hHp : MemLp H (ENNReal.ofReal r.conjExponent.toReal) := by rw [hof]; exact hHr
  have hlim := theorem_5_2.tendsto_eLpNorm_mollify_sub h1 hHp hψc hψ0 hψ1 hψs
  rw [hof] at hlim
  have h1' : (1 : ℝ≥0∞) ≤ r.conjExponent := by
    rw [← hof, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
  have hHl : LocallyIntegrable H := hHr.locallyIntegrable h1'
  have hm : ∀ n, AEStronglyMeasurable (fun x => (∫ y, ψ n (x - y) • H y) - H x) := fun n =>
    remark_4_4.aestronglyMeasurable_mollify_sub hHl hHr.aestronglyMeasurable (hψc n) (hψk n)
  have hℓ : eLpNorm ℓ r volume ≠ ∞ := hweak.2.1.eLpNorm_ne_top
  have hprod : Tendsto (fun n => eLpNorm (fun x => (∫ y, ψ n (x - y) • H y) - H x)
      r.conjExponent volume * eLpNorm ℓ r volume) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hℓ)
  have hev : ∀ᶠ n in atTop,
      eLpNorm (fun x => (∫ y, ψ n (x - y) • H y) - H x) r.conjExponent volume < ∞ :=
    (ENNReal.tendsto_nhds_zero.1 hlim) 1 one_pos |>.mono fun n hn => lt_of_le_of_lt hn ENNReal.one_lt_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with n hn
  have hM : MemLp (fun x => (∫ y, ψ n (x - y) • H y) - H x) r.conjExponent volume := hn
  rw [remark_4_4_seminorm hω hQV hosc hr hℓ0 hweak hM]
  exact remark_4_4.lintegral_le_eLpNorm_mul hr hℓ0 hweak.2.1.aestronglyMeasurable (hm n)

/-- **Remark 4.4** (inclusion). Under the hypotheses of `remark_4_4_density`,
`{F ∈ W^{2,1}(ℝ^d) ∩ C(ℝ^d) : ∇²F ∈ L^{r'}(ℝ^d)} ⊆ 𝓦^2_{ω,π}`, `r' = r/(r-1)`. -/
theorem remark_4_4 (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {F : Rd d → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hHr : MemLp H r.conjExponent) :
    F ∈ PathwiseSobolevSpace π ω := by
  obtain ⟨ψ, hψs, hψk, hψ0, hψ1, hψb⟩ := theorem_2_1_first.exists_mollifier (d := d)
  obtain ⟨G, hG⟩ := theorem_5_2.exists_isWeakGradient_of_memW (by norm_num) hF
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψs n).continuous
  have hFl : LocallyIntegrable F := hF.1.locallyIntegrable le_rfl
  refine ⟨hF, H, hH, ⟨{
    seq := fun m x => ∫ y, F y * ψ m (x - y)
    smooth := fun m _ => (theorem_5_2.mollify_mem hF (hψs m) (hψk m)).1
    sobolev := fun m _ => (theorem_5_2.mollify_mem hF (hψs m) (hψk m)).2
    tendsto_path := fun t _ =>
      remark_4_4.tendsto_mollify_of_continuousAt hFl hψc hψk hψ0 hψ1 hψb hFc.continuousAt
    tendsto_hessian := ?_ }⟩⟩
  have heq : ∀ m, (fun x => smoothHessian (fun z => ∫ y, F y * ψ m (z - y)) x - H x) =
      fun x => (∫ y, ψ m (x - y) • H y) - H x := fun m => by
    funext x; rw [theorem_5_2.smoothHessian_convolution hG hH (hψs m) (hψk m) x]
  simp_rw [heq]
  have : CompleteSpace (Rd d →L[ℝ] Rd d) := FiniteDimensional.complete ℝ _
  exact remark_4_4.tendsto_seminorm_mollify_sub hω hQV hosc hr hℓ0 hweak hHr hψc hψk hψ0 hψ1 hψb

end WeakPathwiseIto
