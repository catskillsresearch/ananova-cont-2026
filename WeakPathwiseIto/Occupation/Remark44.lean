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

/-- **Remark 4.4** (inclusion). Under the hypotheses of `remark_4_4_density`,
`{F ∈ W^{2,1}(ℝ^d) ∩ C(ℝ^d) : ∇²F ∈ L^{r'}(ℝ^d)} ⊆ 𝓦^2_{ω,π}`, `r' = r/(r-1)`. -/
theorem remark_4_4 (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd d → ℝ} (hℓ0 : 0 ≤ ℓ)
    (hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ)
    {F : Rd d → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hHr : MemLp H r.conjExponent) :
    F ∈ PathwiseSobolevSpace π ω := by
  sorry

end WeakPathwiseIto
