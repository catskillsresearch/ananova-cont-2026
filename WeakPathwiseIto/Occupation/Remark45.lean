/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.Remark44
public import WeakPathwiseIto.Occupation.DiscreteLocalTime
public import WeakPathwiseIto.Main.Theorem51

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {π : ℕ → Partition T} {ω : ℝ → Rd 1}

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): the coordinate of `v ∈ ℝ^1` is `v 0`. -/
theorem Rd.coord_one_apply (v : Rd 1) : Rd.coord 0 v = v 0 := by
  simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): `|v| = |v^0|` on `ℝ^1`. -/
theorem Rd.norm_one_eq (v : Rd 1) : ‖v‖ = |Rd.coord 0 v| := by
  rw [Rd.coord_one_apply]
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): the coordinate map `ℝ^1 → ℝ` is
injective. -/
theorem Rd.coord_one_injective : Function.Injective (Rd.coord (d := 1) 0) := fun v w h => by
  rw [Rd.coord_one_apply, Rd.coord_one_apply] at h
  ext i; fin_cases i; exact h

/-- **Subgoal** (Remark 4.5, eq. (7) for `d = 1`): `c_1 = 2 / |B(0,1)| = 1`. -/
theorem occupationConstant_one : occupationConstant 1 = 1 := by
  set e : Rd 1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ) with he
  have hmp : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
      (volume_preserving_funUnique (Fin 1) ℝ)
  have hnorm : ∀ x : Rd 1, ‖x‖ = |e x| := fun x => by
    simp [he, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have hball : e.symm ⁻¹' Metric.ball 0 1 = Ioo (-1) 1 := by
    ext t
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hnorm,
      MeasurableEquiv.apply_symm_apply, Set.mem_Ioo, abs_lt]
  have hvol : volume (Metric.ball (0 : Rd 1) 1) = volume (Ioo (-1 : ℝ) 1) := by
    rw [← hball, hmp.symm.measure_preimage measurableSet_ball.nullMeasurableSet]
  rw [occupationConstant, hvol, Real.volume_Ioo]
  norm_num

/-- **Subgoal** (Remark 4.5, eq. (7) for `d = 1`): the increment ball `Q` from `a` to `b` in `ℝ^1`
is the closed interval `[a ∧ b, a ∨ b]` (in coordinates). -/
theorem incrementBall_one_iff (a b x : Rd 1) : x ∈ incrementBall a b ↔
    Rd.coord 0 x ∈ Icc (min (Rd.coord 0 a) (Rd.coord 0 b)) (max (Rd.coord 0 a) (Rd.coord 0 b)) := by
  have hc : ∀ v w : Rd 1, Rd.coord 0 (v - w) = Rd.coord 0 v - Rd.coord 0 w := fun v w => by
    simp [Rd.coord_one_apply]
  have hm : Rd.coord 0 (midpoint ℝ a b) = (Rd.coord 0 a + Rd.coord 0 b) / 2 := by
    simp [Rd.coord_one_apply, midpoint_eq_smul_add]; ring
  rw [incrementBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, Rd.norm_one_eq,
    Rd.norm_one_eq,
    hc, hc, hm, mem_Icc]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := abs_le.1 h
    rcases le_total (Rd.coord 0 a) (Rd.coord 0 b) with hab | hab
    · rw [abs_sub_comm (Rd.coord 0 a),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 b - Rd.coord 0 a)] at h1 h2
      rw [min_eq_left hab, max_eq_right hab]; constructor <;> linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 a - Rd.coord 0 b)] at h1 h2
      rw [min_eq_right hab, max_eq_left hab]; constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases le_total (Rd.coord 0 a) (Rd.coord 0 b) with hab | hab
    · rw [min_eq_left hab] at h1; rw [max_eq_right hab] at h2
      rw [abs_sub_comm (Rd.coord 0 a),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 b - Rd.coord 0 a)]
      rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right hab] at h1; rw [max_eq_left hab] at h2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 a - Rd.coord 0 b)]
      rw [abs_le]; constructor <;> linarith

/-- **Remark 4.5** (one-dimensional case, identity). For `d = 1`, up to the choice of interval
endpoints (i.e. for a.e. level `u`), `𝓛^{π_n}_ω(u) = ½ (λ^{n,+}_T(u) + λ^{n,-}_T(u))`, where
`λ^{n,+}_T` is the discrete local time of `ω` along `π_n` and `λ^{n,-}_T` that of the reversed
path along the reversed partition. (`ℝ` is identified with `ℝ^1` through the coordinate.) -/
theorem remark_4_5_identity (p : Partition T) (ω : ℝ → Rd 1) :
    (fun v => discreteOccupationDensity p ω v) =ᵐ[volume] fun v =>
      1 / 2 * (discreteLocalTime p (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v) +
        discreteLocalTime.reversed p (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) := by
  sorry

/-- **Remark 4.5** (convergence and seminorm). For `d = 1`, if for some `r ∈ (1, ∞]` both
discrete local-time sequences converge to the same terminal local time,
`λ^{n,±}_T ⇀ ℓ_T` in `L^r(ℝ)`, then `𝓛^{π_n}_ω ⇀ ℓ_T` in `L^r(ℝ)` and
`‖h‖_{W^0_{ω,π}} = ∫ |h(u)| ℓ_T(u) du` for `h ∈ L^{r'}(ℝ)`. -/
theorem remark_4_5_seminorm (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd 1 → ℝ}
    (hplus : WeakLpTendsto r
      (fun n v => discreteLocalTime (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    (hminus : WeakLpTendsto r
      (fun n v => discreteLocalTime.reversed (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ) :
    WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ ∧
      ∀ (h : Rd 1 → Rd 1 →L[ℝ] Rd 1), MemLp h r.conjExponent →
        occupationSeminorm π ω h = ∫⁻ v, ‖h v‖ₑ * ENNReal.ofReal (ℓ v) := by
  sorry

/-- **Remark 4.5** (inclusion). Under the hypotheses of `remark_4_5_seminorm`,
`{F ∈ W^{2,1}(ℝ) : F'' ∈ L^{r'}(ℝ)} ⊆ 𝓦^2_{ω,π}`; `F` is taken to be its continuous
representative (`W^{2,1}(ℝ) ⊂ C^1(ℝ)`), which is what makes the trace condition automatic. -/
theorem remark_4_5_subset (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd 1 → ℝ}
    (hplus : WeakLpTendsto r
      (fun n v => discreteLocalTime (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    (hminus : WeakLpTendsto r
      (fun n v => discreteLocalTime.reversed (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    {F : Rd 1 → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd 1 → (Rd 1 →L[ℝ] Rd 1)}
    (hH : IsWeakHessian F H) (hHr : MemLp H r.conjExponent) :
    F ∈ PathwiseSobolevSpace π ω := by
  sorry

/-- **Remark 4.5** (bounded local-time case). For `d = 1`, if `𝓛^{π_n}_ω →* ℓ_T` weakly-* in
`L^∞(ℝ)`, then `sup_n ‖𝓛^{π_n}_ω‖_{L^∞} < ∞` (Banach–Steinhaus) and `𝓦^2_{ω,π} = W^{2,1}(ℝ)`
(for continuous representatives). -/
theorem remark_4_5_bounded (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {ℓ : Rd 1 → ℝ}
    (hweak : WeakLpTendsto ⊤ (fun n => discreteOccupationDensity (π n) ω) ℓ) :
    (∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n, 1 ≤ n →
        eLpNorm (discreteOccupationDensity (π n) ω) ⊤ volume ≤ K) ∧
      ∀ F : Rd 1 → ℝ, Continuous F → (F ∈ PathwiseSobolevSpace π ω ↔ MemW 2 1 F) := by
  sorry

/-- **Remark 4.5** (comparison with Davis–Obłój–Siorpaes). For `d = 1`, if a local time
`(ℓ_t)_{t ∈ [0,T]}` exists in the sense of [DOS18] and the DOS change-of-variable formula
`F(ω(t)) - F(ω(0)) = ∫_0^t F'(ω(s)) d^π ω(s) + ½ ∫ ℓ_t(u) F''(u) du` applies to the same `F`,
with the same pathwise integral (eq. (16)), then
`[F'(ω), ω]_π(t) = ∫ ℓ_t(u) F''(u) du` for `t ∈ [0, T]`. -/
theorem remark_4_5_local_time (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd 1 → ℝ} (hF : MemW 2 1 F)
    {H : Rd 1 → (Rd 1 →L[ℝ] Rd 1)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H)
    (ℓ : ℝ → Rd 1 → ℝ)
    (hDOS : ∀ t ∈ Icc 0 T, F (ω t) - F (ω 0) = weakPathwiseIntegral A t +
      1 / 2 * ∫ v, ℓ t v * Rd.coord 0 (H v (Rd.basisVec 0))) :
    ∀ t ∈ Icc 0 T, weakCovariation A t = ∫ v, ℓ t v * Rd.coord 0 (H v (Rd.basisVec 0)) := by
  intro t ht
  have h51 := theorem_5_1 hω hQV hosc hF hH A t ht
  have hd := hDOS t ht
  linarith

end WeakPathwiseIto
