/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Occupation.Lemma42
public import WeakPathwiseIto.Smooth.Proposition31

/-! # Eq. (18) of Theorem 5.1, for `C²_b` functions -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

namespace theorem_5_1

namespace eq_18

/-! ### Eq. (18), proved directly for `C²_b` functions

The paper derives (18) from the second estimate of Theorem 2.1 applied per increment; that step
does not hold as written (see WeakPathwiseIto.md, "Theorem 5.1: proof of (18)"). We prove (18)
for `H ∈ C²_b` directly: on each increment `∇²H` is nearly constant (uniform continuity near the
compact set `ω([0,T])` and (6)), while `∫ 𝓛^{n,i}_ω = |δω|²`. -/

/-- **Subgoal** (Theorem 5.1 proof, (18), mean value step): if `‖∇²H‖ ≤ M` on the increment ball
`Q` of `a, b`, then `|(∇H(b) - ∇H(a)) · (b - a)| ≤ M |b - a|²`. -/
theorem abs_inner_increment_le {H : Rd d → ℝ} (hH : ContDiff ℝ 2 H) {a b : Rd d} {M : ℝ}
    (hM : ∀ z ∈ incrementBall a b, ‖smoothHessian H z‖ ≤ M) :
    |⟪gradient H b - gradient H a, b - a⟫| ≤ M * ‖b - a‖ ^ 2 := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient H = L ∘ fderiv ℝ H := rfl
  have hD : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (m := 1) (by norm_num)
  have hgd : Differentiable ℝ (gradient H) := by
    rw [hg]; exact (L.contDiff.comp hD).differentiable one_ne_zero
  have ha : a ∈ incrementBall a b := by
    rw [incrementBall, Metric.mem_closedBall, dist_comm, dist_midpoint_left (𝕜 := ℝ)]
    simp
    linarith [dist_nonneg (x := a) (y := b)]
  have hb : b ∈ incrementBall a b := by
    rw [incrementBall, Metric.mem_closedBall, dist_comm, dist_midpoint_right (𝕜 := ℝ)]
    simp
    linarith [dist_nonneg (x := a) (y := b)]
  have hlip : ‖gradient H b - gradient H a‖ ≤ M * ‖b - a‖ :=
    (convex_closedBall _ _).norm_image_sub_le_of_norm_fderiv_le (fun z _ => hgd z) hM ha hb
  calc |⟪gradient H b - gradient H a, b - a⟫| ≤ ‖gradient H b - gradient H a‖ * ‖b - a‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (M * ‖b - a‖) * ‖b - a‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
    _ = M * ‖b - a‖ ^ 2 := by ring

/-- **Subgoal** (Theorem 5.1 proof, (18), lower bound by the occupation density): if
`m ≤ ‖G‖` on the increment ball `Q` of `a, b`, then `m |b - a|² ≤ ∫ |G| 𝓛^{n,i}_ω`. -/
theorem le_lintegral_piece {G : Rd d → (Rd d →L[ℝ] Rd d)} {a b : Rd d} {m : ℝ}
    (hm : ∀ z ∈ incrementBall a b, m ≤ ‖G z‖) :
    ENNReal.ofReal (m * ‖b - a‖ ^ 2) ≤
      ∫⁻ x, ‖G x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) := by
  rcases le_or_gt m 0 with hm0 | hm0
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hm0 (sq_nonneg _))]
    exact zero_le
  have hpt : ∀ x, ENNReal.ofReal m * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      ‖G x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) := fun x => by
    by_cases hx : x ∈ incrementBall a b
    · refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hm x hx)
    · have : discreteOccupationDensity.piece a b x = 0 := by
        unfold discreteOccupationDensity.piece
        split_ifs
        · rfl
        · exact indicator_of_notMem hx _
      rw [this, ENNReal.ofReal_zero, mul_zero, mul_zero]
  have hint : ∫⁻ x, ENNReal.ofReal (discreteOccupationDensity.piece a b x) =
      ENNReal.ofReal (‖b - a‖ ^ 2) := by
    rw [← discreteOccupationDensity.integral_piece a b,
      ofReal_integral_eq_lintegral_ofReal (discreteOccupationDensity.integrable_piece a b)
        (Eventually.of_forall fun x => discreteOccupationDensity.piece_nonneg a b x)]
  calc ENNReal.ofReal (m * ‖b - a‖ ^ 2)
      = ENNReal.ofReal m * ∫⁻ x, ENNReal.ofReal (discreteOccupationDensity.piece a b x) := by
        rw [hint, ENNReal.ofReal_mul hm0.le]
    _ = ∫⁻ x, ENNReal.ofReal m * ENNReal.ofReal (discreteOccupationDensity.piece a b x) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ _ := lintegral_mono hpt

/-- **Subgoal** (Theorem 5.1 proof, (18), one increment): if `∇²H` varies by at most `ε` on the
increment ball `Q` of `a, b` (from `a`), then
`|(∇H(b) - ∇H(a)) · (b - a)| ≤ ∫ |∇²H| 𝓛^{n,i}_ω + 2ε |b - a|²`. -/
theorem abs_inner_increment_le_lintegral {H : Rd d → ℝ} (hH : ContDiff ℝ 2 H) {a b : Rd d}
    {ε : ℝ} (hε : ∀ z ∈ incrementBall a b, ‖smoothHessian H z - smoothHessian H a‖ ≤ ε) :
    ENNReal.ofReal |⟪gradient H b - gradient H a, b - a⟫| ≤
      (∫⁻ x, ‖smoothHessian H x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x)) +
        ENNReal.ofReal (2 * ε * ‖b - a‖ ^ 2) := by
  set m0 := ‖smoothHessian H a‖ with hm0
  have hup : ∀ z ∈ incrementBall a b, ‖smoothHessian H z‖ ≤ m0 + ε := fun z hz => by
    have := norm_le_insert' (smoothHessian H z) (smoothHessian H a)
    linarith [hε z hz]
  have hlo : ∀ z ∈ incrementBall a b, m0 - ε ≤ ‖smoothHessian H z‖ := fun z hz => by
    have := norm_le_insert' (smoothHessian H a) (smoothHessian H z)
    rw [norm_sub_rev] at this
    linarith [hε z hz]
  calc ENNReal.ofReal |⟪gradient H b - gradient H a, b - a⟫|
      ≤ ENNReal.ofReal ((m0 + ε) * ‖b - a‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (abs_inner_increment_le hH hup)
    _ = ENNReal.ofReal ((m0 - ε) * ‖b - a‖ ^ 2 + 2 * ε * ‖b - a‖ ^ 2) := by congr 1; ring
    _ ≤ ENNReal.ofReal ((m0 - ε) * ‖b - a‖ ^ 2) + ENNReal.ofReal (2 * ε * ‖b - a‖ ^ 2) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add_left (le_lintegral_piece hlo) _

/-- **Subgoal** (Theorem 5.1 proof, (18), uniform continuity): for `H ∈ C²_b` and `ε > 0`,
eventually `‖∇²H(z) - ∇²H(ω(t_k))‖ ≤ ε` on every increment ball of `π_n`. -/
theorem eventually_hessian_close {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ}
    (hH : ContDiffBounded 2 H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ k : Fin (π n).m,
      ∀ z ∈ incrementBall (ω ((π n).left k)) (ω ((π n).right k)),
        ‖smoothHessian H z - smoothHessian H (ω ((π n).left k))‖ ≤ ε := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, (18), summing the increments): for `H ∈ C²_b` and `ε > 0`,
eventually `∑_k |(∇H(ω(t_{k+1})) - ∇H(ω(t_k))) · δω_k| ≤ ∫ |∇²H| 𝓛^{π_n}_ω + ε`. -/
theorem eventually_sum_abs_le {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ} (hH : ContDiffBounded 2 H) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (∑ k : Fin (π n).m,
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫|) ≤
        (∫⁻ x, ‖smoothHessian H x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) +
          ENNReal.ofReal ε := by
  sorry

/-- **Subgoal** (Theorem 5.1 proof, (18), the stopped sum): for `H ∈ C²_b` and `t ∈ [0,T]`,
`|∑_k (∇H(ω(t_{k+1} ∧ t)) - ∇H(ω(t_k ∧ t))) · (ω(t_{k+1} ∧ t) - ω(t_k ∧ t))|` is at most the
full sum `∑_k |(∇H(ω(t_{k+1})) - ∇H(ω(t_k))) · δω_k|` plus a term `→ 0` (the straddling
interval). -/
theorem abs_riemannSum_le {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hosc : pathOscillation.Vanishes ω π) {H : Rd d → ℝ}
    (hH : ContDiffBounded 2 H) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n,
      |pathwiseCovariation.riemannSum (π n) (gradient H) ω t| ≤
        (∑ k : Fin (π n).m,
          |⟪gradient H (ω ((π n).right k)) - gradient H (ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫|) + e n := by
  sorry

end eq_18

/-- **Subgoal** (Theorem 5.1 proof, eq. (18)): for `H ∈ C²_b(ℝ^d)`,
`|[∇H(ω), ω]_π(t)| ≤ C_d ‖∇²H‖_{W^0_{ω,π}}` (proved directly; see `eq_18`). -/
theorem eq_18 {π : ℕ → Partition T} {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) :
    ∃ C : ℝ≥0, ∀ (H : Rd d → ℝ), ContDiffBounded 2 H → ∀ t ∈ Icc 0 T,
      ENNReal.ofReal |pathwiseCovariation π (gradient H) ω t| ≤
        C * occupationSeminorm π ω (smoothHessian H) := by
  sorry

end theorem_5_1

end WeakPathwiseIto
