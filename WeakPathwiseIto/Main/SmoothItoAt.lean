/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Occupation.Lemma42
public import WeakPathwiseIto.Smooth.Proposition31
public import WeakPathwiseIto.Smooth.FollmerItoFormula

/-! # The smooth pathwise Itô formula at every `t ∈ [0,T]` (eq. (21) of Theorem 5.1)

Corollary 3.2 is stated at `t = T`; the proof of Theorem 5.1 uses it at every `t ∈ [0,T]`
(eq. (21)). We derive it from Proposition 3.1 by the trapezoid rule on each stopped increment. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

namespace theorem_5_1

namespace ito_at

/-- **Subgoal** (Theorem 5.1 proof, (21), trapezoid rule): if `‖∇²f(z) - ∇²f(x)‖ ≤ ε` on the
segment `[x, y]`, then `|f(y) - f(x) - ∇f(x)·(y-x) - ½(∇f(y) - ∇f(x))·(y-x)| ≤ 2ε|y-x|²`. -/
theorem abs_trapezoid_le {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) {x y : Rd d} {ε : ℝ}
    (hε : ∀ z ∈ segment ℝ x y, ‖smoothHessian f z - smoothHessian f x‖ ≤ ε) :
    |f y - f x - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪gradient f y - gradient f x, y - x⟫| ≤
      2 * ε * ‖y - x‖ ^ 2 := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hgd : Differentiable ℝ (gradient f) :=
    (L.contDiff.comp (hf.fderiv_right (m := 1) (by norm_num))).differentiable (by norm_num)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε x (left_mem_segment ℝ x y))
  have h1 := follmer_ito_formula.abs_taylor2_le hf hε
  have h2 := proposition_3_1.norm_taylor_le (f := gradient f) hgd (x := y) (y := x) (ε := ε)
    (fun z hz => hε z (segment_symm ℝ y x ▸ hz))
  have e : gradient f x - gradient f y - fderiv ℝ (gradient f) x (x - y) =
      -(gradient f y - gradient f x - smoothHessian f x (y - x)) := by
    have : fderiv ℝ (gradient f) x (x - y) = -(smoothHessian f x (y - x)) := by
      rw [← map_neg, neg_sub]; rfl
    rw [this]; abel
  rw [e, norm_neg, norm_sub_rev x y] at h2
  have h3 : |⟪gradient f y - gradient f x, y - x⟫ - ⟪smoothHessian f x (y - x), y - x⟫| ≤
      ε * ‖y - x‖ ^ 2 := by
    rw [← inner_sub_left]
    calc _ ≤ ‖gradient f y - gradient f x - smoothHessian f x (y - x)‖ * ‖y - x‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (ε * ‖y - x‖) * ‖y - x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ε * ‖y - x‖ ^ 2 := by ring
  have hsplit : f y - f x - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪gradient f y - gradient f x, y - x⟫ =
      (f y - f x - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪smoothHessian f x (y - x), y - x⟫) -
        1 / 2 * (⟪gradient f y - gradient f x, y - x⟫ - ⟪smoothHessian f x (y - x), y - x⟫) := by
    ring
  rw [hsplit]
  calc _ ≤ |f y - f x - ⟪gradient f x, y - x⟫ - 1 / 2 * ⟪smoothHessian f x (y - x), y - x⟫| +
        |1 / 2 * (⟪gradient f y - gradient f x, y - x⟫ - ⟪smoothHessian f x (y - x), y - x⟫)| :=
        abs_sub _ _
    _ ≤ ε * ‖y - x‖ ^ 2 + 1 / 2 * (ε * ‖y - x‖ ^ 2) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
        gcongr
    _ ≤ 2 * ε * ‖y - x‖ ^ 2 := by nlinarith [sq_nonneg ‖y - x‖, mul_nonneg hε0 (sq_nonneg ‖y - x‖)]

/-- **Subgoal** (Theorem 5.1 proof, (21), splitting a stopped sum): for `φ` vanishing on the
diagonal, `∑_k φ(ω(t_k ∧ t), ω(t_{k+1} ∧ t))` is the sum over complete intervals `t_{k+1} ≤ t`
plus the straddling interval `t_k < t < t_{k+1}`. -/
theorem stopped_sum_eq (p : Partition T) (φ : Rd d → Rd d → ℝ) (hφ : ∀ a, φ a a = 0)
    (ω : ℝ → Rd d) (t : ℝ) :
    ∑ k : Fin p.m, φ (ω (min (p.left k) t)) (ω (min (p.right k) t)) =
      ∑ k ∈ Finset.univ.filter (fun k => p.right k ≤ t), φ (ω (p.left k)) (ω (p.right k)) +
      ∑ k ∈ Finset.univ.filter (fun k => p.left k < t ∧ t < p.right k), φ (ω (p.left k)) (ω t) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlr := p.left_lt_right k
  by_cases h1 : p.right k ≤ t
  · have h2 : ¬ (p.left k < t ∧ t < p.right k) := fun h => absurd h1 (not_le.2 h.2)
    rw [if_pos h1, if_neg h2, min_eq_left h1, min_eq_left (hlr.le.trans h1), add_zero]
  · by_cases h3 : p.left k < t
    · have h2 : p.left k < t ∧ t < p.right k := ⟨h3, not_le.1 h1⟩
      rw [if_neg h1, if_pos h2, min_eq_right (not_le.1 h1).le, min_eq_left h3.le, zero_add]
    · have h2 : ¬ (p.left k < t ∧ t < p.right k) := fun h => h3 h.1
      rw [if_neg h1, if_neg h2, min_eq_right (not_le.1 h1).le, min_eq_right (not_lt.1 h3), hφ,
        add_zero]

/-- **Subgoal** (Theorem 5.1 proof, (21), telescoping): for `t ∈ [0,T]`,
`f(ω(t)) - f(ω(0)) = ∑_k (f(ω(t_{k+1} ∧ t)) - f(ω(t_k ∧ t)))`. -/
theorem sub_eq_sum_stopped (p : Partition T) (f : Rd d → ℝ) (ω : ℝ → Rd d) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    f (ω t) - f (ω 0) = ∑ k : Fin p.m, (f (ω (min (p.right k) t)) - f (ω (min (p.left k) t))) := by
  have h1 := Fin.sum_univ_succ (fun j => f (ω (min (p.t j) t)))
  have h2 := Fin.sum_univ_castSucc (fun j => f (ω (min (p.t j) t)))
  have hT : f (ω t) = f (ω (min (p.t (Fin.last p.m)) t)) := by rw [p.t_last, min_eq_right ht.2]
  have h0 : f (ω 0) = f (ω (min (p.t 0) t)) := by rw [p.t_zero, min_eq_left ht.1]
  rw [Finset.sum_sub_distrib, hT, h0]
  change _ = ∑ k : Fin p.m, f (ω (min (p.t k.succ) t)) - ∑ k : Fin p.m, f (ω (min (p.t k.castSucc) t))
  linarith

/-- **Subgoal** (Theorem 5.1 proof, (21), the trapezoid remainders vanish): for `f ∈ C²_b` and
`t ∈ [0,T]`, `∑_k (f(b_k) - f(a_k) - ∇f(a_k)·(b_k - a_k) - ½(∇f(b_k) - ∇f(a_k))·(b_k - a_k)) → 0`
with `a_k = ω(t_k ∧ t)`, `b_k = ω(t_{k+1} ∧ t)`. -/
theorem tendsto_trapezoid {π : ℕ → Partition T} {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ}
    (hf : ContDiffBounded 2 f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k : Fin (π n).m,
      (f (ω (min ((π n).right k) t)) - f (ω (min ((π n).left k) t)) -
        ⟪gradient f (ω (min ((π n).left k) t)),
          ω (min ((π n).right k) t) - ω (min ((π n).left k) t)⟫ -
        1 / 2 * ⟪gradient f (ω (min ((π n).right k) t)) - gradient f (ω (min ((π n).left k) t)),
          ω (min ((π n).right k) t) - ω (min ((π n).left k) t)⟫)) atTop (𝓝 0) := by
  set φ : Rd d → Rd d → ℝ := fun a b => f b - f a - ⟪gradient f a, b - a⟫ -
    1 / 2 * ⟪gradient f b - gradient f a, b - a⟫ with hφdef
  have hφ : ∀ a, φ a a = 0 := fun a => by simp [hφdef]
  refine Tendsto.congr (fun n => (stopped_sum_eq (π n) φ hφ ω t).symm) ?_
  have hg := follmer_ito_formula.contDiffBounded_gradient hf
  have hHc : Continuous (smoothHessian f) := hg.1.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hω).isBounded.exists_norm_le
  have hωC : ∀ s ∈ Icc 0 T, ‖ω s‖ ≤ C := fun s hs => hC _ (mem_image_of_mem ω hs)
  have hu := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : Rd d) (C + 1)).uniformContinuousOn_of_continuous hHc.continuousOn)
  set M : ℝ := |hQV.trace T| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hevS : ∀ᶠ n in atTop, ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 ≤ M :=
    ((lemma_4_2.tendsto_sum_sq hQV).eventually (gt_mem_nhds
      (show hQV.trace T < M by rw [hM]; linarith [le_abs_self (hQV.trace T)]))).mono
        fun n h => h.le
  have hcard : ∀ n, (Finset.univ.filter
      (fun k => (π n).left k < t ∧ t < (π n).right k)).card ≤ 1 := fun n => by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have key : ∀ a b : Fin (π n).m, a < b → (π n).right a ≤ (π n).left b := fun a b hab =>
      (π n).strictMono.monotone (by rw [Fin.le_def]; simp; omega)
    rcases lt_trichotomy a b with h | h | h
    · exact absurd ((key a b h).trans_lt hb.1) (not_lt.2 ha.2.le)
    · exact h
    · exact absurd ((key b a h).trans_lt ha.1) (not_lt.2 hb.2.le)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set ε' := ε / (4 * (M + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδD⟩ := hu ε' hε'0
  filter_upwards [hevS, hosc.eventually (gt_mem_nhds (lt_min hδ one_pos))] with n hn hon
  have hterm : ∀ k : Fin (π n).m, ∀ s ∈ Icc ((π n).left k) ((π n).right k),
      |φ (ω ((π n).left k)) (ω s)| ≤ 2 * ε' * ‖ω s - ω ((π n).left k)‖ ^ 2 := by
    intro k s hs
    have hΔ := proposition_3_1.norm_sub_left_le hω (π n) k hs
    have hΔ' : ‖ω s - ω ((π n).left k)‖ < min δ 1 := hΔ.trans_lt hon
    have ha : ‖ω ((π n).left k)‖ ≤ C := hωC _ ((π n).t_mem _)
    have haB : ω ((π n).left k) ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    refine abs_trapezoid_le hf.1 fun z hz => ?_
    have hz' : z ∈ Metric.closedBall (ω ((π n).left k)) ‖ω s - ω ((π n).left k)‖ :=
      (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (norm_nonneg _))
        (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz'
    have hzB : z ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ = ‖(z - ω ((π n).left k)) + ω ((π n).left k)‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - ω ((π n).left k)‖ + ‖ω ((π n).left k)‖ := norm_add_le _ _
        _ ≤ C + 1 := by linarith [min_le_right δ 1]
    have := hδD z hzB _ haB (by rw [dist_eq_norm]; linarith [min_le_left δ 1])
    rw [dist_eq_norm] at this
    exact this.le
  have hA : |∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      φ (ω ((π n).left k)) (ω ((π n).right k))| ≤ 2 * ε' * M := by
    calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
          |φ (ω ((π n).left k)) (ω ((π n).right k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
          2 * ε' * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 :=
          Finset.sum_le_sum fun k _ =>
            hterm k _ ⟨((π n).left_lt_right k).le, le_rfl⟩
      _ ≤ ∑ k, 2 * ε' * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun k _ _ => by positivity
      _ = 2 * ε' * ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 2 * ε' * M := mul_le_mul_of_nonneg_left hn (by positivity)
  have hB : |∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
      φ (ω ((π n).left k)) (ω t)| ≤ 2 * ε' := by
    have hb : ∀ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
        |φ (ω ((π n).left k)) (ω t)| ≤ 2 * ε' := fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hs : t ∈ Icc ((π n).left k) ((π n).right k) := ⟨hk.1.le, hk.2.le⟩
      have hΔ := (proposition_3_1.norm_sub_left_le hω (π n) k hs).trans_lt hon
      have h1 : ‖ω t - ω ((π n).left k)‖ ^ 2 ≤ 1 := by
        have := min_le_right δ 1
        have h0 := norm_nonneg (ω t - ω ((π n).left k))
        nlinarith
      calc _ ≤ 2 * ε' * ‖ω t - ω ((π n).left k)‖ ^ 2 := hterm k t hs
        _ ≤ 2 * ε' * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * ε' := mul_one _
    calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
          |φ (ω ((π n).left k)) (ω t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k)).card •
            (2 * ε') := Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ 1 • (2 * ε') := nsmul_le_nsmul_left (by positivity) (hcard n)
      _ = 2 * ε' := one_nsmul _
  rw [Real.dist_eq, sub_zero]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * ε' * M + 2 * ε' := add_le_add hA hB
    _ = ε / 2 := by rw [hε']; field_simp; ring
    _ < ε := by linarith

end ito_at

/-- **Subgoal** (Theorem 5.1 proof, eq. (21)): the smooth pathwise Itô formula at every
`t ∈ [0,T]`: for `f ∈ C²_b` the left Riemann sums converge to
`f(ω(t)) - f(ω(0)) - ½ [∇f(ω), ω]_π(t)`. -/
theorem ito_at {π : ℕ → Partition T} {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) {f : Rd d → ℝ}
    (hf : ContDiffBounded 2 f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => follmerIntegral.riemannSum (π n) (gradient f) ω t) atTop
      (𝓝 (f (ω t) - f (ω 0) - 1 / 2 * pathwiseCovariation π (gradient f) ω t)) := by
  sorry

end theorem_5_1

end WeakPathwiseIto
