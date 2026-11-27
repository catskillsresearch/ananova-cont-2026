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
  sorry

/-- **Subgoal** (Theorem 5.1 proof, (21), telescoping): for `t ∈ [0,T]`,
`f(ω(t)) - f(ω(0)) = ∑_k (f(ω(t_{k+1} ∧ t)) - f(ω(t_k ∧ t)))`. -/
theorem sub_eq_sum_stopped (p : Partition T) (f : Rd d → ℝ) (ω : ℝ → Rd d) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    f (ω t) - f (ω 0) = ∑ k : Fin p.m, (f (ω (min (p.right k) t)) - f (ω (min (p.left k) t))) := by
  sorry

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
  sorry

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
