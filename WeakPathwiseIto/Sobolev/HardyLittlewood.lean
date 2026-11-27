/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.

Carleson's Hardy–Littlewood maximal bound is imported, unchanged, from the Carleson project
(https://github.com/fpvandoorn/carleson, `Carleson/ToMathlib/HardyLittlewood.lean`, commit
f7487cc9da4d1e73f009dc0280cd5b958f3e2c78, Apache-2.0, F. van Doorn et al. and contributors),
a Lake dependency of this project. This file only relates the paper's centred, truncated
maximal function `M_1` to Carleson's `globalMaximalFunction`.
-/
module

public import Mathlib
public import Carleson.ToMathlib.HardyLittlewood
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace WeakPathwiseIto

namespace hardyLittlewood

variable {d : ℕ}

/-- **Subgoal** (Hardy–Littlewood, `M_1 f ≤ M f` pointwise, with `M` Carleson's uncentred
`globalMaximalFunction`). -/
theorem le_globalMaximalFunction (f : Rd d → ℝ) (x : Rd d) :
    localMaximalFunction 1 f x ≤ globalMaximalFunction volume 1 f x := by
  unfold localMaximalFunction
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun _ => ?_
  exact laverage_le_globalMaximalFunction (by simpa using hr)

/-- **Subgoal** (Hardy–Littlewood, strong type `(p, p)`, `p > 1`, for measurable `f`), from
Carleson's `hasStrongType_maximalFunction_one`, whose constant
`CMB (2^d) p = 2 (p/(p-1) · 4^d)^{1/p}` gives exactly the constant below. -/
theorem lintegral_rpow_le {f : Rd d → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, localMaximalFunction 1 f x ^ p ≤
      ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
        ∫⁻ y, ‖f y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  set P : ℝ≥0 := p.toNNReal with hPdef
  have hPp : (P : ℝ) = p := Real.coe_toNNReal _ hp0.le
  have hP1 : 1 < P := by rw [← NNReal.coe_lt_coe, hPp]; simpa using hp
  have hPe : (P : ℝ≥0∞) = ENNReal.ofReal p := rfl
  have hP0 : (P : ℝ≥0∞) ≠ 0 := by rw [hPe]; exact (ENNReal.ofReal_pos.2 hp0).ne'
  have hPt : (P : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hPr : (P : ℝ≥0∞).toReal = p := by rw [ENNReal.coe_toReal, hPp]
  -- the constant
  have hK : ((CMB ((2 : ℝ≥0) ^ Module.finrank ℝ (Rd d)) P : ℝ≥0) : ℝ≥0∞) ^ p =
      ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) := by
    rw [CMB_eq_of_one_lt_q hP1, finrank_euclideanSpace_fin, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
      show (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) by
        rw [← ENNReal.ofReal_rpow_of_pos two_pos]; simp,
      ← ENNReal.ofReal_div_of_pos (by linarith),
      show (2 * (2 ^ d) ^ 2 : ℝ≥0∞) = ENNReal.ofReal (2 * (2 ^ d) ^ 2) by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow],
      ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hP1' : (1 : ℝ≥0) ≤ P := hP1.le
    push_cast [NNReal.coe_sub hP1']
    have hq : 0 < p - 1 := by linarith
    have hX : 0 ≤ p / (p - 1) * (2 ^ d) ^ 2 := by positivity
    rw [hPp, Real.mul_rpow zero_le_two (Real.rpow_nonneg hX _), Real.rpow_inv_rpow hX hp0.ne']
    have h2 : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
      rw [← Real.rpow_one_add' zero_le_two (by linarith)]; ring_nf
    rw [h2]
    have : p - 1 ≠ 0 := by linarith
    field_simp
  by_cases hfin : ∫⁻ y, ‖f y‖ₑ ^ p = ⊤
  · rw [hfin, ENNReal.mul_top]
    · exact le_top
    · rw [← hK]; exact (ENNReal.rpow_pos (by
        simp only [CMB_eq_of_one_lt_q hP1, ENNReal.coe_pos]
        exact mul_pos two_pos (NNReal.rpow_pos (mul_pos (div_pos (zero_lt_one.trans hP1)
          (tsub_pos_of_lt hP1)) (by positivity)))) ENNReal.coe_ne_top).ne'
  have hmem : MemLp f P volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt hf.aestronglyMeasurable, hPr]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin
  have h := (hasStrongType_maximalFunction_one (μ := volume) (𝓑 := (Set.univ : Set (Rd d × ℝ)))
    (c := Prod.fst) (r := Prod.snd) (ε' := ℝ) hP1 f hmem).2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt measurable_maximalFunction.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt hf.aestronglyMeasurable, hPr] at h
  have h' := ENNReal.rpow_le_rpow h hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp0.ne', ENNReal.rpow_one, ENNReal.rpow_one, hK] at h'
  refine le_trans (lintegral_mono fun x => ?_) h'
  rw [enorm_eq_self]
  exact ENNReal.rpow_le_rpow (le_globalMaximalFunction f x) hp0.le

end hardyLittlewood

end WeakPathwiseIto
