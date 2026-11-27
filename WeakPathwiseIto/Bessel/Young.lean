/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

/-! # Young's convolution inequality `‖k ⋆ f‖_p ≤ ‖k‖_1 ‖f‖_p` (steps)

Mathlib has only the Hölder-conjugate pointwise bound `enorm_convolution_le`; here we prove the
`L¹ ⋆ Lᵖ → Lᵖ` form for nonnegative extended-real integrands, used for Definition 2.5
(`BesselSpace.eLpNorm_potential_le`). Route: weighted Jensen via Hölder, then Tonelli and
translation invariance of Lebesgue measure; `p = ∞` by an a.e. bound. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace WeakPathwiseIto

namespace BesselSpace

namespace young

/-- **Subgoal** (Definition 2.5, Young: weighted Jensen via Hölder,
`(∫ u v)^q ≤ (∫ u)^{q-1} ∫ u v^q` for `q ≥ 1`). -/
theorem rpow_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ}
    (hq : 1 ≤ q) {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    (∫⁻ a, u a * v a ∂μ) ^ q ≤ (∫⁻ a, u a ∂μ) ^ (q - 1) * ∫⁻ a, u a * v a ^ q ∂μ := by
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · simp [← hq1]
  set r : ℝ := q / (q - 1) with hrdef
  have hqr : q.HolderConjugate r := .conjExponent hq1
  have hq0 : 0 < q := by linarith
  have hfg : ∀ a, u a * v a = (u a ^ (1 / q) * v a) * (u a ^ (1 / q)) ^ (q - 1) := by
    intro a
    rw [mul_comm (u a ^ (1 / q)) (v a), mul_assoc, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by positivity)
        (mul_nonneg (by positivity) (by linarith)),
      show 1 / q + 1 / q * (q - 1) = 1 by field_simp; ring, ENNReal.rpow_one, mul_comm]
  have hf2 : ∀ a, (u a ^ (1 / q) * v a) ^ q = u a * v a ^ q := by
    intro a
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne',
      ENNReal.rpow_one]
  have hg2 : ∀ a, (u a ^ (1 / q)) ^ q = u a := by
    intro a
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hH : ∫⁻ a, u a * v a ∂μ ≤
      (∫⁻ a, u a * v a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, u a ∂μ) ^ (1 / r) := by
    calc ∫⁻ a, u a * v a ∂μ
        = ∫⁻ a, (u a ^ (1 / q) * v a) * (u a ^ (1 / q)) ^ (q - 1) ∂μ := lintegral_congr hfg
      _ ≤ (∫⁻ a, (u a ^ (1 / q) * v a) ^ q ∂μ) ^ (1 / q) * (∫⁻ a, (u a ^ (1 / q)) ^ q ∂μ) ^ (1 / r) :=
          ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hqr
            ((hu.pow_const _).mul hv) (hu.pow_const _)
      _ = _ := by simp_rw [hf2, hg2]
  have h1r : 1 / r * q = q - 1 := by
    rw [← hqr.div_conj_eq_sub_one]; ring
  calc (∫⁻ a, u a * v a ∂μ) ^ q
      ≤ ((∫⁻ a, u a * v a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, u a ∂μ) ^ (1 / r)) ^ q :=
        ENNReal.rpow_le_rpow hH hq0.le
    _ = (∫⁻ a, u a ∂μ) ^ (q - 1) * ∫⁻ a, u a * v a ^ q ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hq0.ne', ENNReal.rpow_one, h1r, mul_comm]

/-- **Subgoal** (Definition 2.5, Young: Tonelli and translation invariance,
`∫∫ K(x - y) G(y) dy dx = (∫ K)(∫ G)`). -/
theorem lintegral_lintegral_sub_mul {d : ℕ} {K G : Rd d → ℝ≥0∞} (hK : AEMeasurable K)
    (hG : AEMeasurable G) :
    ∫⁻ x, ∫⁻ y, K (x - y) * G y = (∫⁻ z, K z) * ∫⁻ y, G y := by
  have hprod : AEMeasurable (Function.uncurry fun x y => K (x - y) * G y)
      ((volume : Measure (Rd d)).prod volume) :=
    (hK.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
        (hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  rw [lintegral_lintegral_swap hprod]
  calc ∫⁻ y, ∫⁻ x, K (x - y) * G y
      = ∫⁻ y, (∫⁻ x, K (x - y)) * G y := lintegral_congr fun y =>
        lintegral_mul_const'' _
        (hK.comp_quasiMeasurePreserving (measurePreserving_sub_right volume y).quasiMeasurePreserving)
    _ = ∫⁻ y, (∫⁻ z, K z) * G y := lintegral_congr fun y => by
        rw [lintegral_sub_right_eq_self]
    _ = (∫⁻ z, K z) * ∫⁻ y, G y := lintegral_const_mul'' _ hG

/-- **Subgoal** (Definition 2.5, Young for `1 ≤ q < ∞` in integrated form,
`∫ (∫ K(x - y) F(y) dy)^q dx ≤ (∫ K)^q ∫ F^q`). -/
theorem lintegral_rpow_conv_le {d : ℕ} {q : ℝ} (hq : 1 ≤ q) {K F : Rd d → ℝ≥0∞}
    (hK : AEMeasurable K) (hF : AEMeasurable F) :
    ∫⁻ x, (∫⁻ y, K (x - y) * F y) ^ q ≤ (∫⁻ z, K z) ^ q * ∫⁻ y, F y ^ q := by
  set A := ∫⁻ z, K z with hA
  have hFq : AEMeasurable (fun y => F y ^ q) := hF.pow_const q
  have hKx : ∀ x : Rd d, AEMeasurable (fun y => K (x - y)) := fun x =>
    hK.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  have hprod : AEMeasurable (fun p : Rd d × Rd d => K (p.1 - p.2) * F p.2 ^ q)
      ((volume : Measure (Rd d)).prod volume) :=
    (hK.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
        (hFq.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hB : AEMeasurable (fun x => ∫⁻ y, K (x - y) * F y ^ q) := hprod.lintegral_prod_right'
  calc ∫⁻ x, (∫⁻ y, K (x - y) * F y) ^ q
      ≤ ∫⁻ x, (∫⁻ y, K (x - y)) ^ (q - 1) * ∫⁻ y, K (x - y) * F y ^ q :=
        lintegral_mono fun x => rpow_lintegral_mul_le hq (hKx x) hF
    _ = ∫⁻ x, A ^ (q - 1) * ∫⁻ y, K (x - y) * F y ^ q := lintegral_congr fun x => by
        rw [lintegral_sub_left_eq_self]
    _ = A ^ (q - 1) * ∫⁻ x, ∫⁻ y, K (x - y) * F y ^ q := lintegral_const_mul'' _ hB
    _ = A ^ (q - 1) * (A * ∫⁻ y, F y ^ q) := by rw [lintegral_lintegral_sub_mul hK hFq]
    _ = A ^ q * ∫⁻ y, F y ^ q := by
        rw [← mul_assoc]
        congr 1
        calc A ^ (q - 1) * A = A ^ (q - 1) * A ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = A ^ (q - 1 + 1) := (ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one).symm
          _ = A ^ q := by ring_nf

/-- **Subgoal** (Definition 2.5, Young for `p = ∞`: an a.e. bound on `F` passes through). -/
theorem lintegral_conv_le_of_ae_le {d : ℕ} {K F : Rd d → ℝ≥0∞} (hK : AEMeasurable K) {C : ℝ≥0∞}
    (hF : ∀ᵐ y, F y ≤ C) (x : Rd d) :
    ∫⁻ y, K (x - y) * F y ≤ (∫⁻ z, K z) * C := by
  calc ∫⁻ y, K (x - y) * F y ≤ ∫⁻ y, K (x - y) * C :=
        lintegral_mono_ae (hF.mono fun y hy => mul_le_mul' le_rfl hy)
    _ = (∫⁻ y, K (x - y)) * C := lintegral_mul_const'' _
        (hK.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving)
    _ = (∫⁻ z, K z) * C := by rw [lintegral_sub_left_eq_self]

end young

end BesselSpace

end WeakPathwiseIto
