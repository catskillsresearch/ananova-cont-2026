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
  sorry

/-- **Subgoal** (Definition 2.5, Young: Tonelli and translation invariance,
`∫∫ K(x - y) G(y) dy dx = (∫ K)(∫ G)`). -/
theorem lintegral_lintegral_sub_mul {d : ℕ} {K G : Rd d → ℝ≥0∞} (hK : AEMeasurable K)
    (hG : AEMeasurable G) :
    ∫⁻ x, ∫⁻ y, K (x - y) * G y = (∫⁻ z, K z) * ∫⁻ y, G y := by
  sorry

/-- **Subgoal** (Definition 2.5, Young for `1 ≤ q < ∞` in integrated form,
`∫ (∫ K(x - y) F(y) dy)^q dx ≤ (∫ K)^q ∫ F^q`). -/
theorem lintegral_rpow_conv_le {d : ℕ} {q : ℝ} (hq : 1 ≤ q) {K F : Rd d → ℝ≥0∞}
    (hK : AEMeasurable K) (hF : AEMeasurable F) :
    ∫⁻ x, (∫⁻ y, K (x - y) * F y) ^ q ≤ (∫⁻ z, K z) ^ q * ∫⁻ y, F y ^ q := by
  sorry

/-- **Subgoal** (Definition 2.5, Young for `p = ∞`: an a.e. bound on `F` passes through). -/
theorem lintegral_conv_le_of_ae_le {d : ℕ} {K F : Rd d → ℝ≥0∞} (hK : AEMeasurable K) {C : ℝ≥0∞}
    (hF : ∀ᵐ y, F y ≤ C) (x : Rd d) :
    ∫⁻ y, K (x - y) * F y ≤ (∫⁻ z, K z) * C := by
  sorry

end young

end BesselSpace

end WeakPathwiseIto
