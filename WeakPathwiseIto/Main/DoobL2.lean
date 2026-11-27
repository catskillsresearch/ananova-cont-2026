/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib

/-! # Doob's `L²` maximal inequality (discrete time)

Used for the Burkholder–Davis–Gundy inequality with `p = 2` in the proof of Proposition 5.3.
Derived from the weak-type maximal inequality `MeasureTheory.maximal_ineq` by the layer-cake
formula and Cauchy–Schwarz: `E (max_{k ≤ n} |M_k|)² ≤ 4 E |M_n|²`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal

namespace WeakPathwiseIto

namespace DoobL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Subgoal** (Doob `L²`, weak type ⇒ strong type): if `0 ≤ X, Y` with `E Y² < ∞` and
`t μ(Y ≥ t) ≤ ∫_{Y ≥ t} X` for all `t > 0`, then `E Y² ≤ 4 E X²` (layer cake:
`E Y² = 2 ∫_0^∞ t μ(Y ≥ t) dt ≤ 2 E[X Y] ≤ 2 ‖X‖₂ ‖Y‖₂`). -/
theorem lintegral_sq_le_of_weak_type {X Y : Ω → ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hXm : Measurable X) (hYm : Measurable Y) (hY2 : ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂μ < ∞)
    (h : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤ ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (X ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂μ := by
  sorry

/-- **Subgoal** (Doob's `L²` maximal inequality, discrete time): for a real martingale `M`
with `M_k ∈ L²`, `E (max_{k ≤ n} |M_k|)² ≤ 4 E |M_n|²`. -/
theorem lintegral_sup_sq_le [IsFiniteMeasure μ] {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫⁻ ω, (⨆ k ∈ range (n + 1), ‖M k ω‖ₑ) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ := by
  sorry

end DoobL2

end WeakPathwiseIto
