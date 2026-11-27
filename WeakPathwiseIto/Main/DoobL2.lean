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

/-- **Subgoal** (Doob `L²`, weak type ⇒ strong type): if `0 ≤ Y`, `X` measurable, `E Y² < ∞`
and `t μ(Y ≥ t) ≤ ∫_{Y ≥ t} X` for all `t > 0`, then `E Y² ≤ 4 E X²` (layer cake:
`E Y² = 2 ∫_0^∞ t μ(Y ≥ t) dt ≤ 2 E[X Y] ≤ 2 ‖X‖₂ ‖Y‖₂`). -/
theorem lintegral_sq_le_of_weak_type [SFinite μ] {X Y : Ω → ℝ} (hY0 : 0 ≤ Y)
    (hXm : Measurable X) (hYm : Measurable Y) (hY2 : ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂μ < ∞)
    (h : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤ ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (X ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂μ := by
  set a := ∫⁻ ω, ENNReal.ofReal (X ω) ^ 2 ∂μ with ha
  set b := ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂μ with hb
  -- layer cake
  have hlc : b = ENNReal.ofReal 2 *
      ∫⁻ t in Ioi 0, μ {ω | t ≤ Y ω} * ENNReal.ofReal (t ^ ((2:ℝ) - 1)) := by
    rw [← lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hY0)
      hYm.aemeasurable (by norm_num : (0:ℝ) < 2)]
    refine lintegral_congr fun ω => ?_
    rw [Real.rpow_two, ENNReal.ofReal_pow (hY0 ω)]
  have hstep : ∫⁻ t in Ioi 0, μ {ω | t ≤ Y ω} * ENNReal.ofReal (t ^ ((2:ℝ) - 1)) ≤
      ∫⁻ t in Ioi 0, ∫⁻ ω, {ω | t ≤ Y ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω ∂μ := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [lintegral_indicator (measurableSet_le measurable_const hYm), mul_comm]
    simpa [show (2:ℝ) - 1 = 1 by norm_num] using h t ht
  have hswap : ∫⁻ t in Ioi 0, ∫⁻ ω, {ω | t ≤ Y ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (X ω) * ENNReal.ofReal (Y ω) ∂μ := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun ω => ?_
      have : ∀ t, {ω | t ≤ Y ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω =
          (Iic (Y ω)).indicator (fun _ => ENNReal.ofReal (X ω)) t := by
        intro t; by_cases ht : t ≤ Y ω <;> simp [ht, Set.indicator]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Iic, setLIntegral_const, Measure.restrict_apply
        measurableSet_Iic, Iic_inter_Ioi, Real.volume_Ioc, sub_zero, mul_comm]
    · have hu : (Function.uncurry fun t ω =>
          {ω | t ≤ Y ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω) =
          {p : ℝ × Ω | p.1 ≤ Y p.2}.indicator (fun p => ENNReal.ofReal (X p.2)) := by
        ext p; simp [Set.indicator, Function.uncurry]
      rw [hu]
      exact ((hXm.comp measurable_snd).ennreal_ofReal.indicator
        (measurableSet_le measurable_fst (hYm.comp measurable_snd))).aemeasurable
  have hhold : ∫⁻ ω, ENNReal.ofReal (X ω) * ENNReal.ofReal (Y ω) ∂μ ≤
      a ^ (1 / (2:ℝ)) * b ^ (1 / (2:ℝ)) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      hXm.ennreal_ofReal.aemeasurable hYm.ennreal_ofReal.aemeasurable
    simpa [ha, hb, ENNReal.rpow_two] using this
  have key : b ≤ 2 * (a ^ (1 / (2:ℝ)) * b ^ (1 / (2:ℝ))) := by
    calc b ≤ ENNReal.ofReal 2 *
          ∫⁻ t in Ioi 0, ∫⁻ ω, {ω | t ≤ Y ω}.indicator (fun ω => ENNReal.ofReal (X ω)) ω ∂μ := by
          rw [hlc]; gcongr
      _ ≤ 2 * (a ^ (1 / (2:ℝ)) * b ^ (1 / (2:ℝ))) := by
          rw [hswap, ENNReal.ofReal_ofNat]; gcongr
  -- algebra
  set b' := b ^ (1 / (2:ℝ))
  set a' := a ^ (1 / (2:ℝ))
  have hbb : b = b' ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have haa : a = a' ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rcases eq_or_ne b' 0 with h0 | h0
  · rw [hbb, h0]; simp
  have htop : b' ≠ ⊤ := by
    rw [Ne, ENNReal.rpow_eq_top_iff]; push Not
    exact ⟨fun _ => by norm_num, fun h => absurd hY2 (by rw [h]; simp)⟩
  have hb' : b' ≤ 2 * a' := by
    have : b' * b' ≤ (2 * a') * b' := by
      calc b' * b' = b := by rw [hbb, sq]
        _ ≤ _ := key
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left h0 htop).1 this
  calc b = b' ^ 2 := hbb
    _ ≤ (2 * a') ^ 2 := by gcongr
    _ = 4 * a := by rw [haa, mul_pow]; norm_num

/-- **Subgoal** (Doob's `L²` maximal inequality, discrete time): for a real martingale `M`
with `M_k ∈ L²`, `E (max_{k ≤ n} |M_k|)² ≤ 4 E |M_n|²`. -/
theorem lintegral_sup_sq_le [IsFiniteMeasure μ] {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) (hM2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫⁻ ω, (⨆ k ∈ range (n + 1), ‖M k ω‖ₑ) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ := by
  sorry

end DoobL2

end WeakPathwiseIto
