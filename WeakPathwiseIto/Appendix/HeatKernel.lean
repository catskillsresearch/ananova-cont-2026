/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition
public import WeakPathwiseIto.Appendix.PotentialProfile
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Gaussian heat kernel `p_s(x) := (2πs)^{-d/2} e^{-|x|²/(2s)}` (Appendix B). -/
def heatKernel (d : ℕ) (s : ℝ) (x : Rd d) : ℝ :=
  (2 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * s))

namespace heatKernel

variable {d : ℕ}

/-- **Subgoal** (Lemma B.2 proof, eq. (32), scaling `s = |x|² u`):
`p_{|x|² u}(x) = |x|^{-d} · (2πu)^{-d/2} e^{-1/(2u)}`. -/
theorem scaling (x : Rd d) (hx : x ≠ 0) {u : ℝ} (hu : 0 < u) :
    heatKernel d (‖x‖ ^ 2 * u) x =
      ‖x‖ ^ (-(d : ℝ)) * ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u))) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  unfold heatKernel
  have h1 : 2 * Real.pi * (‖x‖ ^ 2 * u) = ‖x‖ ^ 2 * (2 * Real.pi * u) := by ring
  have h2 : (‖x‖ ^ 2) ^ (-(d : ℝ) / 2) = ‖x‖ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have h3 : -‖x‖ ^ 2 / (2 * (‖x‖ ^ 2 * u)) = -1 / (2 * u) := by
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), h2, h3]
  ring

/-- **Subgoal** (Lemma B.2 proof, eq. (32), unit kernel): for `d ≥ 3`,
`u ↦ (2πu)^{-d/2} e^{-1/(2u)}` is integrable on `(0, ∞)` (substitute `v = 1/u`). -/
theorem integrableOn_unitKernel (hd : 2 < d) :
    IntegrableOn (fun u : ℝ => (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)))
      (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff' _ (p := -1) (by norm_num)]
  have hs : (-1 : ℝ) < (d : ℝ) / 2 - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine IntegrableOn.congr_fun
    ((integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      ((2 * Real.pi) ^ (-(d : ℝ) / 2))) (fun v hv => ?_) measurableSet_Ioi
  have hv : 0 < v := hv
  simp only [smul_eq_mul, Real.rpow_neg_one, Real.rpow_one]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hv.le]
  have hp : (2 * Real.pi * v⁻¹) ^ (-(d : ℝ) / 2) =
      (2 * Real.pi) ^ (-(d : ℝ) / 2) * v ^ ((d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hv.le, neg_div,
      Real.rpow_neg hv.le, inv_inv]
  have he : Real.exp (-1 / (2 * v⁻¹)) = Real.exp (-(1 / 2) * v) := by
    congr 1
    field_simp
  rw [hp, he, Real.rpow_sub hv, Real.rpow_two]
  field_simp

/-- **Subgoal** (Lemma B.2 proof, eq. (32), case `d ≥ 3`):
`∫_0^T p_s(x) ds ≤ C |x|^{2-d}` (scaling `s = |x|² u` on `(0, ∞)`). -/
theorem integral_le_potentialProfile_of_two_lt (hd : 2 < d) (T : ℝ) : ∃ C : ℝ, ∀ x : Rd d,
    x ≠ 0 → ∫ s in Ioc 0 T, heatKernel d s x ≤ C * potentialProfile d ‖x‖ := by
  refine ⟨∫ u in Ioi 0, (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)),
    fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖x‖ ^ 2 := by positivity
  set f : ℝ → ℝ := fun s => heatKernel d s x with hf
  have hscale : EqOn (fun u => f (‖x‖ ^ 2 * u)) (fun u => ‖x‖ ^ (-(d : ℝ)) *
      ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)))) (Ioi 0) :=
    fun u hu => scaling x hx hu
  have hfi : IntegrableOn f (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff f 0 hb).1
      (IntegrableOn.congr_fun ((integrableOn_unitKernel hd).const_mul _) hscale.symm
        measurableSet_Ioi)
    simpa using this
  have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ f s := fun s hs => by
    have hs : (0 : ℝ) < s := hs
    simp only [hf, heatKernel]
    positivity
  have hν : potentialProfile d ‖x‖ = ‖x‖ ^ (2 - (d : ℝ)) := by
    simp [potentialProfile, show d ≠ 1 by omega, show d ≠ 2 by omega]
  calc ∫ s in Ioc 0 T, f s ≤ ∫ s in Ioi 0, f s :=
        setIntegral_mono_set hfi (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
          Ioc_subset_Ioi_self.eventuallyLE
    _ = ‖x‖ ^ 2 * ∫ u in Ioi 0, f (‖x‖ ^ 2 * u) := by
        rw [integral_comp_mul_left_Ioi f 0 hb, mul_zero, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hb.ne', one_mul]
    _ = _ := by
        rw [setIntegral_congr_fun measurableSet_Ioi hscale, integral_const_mul, hν,
          Real.rpow_sub hr, Real.rpow_neg hr.le, Real.rpow_two]
        field_simp

/-- **Subgoal** (Lemma B.2 proof, eq. (32), case `d = 1`): `∫_0^T p_s(x) ds ≤ C`, since
`p_s(x) ≤ (2πs)^{-1/2}` and `s^{-1/2}` is integrable on `(0, T]`. -/
theorem integral_le_potentialProfile_one (T : ℝ) : ∃ C : ℝ, ∀ x : Rd 1,
    x ≠ 0 → ∫ s in Ioc 0 T, heatKernel 1 s x ≤ C * potentialProfile 1 ‖x‖ := by
  rcases le_or_gt T 0 with hT | hT
  · exact ⟨0, fun x _ => by simp [Ioc_eq_empty_of_le hT]⟩
  refine ⟨∫ s in Ioc 0 T, (2 * Real.pi * s) ^ (-(1 : ℝ) / 2), fun x _ => ?_⟩
  have hg : IntegrableOn (fun s : ℝ => (2 * Real.pi * s) ^ (-(1 : ℝ) / 2)) (Ioc 0 T) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1
      (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (by norm_num))
    refine IntegrableOn.congr_fun (hi.const_mul ((2 * Real.pi) ^ (-(1 : ℝ) / 2)))
      (fun s hs => ?_) measurableSet_Ioc
    exact (Real.mul_rpow (by positivity) hs.1.le).symm
  simp only [potentialProfile, ite_true, mul_one]
  refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_) hg
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
  · have : (0 : ℝ) < s := hs.1
    simp only [heatKernel]
    positivity
  · have hs0 : (0 : ℝ) < s := hs.1
    simp only [heatKernel, Nat.cast_one]
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)

/-- **Subgoal** (Lemma B.2 proof, eq. (32), case `d = 2`, pointwise step): since
`e^{-y} ≤ 1/(1+y)`, `p_s(x) ≤ π^{-1} / (2s + |x|²)` for `s > 0`. -/
theorem le_inv_two_mul_add (x : Rd 2) {s : ℝ} (hs : 0 < s) :
    heatKernel 2 s x ≤ 1 / Real.pi / (2 * s + ‖x‖ ^ 2) := by
  unfold heatKernel
  have ha : 0 ≤ ‖x‖ ^ 2 / (2 * s) := by positivity
  rw [show (-((2 : ℕ) : ℝ)) / 2 = -1 by norm_num, Real.rpow_neg_one, neg_div, Real.exp_neg]
  calc (2 * Real.pi * s)⁻¹ * (Real.exp (‖x‖ ^ 2 / (2 * s)))⁻¹
      ≤ (2 * Real.pi * s)⁻¹ * (‖x‖ ^ 2 / (2 * s) + 1)⁻¹ := by
        gcongr
        exact Real.add_one_le_exp _
    _ = 1 / Real.pi / (2 * s + ‖x‖ ^ 2) := by
        field_simp
        ring

/-- **Subgoal** (Lemma B.2 proof, eq. (32), case `d = 2`):
`∫_0^T p_s(x) ds ≤ (2π)^{-1} log(1 + 2T/|x|²) ≤ C (1 + log⁺(1/|x|))`. -/
theorem integral_le_potentialProfile_two (T : ℝ) : ∃ C : ℝ, ∀ x : Rd 2,
    x ≠ 0 → ∫ s in Ioc 0 T, heatKernel 2 s x ≤ C * potentialProfile 2 ‖x‖ := by
  rcases le_or_gt T 0 with hT | hT
  · exact ⟨0, fun x _ => by simp [Ioc_eq_empty_of_le hT]⟩
  refine ⟨1 / (2 * Real.pi) * (Real.log (1 + 2 * T) + 2), fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖x‖ ^ 2 := by positivity
  set g : ℝ → ℝ := fun s => 1 / Real.pi / (2 * s + ‖x‖ ^ 2) with hgdef
  have hgc : ContinuousOn g (Icc 0 T) := continuousOn_const.div (by fun_prop)
    (fun s hs => by have : (0 : ℝ) ≤ s := hs.1; positivity)
  have hg : IntegrableOn g (Ioc 0 T) := (hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h1 : ∫ s in Ioc 0 T, heatKernel 2 s x ≤ ∫ s in Ioc 0 T, g s :=
    integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
      have : (0 : ℝ) < s := hs.1
      simp only [heatKernel]
      positivity) hg
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => le_inv_two_mul_add x hs.1)
  have hF : ∀ s ∈ uIcc 0 T, HasDerivAt (fun s => 1 / (2 * Real.pi) * Real.log (2 * s + ‖x‖ ^ 2))
      (g s) s := by
    intro s hs
    rw [uIcc_of_le hT.le] at hs
    have hpos : 0 < 2 * s + ‖x‖ ^ 2 := by have : (0 : ℝ) ≤ s := hs.1; positivity
    have := (((hasDerivAt_id s).const_mul 2).add_const (‖x‖ ^ 2)).log hpos.ne' |>.const_mul
      (1 / (2 * Real.pi))
    convert this using 1
    · rfl
    · show 1 / Real.pi / (2 * s + ‖x‖ ^ 2) = _
      simp only [id]
      field_simp
  have h2 : ∫ s in Ioc 0 T, g s =
      1 / (2 * Real.pi) * (Real.log (2 * T + ‖x‖ ^ 2) - Real.log (‖x‖ ^ 2)) := by
    rw [← intervalIntegral.integral_of_le hT.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        (hgc.intervalIntegrable_of_Icc hT.le)]
    simp only [mul_zero, zero_add]
    ring
  have hL0 : 0 ≤ Real.log (1 + 2 * T) := Real.log_nonneg (by linarith)
  set m := max 0 (Real.log (1 / ‖x‖)) with hm
  have hm0 : 0 ≤ m := le_max_left _ _
  have hlog : Real.log (2 * T + ‖x‖ ^ 2) - Real.log (‖x‖ ^ 2) ≤ Real.log (1 + 2 * T) + 2 * m := by
    rw [← Real.log_div (by positivity) hb.ne']
    rcases le_or_gt 1 ‖x‖ with h1r | h1r
    · have : (2 * T + ‖x‖ ^ 2) / ‖x‖ ^ 2 ≤ 1 + 2 * T := by
        have : 1 ≤ ‖x‖ ^ 2 := one_le_pow₀ h1r
        rw [div_le_iff₀ hb]; nlinarith
      linarith [Real.log_le_log (by positivity) this]
    · have : (2 * T + ‖x‖ ^ 2) / ‖x‖ ^ 2 ≤ (1 + 2 * T) * (1 / ‖x‖) ^ 2 := by
        rw [div_le_iff₀ hb, one_div, inv_pow, mul_assoc, inv_mul_cancel₀ hb.ne', mul_one]
        nlinarith
      have hl := Real.log_le_log (by positivity) this
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
      have : Real.log (1 / ‖x‖) ≤ m := le_max_right _ _
      push_cast at hl
      linarith
  have hν : potentialProfile 2 ‖x‖ = 1 + m := by simp [potentialProfile, hm]
  rw [hν]
  calc ∫ s in Ioc 0 T, heatKernel 2 s x ≤ _ := h1
    _ = _ := h2
    _ ≤ 1 / (2 * Real.pi) * (Real.log (1 + 2 * T) + 2 * m) := by gcongr
    _ ≤ 1 / (2 * Real.pi) * (Real.log (1 + 2 * T) + 2) * (1 + m) := by
        rw [mul_assoc]
        gcongr
        nlinarith

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (32) [FP00]: `∫_0^T p_s(x) ds ≤ C(R) ν(|x|)` for `|x| ≤ R`. -/
theorem integral_le_potentialProfile (T R : ℝ) : ∃ C : ℝ, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ R →
    ∫ s in Ioc 0 T, heatKernel d s x ≤ C * potentialProfile d ‖x‖ := by
  rcases Nat.lt_or_ge 2 d with hd | hd
  · obtain ⟨C, hC⟩ := integral_le_potentialProfile_of_two_lt hd T
    exact ⟨C, fun x hx _ => hC x hx⟩
  · interval_cases d
    · exact ⟨0, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩
    · obtain ⟨C, hC⟩ := integral_le_potentialProfile_one T
      exact ⟨C, fun x hx _ => hC x hx⟩
    · obtain ⟨C, hC⟩ := integral_le_potentialProfile_two T
      exact ⟨C, fun x hx _ => hC x hx⟩

/-- **Subgoal** (Lemma B.2 proof, eq. (34), scaling `s = |x|² u`):
`p_{|x|² u}(x) / (|x|² u) = |x|^{-d} |x|^{-2} · (2πu)^{-d/2} e^{-1/(2u)} / u`. -/
theorem div_scaling (x : Rd d) (hx : x ≠ 0) {u : ℝ} (hu : 0 < u) :
    heatKernel d (‖x‖ ^ 2 * u) x / (‖x‖ ^ 2 * u) =
      ‖x‖ ^ (-(d : ℝ)) / ‖x‖ ^ 2 *
        ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  unfold heatKernel
  have h1 : 2 * Real.pi * (‖x‖ ^ 2 * u) = ‖x‖ ^ 2 * (2 * Real.pi * u) := by ring
  have h2 : (‖x‖ ^ 2) ^ (-(d : ℝ) / 2) = ‖x‖ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have h3 : -‖x‖ ^ 2 / (2 * (‖x‖ ^ 2 * u)) = -1 / (2 * u) := by
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), h2, h3]
  field_simp

/-- **Subgoal** (Lemma B.2 proof, eq. (34), unit profile): for `d ≥ 1`,
`u ↦ (2πu)^{-d/2} e^{-1/(2u)} / u` is integrable on `(0, ∞)` (substitute `v = 1/u`, Gamma
integral). -/
theorem integrableOn_unitProfile (hd : 0 < d) :
    IntegrableOn (fun u : ℝ => (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u)
      (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff' _ (p := -1) (by norm_num)]
  have hs : (-1 : ℝ) < (d : ℝ) / 2 - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine IntegrableOn.congr_fun
    ((integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      ((2 * Real.pi) ^ (-(d : ℝ) / 2))) (fun v hv => ?_) measurableSet_Ioi
  have hv : 0 < v := hv
  simp only [smul_eq_mul, Real.rpow_neg_one, Real.rpow_one]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hv.le]
  have hp : (2 * Real.pi * v⁻¹) ^ (-(d : ℝ) / 2) =
      (2 * Real.pi) ^ (-(d : ℝ) / 2) * v ^ ((d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hv.le, neg_div,
      Real.rpow_neg hv.le, inv_inv]
  rw [hp, Real.rpow_sub_one hv.ne', Real.rpow_two]
  have he : Real.exp (-1 / (2 * v⁻¹)) = Real.exp (-(1 / 2) * v) := by
    congr 1
    field_simp
  rw [he]
  field_simp

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (34): `∫_0^T p_s(x) / s ds ≤ C |x|^{-d}`. -/
theorem integral_div_le (T : ℝ) : ∃ C : ℝ, ∀ x : Rd d, x ≠ 0 →
    ∫ s in Ioc 0 T, heatKernel d s x / s ≤ C * ‖x‖ ^ (-(d : ℝ)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩
  refine ⟨∫ u in Ioi 0, (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u,
    fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖x‖ ^ 2 := by positivity
  set f : ℝ → ℝ := fun s => heatKernel d s x / s with hf
  have hscale : EqOn (fun u => f (‖x‖ ^ 2 * u)) (fun u => ‖x‖ ^ (-(d : ℝ)) / ‖x‖ ^ 2 *
      ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u)) (Ioi 0) :=
    fun u hu => div_scaling x hx hu
  have hfi : IntegrableOn f (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff f 0 hb).1
      (IntegrableOn.congr_fun ((integrableOn_unitProfile hd).const_mul _) hscale.symm measurableSet_Ioi)
    simpa using this
  have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ f s := fun s hs => by
    have hs : (0 : ℝ) < s := hs
    simp only [hf, heatKernel]
    positivity
  calc ∫ s in Ioc 0 T, f s ≤ ∫ s in Ioi 0, f s :=
        setIntegral_mono_set hfi (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
          Ioc_subset_Ioi_self.eventuallyLE
    _ = ‖x‖ ^ 2 * ∫ u in Ioi 0, f (‖x‖ ^ 2 * u) := by
        rw [integral_comp_mul_left_Ioi f 0 hb, mul_zero, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hb.ne', one_mul]
    _ = _ := by
        rw [setIntegral_congr_fun measurableSet_Ioi hscale, integral_const_mul]
        field_simp

/-- **Subgoal** (Lemma B.2 proof, eq. (35), kernel comparison): for `0 < a ≤ s ≤ K a`,
`p_a(x) ≤ K^{d/2} p_s(x)`. -/
theorem le_rpow_mul (x : Rd d) {a s K : ℝ} (ha : 0 < a) (has : a ≤ s) (hsK : s ≤ K * a) :
    heatKernel d a x ≤ K ^ ((d : ℝ) / 2) * heatKernel d s x := by
  have hs : 0 < s := ha.trans_le has
  have hK : 0 < K := by
    by_contra h
    push Not at h
    nlinarith
  unfold heatKernel
  have e1 : Real.exp (-‖x‖ ^ 2 / (2 * a)) ≤ Real.exp (-‖x‖ ^ 2 / (2 * s)) := by
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have e2 : (2 * Real.pi * a) ^ (-(d : ℝ) / 2) ≤
      K ^ ((d : ℝ) / 2) * (2 * Real.pi * s) ^ (-(d : ℝ) / 2) := by
    have h3 : K ^ ((d : ℝ) / 2) * (2 * Real.pi * s) ^ (-(d : ℝ) / 2) =
        (2 * Real.pi * s / K) ^ (-(d : ℝ) / 2) := by
      have h4 : (K⁻¹) ^ (-(d : ℝ) / 2) = K ^ ((d : ℝ) / 2) := by
        rw [Real.inv_rpow hK.le, neg_div, Real.rpow_neg hK.le, inv_inv]
      rw [div_eq_mul_inv (2 * Real.pi * s) K,
        Real.mul_rpow (x := 2 * Real.pi * s) (by positivity) (by positivity), h4, mul_comm]
    rw [h3]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
    rw [div_le_iff₀ hK]
    nlinarith [Real.pi_pos]
  calc (2 * Real.pi * a) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * a))
      ≤ K ^ ((d : ℝ) / 2) * (2 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * s)) :=
        mul_le_mul e2 e1 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **Subgoal** (Lemma B.2 proof, eq. (35), integrability): for `d ≥ 1` and `x ≠ 0`,
`s ↦ p_s(x)` is integrable on `(0, T]` (dominations from the proof of eq. (32)). -/
theorem integrableOn_Ioc (hd : 0 < d) {x : Rd d} (hx : x ≠ 0) (T : ℝ) :
    IntegrableOn (fun s => heatKernel d s x) (Ioc 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · simp [Ioc_eq_empty_of_le hT]
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hmeas : AEStronglyMeasurable (fun s => heatKernel d s x) (volume.restrict (Ioc 0 T)) :=
    (by unfold heatKernel; fun_prop : Measurable fun s => heatKernel d s x).aestronglyMeasurable
  have hnn : ∀ s ∈ Ioc (0 : ℝ) T, ‖heatKernel d s x‖ = heatKernel d s x := fun s hs => by
    have : (0 : ℝ) < s := hs.1
    exact Real.norm_of_nonneg (by unfold heatKernel; positivity)
  rcases Nat.lt_or_ge 2 d with h3 | h3
  · have hb : 0 < ‖x‖ ^ 2 := by positivity
    have hscale : EqOn (fun u => heatKernel d (‖x‖ ^ 2 * u) x) (fun u => ‖x‖ ^ (-(d : ℝ)) *
        ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)))) (Ioi 0) :=
      fun u hu => scaling x hx hu
    have := (integrableOn_Ioi_comp_mul_left_iff (fun s => heatKernel d s x) 0 hb).1
      (IntegrableOn.congr_fun ((integrableOn_unitKernel h3).const_mul _) hscale.symm
        measurableSet_Ioi)
    rw [mul_zero] at this
    exact this.mono_set Ioc_subset_Ioi_self
  interval_cases d
  · have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1
      (intervalIntegral.intervalIntegrable_rpow' (r := -(1 : ℝ) / 2) (by norm_num))
    have hg : IntegrableOn (fun s : ℝ => (2 * Real.pi * s) ^ (-(1 : ℝ) / 2)) (Ioc 0 T) :=
      IntegrableOn.congr_fun (hi.const_mul ((2 * Real.pi) ^ (-(1 : ℝ) / 2)))
        (fun s hs => (Real.mul_rpow (by positivity) hs.1.le).symm) measurableSet_Ioc
    refine Integrable.mono' hg hmeas (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    rw [hnn s hs]
    have hs0 : (0 : ℝ) < s := hs.1
    simp only [heatKernel, Nat.cast_one]
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)
  · have hgc : ContinuousOn (fun s : ℝ => 1 / Real.pi / (2 * s + ‖x‖ ^ 2)) (Icc 0 T) :=
      continuousOn_const.div (by fun_prop)
        (fun s hs => by have : (0 : ℝ) ≤ s := hs.1; positivity)
    refine Integrable.mono' ((hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self) hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    rw [hnn s hs]
    exact le_inv_two_mul_add x hs.1

/-- **Subgoal** (Lemma B.2 proof, eq. (35), Riemann sum vs integral): if `t_{i+1} ≤ K t_i`
whenever `t_i > 0`, then `∑_i p_{t_i}(x)(t_{i+1} - t_i) ≤ K^{d/2} ∫_0^T p_s(x) ds`. -/
theorem riemannSum_le_integral {T : ℝ} (π : Partition T) (hd : 0 < d) {x : Rd d} (hx : x ≠ 0)
    {K : ℝ} (hK1 : 1 ≤ K) (hK : ∀ i, 0 < π.left i → π.right i ≤ K * π.left i) :
    ∑ i : Fin π.m, heatKernel d (π.left i) x * (π.right i - π.left i) ≤
      K ^ ((d : ℝ) / 2) * ∫ s in Ioc 0 T, heatKernel d s x := by
  have hfi := integrableOn_Ioc hd hx T
  have hnn : ∀ s : ℝ, 0 < s → 0 ≤ heatKernel d s x := fun s hs => by
    unfold heatKernel; positivity
  have hKd : 0 ≤ K ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hl0 : ∀ i, 0 ≤ π.left i := fun i => (π.t_mem _).1
  have hsub : ∀ i, Ioc (π.left i) (π.right i) ⊆ Ioc 0 T := fun i s hs =>
    ⟨(hl0 i).trans_lt hs.1, hs.2.trans (π.t_mem _).2⟩
  have hterm : ∀ i, heatKernel d (π.left i) x * (π.right i - π.left i) ≤
      K ^ ((d : ℝ) / 2) * ∫ s in Ioc (π.left i) (π.right i), heatKernel d s x := by
    intro i
    have hlr := π.left_lt_right i
    by_cases hl : 0 < π.left i
    · have hc : ∫ _ in Ioc (π.left i) (π.right i), heatKernel d (π.left i) x =
          heatKernel d (π.left i) x * (π.right i - π.left i) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
          mul_comm]
      rw [← hc, ← integral_const_mul]
      exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne)) ((hfi.mono_set (hsub i)).const_mul _)
        measurableSet_Ioc fun s hs => le_rpow_mul x hl hs.1.le (hs.2.trans (hK i hl))
    · have h0 : π.left i = 0 := le_antisymm (not_lt.1 hl) (hl0 i)
      have hz : heatKernel d 0 x = 0 := by
        unfold heatKernel
        rw [mul_zero, Real.zero_rpow (by
          have : (0 : ℝ) < d := by exact_mod_cast hd
          intro h; linarith), zero_mul]
      rw [h0, hz, zero_mul]
      exact mul_nonneg hKd (setIntegral_nonneg measurableSet_Ioc fun s hs =>
        hnn s hs.1)
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin π.m => Ioc (π.left i) (π.right i)) := by
    have key : ∀ i j : Fin π.m, i < j → Disjoint (Ioc (π.left i) (π.right i))
        (Ioc (π.left j) (π.right j)) := fun i j hij => by
      refine Set.disjoint_left.2 fun s h1 h2 => ?_
      have : π.right i ≤ π.left j :=
        π.strictMono.monotone (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      linarith [h1.2, h2.1]
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  calc _ ≤ ∑ i : Fin π.m, K ^ ((d : ℝ) / 2) * ∫ s in Ioc (π.left i) (π.right i), heatKernel d s x :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = K ^ ((d : ℝ) / 2) * ∫ s in ⋃ i, Ioc (π.left i) (π.right i), heatKernel d s x := by
        rw [← Finset.mul_sum, integral_iUnion_fintype (fun _ => measurableSet_Ioc) hdisj
          fun i => hfi.mono_set (hsub i)]
    _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left (setIntegral_mono_set hfi (ae_restrict_of_forall_mem
          measurableSet_Ioc fun s hs => hnn s hs.1) (Eventually.of_forall (Set.iUnion_subset hsub)))
          hKd

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (35) [FP00]: under Assumptions 1 and 2,
`∑_i p_{t_i}(x) (t_{i+1} - t_i) ≤ C(R) ν(|x|)` for `|x| ≤ R`. -/
theorem riemannSum_le_potentialProfile {T : ℝ} {π : ℕ → Partition T}
    (h1 : BalancedPartitions π) (_h2 : GeometricMeshDecay π) (R : ℝ) :
    ∃ C : ℝ, ∀ n, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ R →
      ∑ i : Fin (π n).m, heatKernel d ((π n).left i) x * ((π n).right i - (π n).left i) ≤
        C * potentialProfile d ‖x‖ := by
  obtain ⟨M₁, hM₁⟩ := h1
  obtain ⟨C', hC'⟩ := integral_le_potentialProfile (d := d) T R
  set K : ℝ := max (max (1 + M₁) (1 + (π 0).mesh / (π 0).minGap)) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨K ^ ((d : ℝ) / 2) * C', fun n x hx hxR => ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact (hx (Subsingleton.elim _ _)).elim
  have hratio : 1 + (π n).mesh / (π n).minGap ≤ K := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · have := hM₁ n hn
      exact (by linarith : 1 + (π n).mesh / (π n).minGap ≤ 1 + M₁).trans
        ((le_max_left _ _).trans (le_max_left _ _))
  have hK : ∀ i, 0 < (π n).left i → (π n).right i ≤ K * (π n).left i := fun i hi =>
    ((π n).right_le_mul_left i hi).trans (mul_le_mul_of_nonneg_right hratio hi.le)
  calc _ ≤ K ^ ((d : ℝ) / 2) * ∫ s in Ioc 0 T, heatKernel d s x :=
        riemannSum_le_integral (π n) hd hx hK1 hK
    _ ≤ K ^ ((d : ℝ) / 2) * (C' * potentialProfile d ‖x‖) :=
        mul_le_mul_of_nonneg_left (hC' x hx hxR) (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

end heatKernel

end WeakPathwiseIto
