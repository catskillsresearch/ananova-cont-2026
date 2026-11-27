/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakGradient
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Sobolev.Theorem23Steps

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.3** (first estimate). For `f ∈ W^{1,1}(ℝ^d)` and `f̃(x), f̃(y)` finite,
`|f̃(y) - f̃(x)| ≤ C_d (M_{|x-y|}|∇f|(x) + M_{|x-y|}|∇f|(y)) |x - y|`. -/
theorem theorem_2_3_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G → ∀ x y : Rd d,
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x| ≤
        C * (localMaximalFunction (edist x y) G x + localMaximalFunction (edist x y) G y) *
          edist x y := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun f G _ _ x y _ _ => ?_⟩
    rw [Subsingleton.elim x y, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  obtain ⟨C1, hC1⟩ := theorem_2_1_first d
  obtain ⟨Ck, hCk⟩ := theorem_2_3.lintegral_kernel_le_maximal (d := d) (F := Rd d) (α := 1) one_pos
  refine ⟨C1 * Ck + 1, fun f G hf hG x y hfx hfy => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  set R := edist x y with hRdef
  have hR : 0 < R := edist_pos.2 hxy
  have hc0 : ((C1 * Ck + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]; exact (add_pos_of_nonneg_of_pos zero_le one_pos).ne'
  by_cases htop : localMaximalFunction R G x = ⊤ ∨ localMaximalFunction R G y = ⊤
  · have hsum : localMaximalFunction R G x + localMaximalFunction R G y = ⊤ :=
      ENNReal.add_eq_top.2 htop
    rw [hsum, ENNReal.mul_top hc0, ENNReal.top_mul hR.ne']
    exact le_top
  push Not at htop
  obtain ⟨hMx, hMy⟩ := htop
  have hLx := theorem_2_3.isLebesguePoint_of_maximal_lt_top hd hf hG hR (lt_top_iff_ne_top.2 hMx)
  have hLy := theorem_2_3.isLebesguePoint_of_maximal_lt_top hd hf hG hR (lt_top_iff_ne_top.2 hMy)
  obtain ⟨hQ, hxQ, hyQ, hdiam⟩ := theorem_2_3.closedBall_midpoint hxy
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) :=
    theorem_2_1_first.coord_integrable hf hG
  have hexp : ∀ w : Rd d, w = ∑ i, Rd.coord i w • Rd.basisVec i := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGint : Integrable G := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext fun z => hexp (G z)
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hGi i).smul_const _
  have h := hC1 f G hf hG _ hQ x y hxQ hyQ hfx hfy hLx hLy
  have hkx := hCk _ G hQ hGint x hxQ R hdiam
  have hky := hCk _ G hQ hGint y hyQ R hdiam
  rw [ENNReal.rpow_one] at hkx hky
  calc ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x|
      ≤ C1 * ((∫⁻ z in Metric.closedBall (midpoint ℝ x y) (dist x y / 2),
            ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1)) +
          ∫⁻ z in Metric.closedBall (midpoint ℝ x y) (dist x y / 2),
            ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1)) := h
    _ ≤ C1 * (Ck * R * localMaximalFunction R G x + Ck * R * localMaximalFunction R G y) :=
        mul_le_mul' le_rfl (add_le_add hkx hky)
    _ = ((C1 * Ck : ℝ≥0) : ℝ≥0∞) * (localMaximalFunction R G x + localMaximalFunction R G y) * R := by
        push_cast; ring
    _ ≤ ((C1 * Ck + 1 : ℝ≥0) : ℝ≥0∞) * (localMaximalFunction R G x + localMaximalFunction R G y) * R :=
        mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.2 le_self_add) le_rfl) le_rfl

/-- **Theorem 2.3** (second estimate). For `f ∈ W^{2,1}(ℝ^d)` and `f̃(x), f̃(y), ∇̃f(x)` finite,
`|f̃(y) - f̃(x) - ∇̃f(x)(y - x)| ≤ C_d (M_{|x-y|}|∇²f|(x) + M_{|x-y|}|∇²f|(y)) |x - y|²`. -/
theorem theorem_2_3_second (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)),
    MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H → ∀ x y : Rd d,
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      preciseRepresentative.VecIsFinite G x →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x -
          ⟪preciseRepresentative.vec G x, y - x⟫| ≤
        C * (localMaximalFunction (edist x y) H x + localMaximalFunction (edist x y) H y) *
          edist x y ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun f G H _ _ _ x y _ _ _ => ?_⟩
    rw [Subsingleton.elim x y, sub_self, sub_self, inner_zero_right, sub_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  obtain ⟨C2, hC2⟩ := theorem_2_1_second d
  obtain ⟨Ck2, hCk2⟩ := theorem_2_3.lintegral_kernel_le_maximal (d := d)
    (F := Rd d →L[ℝ] Rd d) (α := 2) two_pos
  obtain ⟨Ck1, hCk1⟩ := theorem_2_3.lintegral_kernel_le_maximal (d := d)
    (F := Rd d →L[ℝ] Rd d) (α := 1) one_pos
  refine ⟨C2 * (Ck2 + Ck1) + 1, fun f G H hf hG hH x y hfx hfy hGx => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, sub_self, inner_zero_right, sub_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  set R := edist x y with hRdef
  have hR : 0 < R := edist_pos.2 hxy
  have hc0 : ((C2 * (Ck2 + Ck1) + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]; exact (add_pos_of_nonneg_of_pos zero_le one_pos).ne'
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero _ hR.ne'
  by_cases htop : localMaximalFunction R H x = ⊤ ∨ localMaximalFunction R H y = ⊤
  · have hsum : localMaximalFunction R H x + localMaximalFunction R H y = ⊤ :=
      ENNReal.add_eq_top.2 htop
    rw [hsum, ENNReal.mul_top hc0, ENNReal.top_mul hR2]
    exact le_top
  push Not at htop
  obtain ⟨hMx, hMy⟩ := htop
  have hf1 : MemW 1 1 f := ⟨hf.1, fun α h => hf.2 α (h.trans (by norm_num))⟩
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) :=
    theorem_2_1_first.coord_integrable hf1 hG
  have hLG : ∀ z, localMaximalFunction R H z ≠ ⊤ → ∀ i,
      IsLebesguePoint (fun w => Rd.coord i (G w)) z := fun z hz i =>
    theorem_2_3.isLebesguePoint_of_maximal_lt_top hd
      (theorem_2_1_second.memW_coord hf hG hH i)
      (theorem_2_1_second.isWeakGradient_coord hG hH i) hR
      (lt_of_le_of_lt (theorem_2_3.maximal_coord_hessian_le i R z) (lt_top_iff_ne_top.2 hz))
  have hLf : ∀ z, localMaximalFunction R H z ≠ ⊤ → IsLebesguePoint f z := by
    intro z hz
    obtain ⟨R', hR', hM'⟩ := theorem_2_3.maximal_lt_top_of_isLebesguePoint
      (fun i => (hGi i).locallyIntegrable) (hLG z hz)
    exact theorem_2_3.isLebesguePoint_of_maximal_lt_top hd hf1 hG hR' hM'
  obtain ⟨hQ, hxQ, hyQ, hdiam⟩ := theorem_2_3.closedBall_midpoint hxy
  have hHint : Integrable H := theorem_2_1_second.integrable_hessian hf hH
  have h := hC2 f G H hf hG hH _ hQ x y hxQ hyQ hfx hfy hGx (hLf x hMx) (hLf y hMy) (hLG x hMx)
  have hkx2 := hCk2 _ H hQ hHint x hxQ R hdiam
  have hky2 := hCk2 _ H hQ hHint y hyQ R hdiam
  have hkx1 := hCk1 _ H hQ hHint x hxQ R hdiam
  rw [ENNReal.rpow_two] at hkx2 hky2
  rw [ENNReal.rpow_one] at hkx1
  set Mx := localMaximalFunction R H x
  set My := localMaximalFunction R H y
  refine h.trans ?_
  calc (C2 : ℝ≥0∞) * ((∫⁻ z in Metric.closedBall (midpoint ℝ x y) (dist x y / 2),
            ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2)) +
          (∫⁻ z in Metric.closedBall (midpoint ℝ x y) (dist x y / 2),
            ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2)) +
          Metric.ediam (Metric.closedBall (midpoint ℝ x y) (dist x y / 2)) *
            ∫⁻ z in Metric.closedBall (midpoint ℝ x y) (dist x y / 2),
              ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 1))
      ≤ C2 * (Ck2 * R ^ 2 * Mx + Ck2 * R ^ 2 * My + R * (Ck1 * R * Mx)) :=
        mul_le_mul' le_rfl (add_le_add (add_le_add hkx2 hky2) (mul_le_mul' hdiam hkx1))
    _ = C2 * (Ck2 * R ^ 2 * Mx + Ck2 * R ^ 2 * My + Ck1 * R ^ 2 * Mx) := by ring
    _ ≤ C2 * (Ck2 * R ^ 2 * Mx + Ck2 * R ^ 2 * My + Ck1 * R ^ 2 * (Mx + My)) :=
        mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add))
    _ = ((C2 * (Ck2 + Ck1) : ℝ≥0) : ℝ≥0∞) * (Mx + My) * R ^ 2 := by push_cast; ring
    _ ≤ ((C2 * (Ck2 + Ck1) + 1 : ℝ≥0) : ℝ≥0∞) * (Mx + My) * R ^ 2 :=
        mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.2 le_self_add) le_rfl) le_rfl

end WeakPathwiseIto
