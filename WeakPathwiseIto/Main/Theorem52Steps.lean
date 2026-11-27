/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Bessel.Theorem29
public import WeakPathwiseIto.Sobolev.MemW2Plus
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Sobolev.HardyLittlewood
public import Carleson.ToMathlib.RealInterpolation.Minkowski
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.Theorem21Second
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Bessel.WienerLawExists
public import WeakPathwiseIto.Main.Theorem51Steps

/-! # Steps of the proof of Theorem 5.2 (Appendix C)

Appendix C: mollify `F_m := η_m ⋆ F`; the non-Lebesgue points `E₁` of `F` are polar
(Theorem 2.9, [AM71], [Fuk93]); `u_m := ‖∇²F_m - ∇²F‖ → 0` in `L^p` and `W^{s,p}`; the truncated
maximal operator `M_1` is bounded on `L^p` and `W^{s,p}`; `h_m := (M_1 u_m)^p` satisfies the
hypotheses of Lemma B.2; Brownian motion avoids Lebesgue-null sets at the (countably many)
positive partition times; the first partition interval is treated with Lemma B.1; then (10),
Hölder and Lemma A.1 give `‖u_m‖_{W⁰_{B,π}} ≤ C limsup_n ‖h_m‖_{n,1,B}^{1/p}`. Only the first
steps are stubbed here; the path-side steps are stubbed after the plan is approved. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace Convolution

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Appendix C, mollification: a `W^{1,1}` function has a weak gradient, assembled
from its first-order weak derivatives). -/
theorem exists_isWeakGradient {k : ℕ} (hk : 1 ≤ k) {F : Rd d → ℝ} (hF : MemW k 1 F) :
    ∃ G : Rd d → Rd d, IsWeakGradient F G := by
  have h : ∀ i : Fin d, ∃ g : Rd d → ℝ, IsWeakDerivative (Pi.single i 1) F g := by
    intro i
    have hord : IsWeakDerivative.order (Pi.single i 1 : Fin d → ℕ) ≤ k := by
      simpa [IsWeakDerivative.order] using hk
    obtain ⟨g, hg, -⟩ := hF.2 _ hord
    exact ⟨g, hg⟩
  choose g hg using h
  refine ⟨fun x => WithLp.toLp 2 (fun i => g i x), fun i => ?_⟩
  simpa [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right] using hg i

/-- **Subgoal** (Appendix C, mollification: the `(i, j)` entry of the linear map of a matrix `M` is
`M i j`). -/
theorem coord_toEuclideanCLM (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Rd.coord i (Matrix.toEuclideanCLM (𝕜 := ℝ) M (Rd.basisVec j)) = M i j := by
  have hb : (EuclideanSpace.single j 1 : Rd d) = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis j := by
    simp
  simp only [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Matrix.toEuclideanCLM]
  rw [hb]
  erw [Matrix.toLin_self]
  simp [Pi.single_apply]

/-- **Subgoal** (Appendix C, mollification: a `W^{2,1}` function has a weak Hessian, assembled
from its second-order weak derivatives). -/
theorem exists_isWeakHessian {F : Rd d → ℝ} (hF : MemW 2 1 F) :
    ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H := by
  have h : ∀ i j : Fin d, ∃ g : Rd d → ℝ, IsWeakDerivative (Pi.single i 1 + Pi.single j 1) F g := by
    intro i j
    have hord : IsWeakDerivative.order (Pi.single i 1 + Pi.single j 1 : Fin d → ℕ) ≤ 2 := by
      simp [IsWeakDerivative.order, Finset.sum_add_distrib]
    obtain ⟨g, hg, -⟩ := hF.2 _ hord
    exact ⟨g, hg⟩
  choose g hg using h
  refine ⟨fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of fun i j => g i j x), fun i j => ?_⟩
  simp only [coord_toEuclideanCLM, Matrix.of_apply]
  exact hg i j

/-- **Subgoal** (Appendix C, mollification: `|h * ψ| ≤ ‖h‖_1 ‖ψ‖_∞`). -/
theorem abs_convolution_le {h ψ : Rd d → ℝ} (hh : Integrable h) {C : ℝ}
    (hC : ∀ x, |ψ x| ≤ C) (x : Rd d) :
    |∫ y, h y * ψ (x - y)| ≤ (∫ y, |h y|) * C := by
  calc |∫ y, h y * ψ (x - y)| ≤ ∫ y, |h y * ψ (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, |h y| * C := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
          (hh.abs.mul_const C) (Eventually.of_forall fun y => ?_)
        show |h y * ψ (x - y)| ≤ |h y| * C
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
    _ = _ := integral_mul_const _ _

/-- **Subgoal** (Appendix C, mollification: `‖(F ⋆[L] g)(x)‖ ≤ ‖L‖ ‖g‖_∞ ‖F‖_1`). -/
theorem norm_convolution_le_of_bound {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (L : ℝ →L[ℝ] E →L[ℝ] E') {F : Rd d → ℝ}
    (hF : Integrable F) {g : Rd d → E} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (x : Rd d) :
    ‖(F ⋆[L, volume] g) x‖ ≤ ‖L‖ * C * ∫ y, |F y| := by
  rw [convolution_def, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hF.norm.const_mul (‖L‖ * C)).congr
    (ae_of_all _ fun y => by simp [Real.norm_eq_abs])) (ae_of_all _ fun y => ?_)
  calc ‖L (F y) (g (x - y))‖ ≤ ‖L‖ * ‖F y‖ * ‖g (x - y)‖ := L.le_opNorm₂ _ _
    _ ≤ ‖L‖ * ‖F y‖ * C := by gcongr; exact hC _
    _ = ‖L‖ * C * |F y| := by rw [Real.norm_eq_abs]; ring

/-- **Subgoal** (Appendix C, mollification: `F * ψ ∈ C²_b` for `F ∈ W^{2,1}`: its derivatives of
order `≤ 2` are `F * ψ`, `F * Dψ`, `F * D²ψ`, bounded by `‖F‖_1 ‖D^k ψ‖_∞`). -/
theorem contDiffBounded_convolution {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiffBounded 2 (fun x => ∫ y, F y * ψ (x - y)) := by
  set L := ContinuousLinearMap.mul ℝ ℝ
  have hu : (fun x => ∫ y, F y * ψ (x - y)) = F ⋆[L, volume] ψ := rfl
  have hF1 : Integrable F := memLp_one_iff_integrable.1 hF.1
  have hFl : LocallyIntegrable F := hF1.locallyIntegrable
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.2 le_top)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hψ'1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ2.fderiv_right (by norm_num)
  have hψ'c : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv (𝕜 := ℝ)
  have hψ''c : HasCompactSupport (fderiv ℝ (fderiv ℝ ψ)) := hψ'c.fderiv (𝕜 := ℝ)
  set L1 : ℝ →L[ℝ] (Rd d →L[ℝ] ℝ) →L[ℝ] (Rd d →L[ℝ] ℝ) := L.precompR (Rd d)
  have hd1 : fderiv ℝ (F ⋆[L, volume] ψ) = F ⋆[L1, volume] fderiv ℝ ψ :=
    funext fun x => (hψc.hasFDerivAt_convolution_right L hFl hψ1 x).fderiv
  obtain ⟨C0, hC0⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨C1, hC1⟩ := (hψ'1.continuous).bounded_above_of_compact_support hψ'c
  obtain ⟨C2, hC2⟩ := (hψ'1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    hψ''c
  rw [hu]
  refine ⟨hψc.contDiff_convolution_right (n := 2) L hFl hψ2, fun i hi => ?_⟩
  interval_cases i
  · exact ⟨_, fun x => by
      rw [norm_iteratedFDeriv_zero]; exact norm_convolution_le_of_bound L hF1 hC0 x⟩
  · exact ⟨_, fun x => by
      rw [show (1 : ℕ) = 0 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hd1]
      exact norm_convolution_le_of_bound _ hF1 hC1 x⟩
  · exact ⟨_, fun x => by
      rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
        ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hd1,
        (hψ'c.hasFDerivAt_convolution_right L1 hFl hψ'1 x).fderiv]
      exact norm_convolution_le_of_bound _ hF1 hC2 x⟩

/-- **Subgoal** (Appendix C, mollification: `D^0 f = f` weakly). -/
theorem isWeakDerivative_zero {f : Rd d → ℝ} (hf : LocallyIntegrable f) :
    IsWeakDerivative 0 f f := by
  refine ⟨hf, hf, fun φ hφ hφc => ?_⟩
  have hdir : IsWeakDerivative.directions (0 : Fin d → ℕ) = [] := by
    simp [IsWeakDerivative.directions, List.flatMap]
  have key : ∀ (l : List (Rd d)) (x : Rd d), l = [] →
      iteratedFDeriv ℝ l.length φ x (fun k => l.get k) = φ x := by
    rintro l x rfl
    simp
  have ht : ∀ x, IsWeakDerivative.testDeriv 0 φ x = φ x := fun x => key _ x hdir
  simp [ht, IsWeakDerivative.order]

/-- **Subgoal** (Appendix C, mollification: the classical partial derivative of a `C¹` function
is its weak derivative, by integration by parts). -/
theorem isWeakDerivative_single_of_contDiff {f : Rd d → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin d) :
    IsWeakDerivative (Pi.single i 1) f (fun x => fderiv ℝ f x (Rd.basisVec i)) := by
  have hdc : Continuous (fun x => fderiv ℝ f x (Rd.basisVec i)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hf.continuous.locallyIntegrable, hdc.locallyIntegrable, fun φ hφ hφc => ?_⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφd : Continuous (fun x => fderiv ℝ φ x (Rd.basisVec i)) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hord : IsWeakDerivative.order (Pi.single i 1 : Fin d → ℕ) = 1 := by
    simp [IsWeakDerivative.order]
  simp_rw [theorem_2_1_first.testDeriv_single, hord, pow_one, neg_one_mul]
  have hc1 : HasCompactSupport (fun x => f x * fderiv ℝ φ x (Rd.basisVec i)) :=
    (hφc.fderiv_apply (𝕜 := ℝ) _).mul_left
  have hc2 : HasCompactSupport (fun x => fderiv ℝ f x (Rd.basisVec i) * φ x) := hφc.mul_left
  have hc3 : HasCompactSupport (fun x => f x * φ x) := hφc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdc.mul hφ.continuous).integrable_of_hasCompactSupport hc2)
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport hc1)
    ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc3)
    (fun x _ => (hf.differentiable one_ne_zero).differentiableAt)
    (fun x _ => (hφ1.differentiable one_ne_zero).differentiableAt)

/-- **Subgoal** (Appendix C, mollification: the multi-indices of order `≤ 1` are `0` and `e_i`). -/
theorem le_one_cases {α : Fin d → ℕ} (hα : ∑ k, α k ≤ 1) :
    α = 0 ∨ ∃ i, α = Pi.single i 1 := by
  by_cases h : ∀ i, α i = 0
  · exact Or.inl (funext h)
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine Or.inr ⟨i, funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    have := Finset.single_le_sum (f := α) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.single_eq_same]
    omega
  · have hpair : α i + α j ≤ ∑ k, α k := by
      rw [← Finset.sum_pair (f := α) (Ne.symm hj)]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Pi.single_eq_of_ne hj]
    omega

/-- **Subgoal** (Appendix C, mollification: the multi-indices of order `≤ 2` are `0`, `e_i` and
`e_i + e_j`). -/
theorem order_le_two_cases {α : Fin d → ℕ} (hα : IsWeakDerivative.order α ≤ 2) :
    α = 0 ∨ (∃ i, α = Pi.single i 1) ∨ ∃ i j, α = Pi.single i 1 + Pi.single j 1 := by
  unfold IsWeakDerivative.order at hα
  by_cases h : ∀ i, α i = 0
  · exact Or.inl (funext h)
  push Not at h
  obtain ⟨i, hi⟩ := h
  set β : Fin d → ℕ := Function.update α i (α i - 1) with hβ
  have hαβ : α = Pi.single i 1 + β := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hβ]; omega
    · simp [hβ, hj]
  have hsum : ∑ k, β k ≤ 1 := by
    have : ∑ k, α k = 1 + ∑ k, β k := by
      conv_lhs => rw [hαβ]
      simp [Finset.sum_add_distrib]
    omega
  rcases le_one_cases hsum with h0 | ⟨j, hj⟩
  · exact Or.inr (Or.inl ⟨i, by rw [hαβ, h0, add_zero]⟩)
  · exact Or.inr (Or.inr ⟨i, j, by rw [hαβ, hj]⟩)

/-- **Subgoal** (Appendix C, mollification: `∂_v (F * g) = F * ∂_v g` for `g ∈ C¹_c`). -/
theorem fderiv_convolution_apply {F : Rd d → ℝ} (hF : LocallyIntegrable F) {g : Rd d → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Rd d) :
    (fun x => fderiv ℝ (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x v) =
      F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => fderiv ℝ g y v) := by
  funext x
  rw [(hgc.hasFDerivAt_convolution_right _ hF hg x).fderiv, convolution_def, convolution_def,
    ContinuousLinearMap.integral_apply (show Integrable (fun t => (ContinuousLinearMap.precompR (Rd d)
        (ContinuousLinearMap.mul ℝ ℝ)) (F t) (fderiv ℝ g (x - t))) volume from
      (hgc.fderiv (𝕜 := ℝ)).convolutionExists_right
        (ContinuousLinearMap.precompR (Rd d) (ContinuousLinearMap.mul ℝ ℝ)) hF
        (hg.continuous_fderiv one_ne_zero) x)]
  rfl

/-- **Subgoal** (Appendix C, mollification: `F * ψ ∈ W^{2,1}` for `F ∈ W^{2,1}`: its classical, hence
weak, derivatives of order `≤ 2` are `F * D^α ψ`, integrable by Young's inequality). -/
theorem memW_convolution {F : Rd d → ℝ} (hF : MemW 2 1 F)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    MemW 2 1 (fun x => ∫ y, F y * ψ (x - y)) := by
  set L := ContinuousLinearMap.mul ℝ ℝ
  have hu : (fun x => ∫ y, F y * ψ (x - y)) = F ⋆[L, volume] ψ := rfl
  have hu2 : ContDiff ℝ 2 (F ⋆[L, volume] ψ) := (contDiffBounded_convolution hF hψ hψc).1
  rw [hu]
  have hF1 : Integrable F := memLp_one_iff_integrable.1 hF.1
  have hFl : LocallyIntegrable F := hF1.locallyIntegrable
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (WithTop.coe_le_coe.2 le_top)
  have hI : ∀ g : Rd d → ℝ, Continuous g → HasCompactSupport g →
      MemLp (F ⋆[L, volume] g) 1 := fun g hg hgc =>
    memLp_one_iff_integrable.2 (hF1.integrable_convolution L (hg.integrable_of_hasCompactSupport hgc))
  have hψi : ∀ i : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ ψ y (Rd.basisVec i)) :=
    fun i => (hψ.fderiv_right le_rfl).clm_apply contDiff_const
  have hψic : ∀ i : Fin d, HasCompactSupport (fun y => fderiv ℝ ψ y (Rd.basisVec i)) :=
    fun i => hψc.fderiv_apply (𝕜 := ℝ) (Rd.basisVec i)
  refine ⟨hI ψ hψ.continuous hψc, fun α hα => ?_⟩
  rcases order_le_two_cases hα with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact ⟨_, isWeakDerivative_zero ((hI ψ hψ.continuous hψc).locallyIntegrable le_rfl),
      hI ψ hψ.continuous hψc⟩
  · refine ⟨_, isWeakDerivative_single_of_contDiff (hu2.of_le (by norm_num)) i, ?_⟩
    rw [fderiv_convolution_apply hFl hψ1 hψc]
    exact hI _ (hψi i).continuous (hψic i)
  · refine ⟨_, PathwiseSobolevSpace.isWeakHessian_smoothHessian hu2 i j, ?_⟩
    simp_rw [PathwiseSobolevSpace.coord_smoothHessian hu2]
    rw [fderiv_convolution_apply hFl hψ1 hψc,
      fderiv_convolution_apply hFl ((hψi i).of_le (WithTop.coe_le_coe.2 le_top)) (hψic i)]
    exact hI _ (((hψi i).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hψic i).fderiv_apply (𝕜 := ℝ) (Rd.basisVec j))

/-- **Subgoal** (Appendix C, mollification: `F_m ∈ C²_b ∩ W^{2,1}`). -/
theorem mollify_mem {F : Rd d → ℝ} (hF : MemW 2 1 F) {ψ : Rd d → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiffBounded 2 (fun x => ∫ y, F y * ψ (x - y)) ∧
      MemW 2 1 (fun x => ∫ y, F y * ψ (x - y)) := by
  exact ⟨contDiffBounded_convolution hF hψ hψc, memW_convolution hF hψ hψc⟩

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: `|⨍_s f - c| ≤ ⨍_s |f - c|`). -/
theorem abs_setAverage_sub_le {f : Rd d → ℝ} {s : Set (Rd d)} (hf : IntegrableOn f s)
    (hs0 : volume s ≠ 0) (hst : volume s ≠ ∞) (c : ℝ) :
    |(⨍ y in s, f y) - c| ≤ ⨍ y in s, |f y - c| := by
  have hm : 0 < volume.real s := ENNReal.toReal_pos hs0 hst
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
  have h : (volume.real s)⁻¹ * (∫ y in s, f y) - c =
      (volume.real s)⁻¹ * ∫ y in s, (f y - c) := by
    rw [integral_sub hf (integrableOn_const hst), setIntegral_const, smul_eq_mul, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
  rw [h, abs_mul, abs_of_pos (inv_pos.2 hm)]
  gcongr
  exact abs_integral_le_integral_abs

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: at a Lebesgue point with value `c`, `F̃(x) = c`). -/
theorem preciseRepresentative_eq_of_tendsto {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {x : Rd d} {c : ℝ}
    (hc : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, |F y - c|) (𝓝[>] 0) (𝓝 0)) :
    preciseRepresentative F x = c := by
  unfold preciseRepresentative
  apply Tendsto.limsup_eq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hc
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.norm_eq_abs]
  exact abs_setAverage_sub_le ((hF.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
    Metric.ball_subset_closedBall) (Metric.measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne c

/-- **Subgoal** (Appendix C, mollification at Lebesgue points: `|F * ψ(x) - c| ≤ K ∫_{B(x,r)} |F - c|` for a mollifier `0 ≤ ψ ≤ K`, `∫ ψ = 1`, `supp ψ ⊆ B(0,r)`). -/
theorem abs_mollify_sub_le {F : Rd d → ℝ} (hF : LocallyIntegrable F) {ψ : Rd d → ℝ}
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x = 1) {r K : ℝ}
    (hψs : Function.support ψ ⊆ Metric.ball 0 r) (hψb : ∀ x, ψ x ≤ K) (x : Rd d) (c : ℝ) :
    |(∫ y, F y * ψ (x - y)) - c| ≤ K * ∫ y in Metric.ball x r, |F y - c| := by
  have hψi : Integrable ψ := Integrable.of_integral_ne_zero (by rw [hψ1]; norm_num)
  have hψx : Integrable (fun y => ψ (x - y)) := hψi.comp_sub_left x
  have hψx1 : ∫ y, ψ (x - y) = 1 := by rw [integral_sub_left_eq_self]; exact hψ1
  have hK : 0 ≤ K := (hψ0 0).trans (hψb 0)
  have hsupp : ∀ y, y ∉ Metric.ball x r → ψ (x - y) = 0 := fun y hy => by
    by_contra h
    apply hy
    have := hψs h
    rw [mem_ball_zero_iff] at this
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact this
  have hFb : IntegrableOn F (Metric.ball x r) :=
    (hF.integrableOn_isCompact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hG : ∀ c' : ℝ, Integrable ((Metric.ball x r).indicator fun y => |F y - c'|) := fun c' =>
    (show IntegrableOn (fun y => |F y - c'|) (Metric.ball x r) volume from
      (hFb.sub (integrableOn_const (C := c') measure_ball_lt_top.ne (by simp))).abs).integrable_indicator
      measurableSet_ball
  have hpt : ∀ c' y, ‖(F y - c') * ψ (x - y)‖ ≤
      K * (Metric.ball x r).indicator (fun y => |F y - c'|) y := fun c' y => by
    by_cases hy : y ∈ Metric.ball x r
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 _), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hψb _) (abs_nonneg _)
    · rw [indicator_of_notMem hy, hsupp y hy]; simp
  have hFψ : Integrable (fun y => F y * ψ (x - y)) := by
    refine Integrable.mono' ((hG 0).const_mul K)
      (hF.aestronglyMeasurable.mul hψx.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    simpa using hpt 0 y
  have heq : (∫ y, F y * ψ (x - y)) - c = ∫ y, (F y - c) * ψ (x - y) := by
    have : (∫ y, F y * ψ (x - y)) - c = (∫ y, F y * ψ (x - y)) - ∫ y, c * ψ (x - y) := by
      rw [integral_const_mul, hψx1, mul_one]
    rw [this, ← integral_sub hFψ (hψx.const_mul c)]
    simp_rw [sub_mul]
  rw [heq, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((hG c).const_mul K) (ae_of_all _ (hpt c))).trans
    (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator measurableSet_ball]

/-- **Subgoal** (Appendix C, mollification: `F_m(x) → F̃(x)` at every Lebesgue point). -/
theorem tendsto_mollify_of_isLebesguePoint {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)))
    (hψb : ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d) {x : Rd d}
    (hx : IsLebesguePoint F x) :
    Tendsto (fun n => ∫ y, F y * ψ n (x - y)) atTop (𝓝 (preciseRepresentative F x)) := by
  obtain ⟨c, hc⟩ := hx
  rw [preciseRepresentative_eq_of_tendsto hF hc]
  obtain ⟨C, hC⟩ := hψb
  set V : ℝ := volume.real (Metric.ball (0 : Rd d) 1)
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have hlim := (hc.comp hr).const_mul (C * V)
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  have hrn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hvol : volume.real (Metric.ball x (1 / ((n : ℝ) + 1))) =
      (1 / ((n : ℝ) + 1)) ^ d * V := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos _ _ hrn, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hint : ∫ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| =
      volume.real (Metric.ball x (1 / ((n : ℝ) + 1))) *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact (ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hrn).ne' measure_ball_lt_top.ne).ne'
  rw [Real.norm_eq_abs]
  refine (abs_mollify_sub_le hF (hψ0 n) (hψ1 n) (hψs n) (hC n) x c).trans (le_of_eq ?_)
  rw [hint, hvol, Function.comp_apply]
  have h1 : ((n : ℝ) + 1) ^ d * (1 / ((n : ℝ) + 1)) ^ d = 1 := by
    rw [← mul_pow, mul_one_div_cancel (by positivity), one_pow]
  calc C * ((n : ℝ) + 1) ^ d * ((1 / ((n : ℝ) + 1)) ^ d * V *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c|)
      = C * (((n : ℝ) + 1) ^ d * (1 / ((n : ℝ) + 1)) ^ d) * V *
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)), |F y - c| := by ring
    _ = _ := by rw [h1, mul_one]

/-- **Subgoal** (Appendix C, `E₁` is polar: Theorem 2.9, [AM71, Thm. 1], [Fuk93]). -/
theorem isBrownianPolar_nonLebesgue (hT : 0 < T) {p : ℝ} (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2Plus p F) : IsBrownianPolar d T {x | ¬ IsLebesguePoint F x} := by
  obtain ⟨_, _, hFs⟩ := hF
  have h29 := theorem_2_9 d 2 hp hFs.1
  rw [Nat.cast_ofNat] at h29
  exact (IsBrownianPolar.iff_isNull hT _).2 (besselCapacity.IsNull.one_two_of_two_p hp h29)

/-- **Subgoal** (Appendix C, Brownian motion does not enter a polar set at positive times). -/
theorem ae_forall_path_not_mem {E : Set (Rd d)} (hE : IsBrownianPolar d T E) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ Ioc 0 T,
      CanonicalWienerSpace.path ω t ∉ E := by
  refine measure_eq_zero_iff_ae_notMem.1 (hE x₀) |>.mono fun ω hω t ht hmem => hω ?_
  refine ⟨⟨t, ht.1.le, ht.2⟩, ht.1, ?_⟩
  simpa [CanonicalWienerSpace.path, CanonicalWienerSpace.B, ht.1.le, ht.2] using hmem

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 2: translation is continuous in `L^p`
for continuous compactly supported functions). -/
theorem tendsto_eLpNorm_comp_sub_sub_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (_hp : 1 ≤ p) {g : Rd d → E} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun z : Rd d => eLpNorm (fun x => g (x - z) - g x) (ENNReal.ofReal p) volume)
      (𝓝 0) (𝓝 0) := by
  set K : Set (Rd d) := Metric.cthickening 1 (tsupport g)
  have hK : IsCompact K := hgc.cthickening
  set C : ℝ≥0∞ := volume K ^ (ENNReal.ofReal p).toReal⁻¹
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  have huc := hgc.uniformContinuous_of_continuous hg
  -- the bound for small translations
  have hbound : ∀ η > 0, ∀ᶠ z in 𝓝 (0 : Rd d),
      eLpNorm (fun x => g (x - z) - g x) (ENNReal.ofReal p) volume ≤ C * ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc η hη
    filter_upwards [Metric.ball_mem_nhds (0 : Rd d) (lt_min hδ one_pos)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hmeas : AEStronglyMeasurable (fun x => g (x - z) - g x) volume :=
      ((hg.comp (continuous_id.sub continuous_const)).sub hg).aestronglyMeasurable
    have hsupp : Function.support (fun x => g (x - z) - g x) ⊆ K := by
      intro x hx
      by_contra hxK
      have h1 : x ∉ tsupport g := fun h => hxK (Metric.self_subset_cthickening _ h)
      have h2 : x - z ∉ tsupport g := by
        intro h
        refine hxK (Metric.mem_cthickening_of_dist_le x (x - z) 1 _ h ?_)
        rw [dist_eq_norm, sub_sub_cancel]; exact (hz.trans_le (min_le_right _ _)).le
      exact hx (show g (x - z) - g x = 0 by rw [image_eq_zero_of_notMem_tsupport h1,
        image_eq_zero_of_notMem_tsupport h2, sub_zero])
    rw [← eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
    refine (eLpNorm_le_of_ae_bound hmeas.restrict (Eventually.of_forall fun x => ?_)).trans
      (by rw [Measure.restrict_apply_univ])
    rw [← dist_eq_norm]
    refine (hδg ?_).le
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hz.trans_le (min_le_left _ _)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlim : Tendsto (fun η : ℝ => C * ENNReal.ofReal η) (𝓝 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hC)
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), C * ENNReal.ofReal η < ε :=
    nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨η, hηε, hη0⟩ := (hev.and self_mem_nhdsWithin).exists
  filter_upwards [hbound η hη0] with z hz using hz.trans hηε.le

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 2: translation is continuous in `L^p`,
`‖f(· - z) - f‖_p → 0` as `z → 0`, by density of `C_c` in `L^p`). -/
theorem tendsto_eLpNorm_comp_sub_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p)) :
    Tendsto (fun z : Rd d => eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume)
      (𝓝 0) (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨g, hgc, hfg, hgcont, -⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofReal_ne_top hε3
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hfgm : AEStronglyMeasurable (f - g) volume := hfm.sub hgcont.aestronglyMeasurable
  have hgf : eLpNorm (g - f) (ENNReal.ofReal p) volume ≤ ε / 3 := by
    rw [← neg_sub, eLpNorm_neg]; exact hfg
  filter_upwards [(ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_comp_sub_sub_of_hasCompactSupport hp hgcont hgc)) (ε / 3)
      (pos_iff_ne_zero.2 hε3)] with z hz
  have hshift : eLpNorm (fun x => (f - g) (x - z)) (ENNReal.ofReal p) volume =
      eLpNorm (f - g) (ENNReal.ofReal p) volume :=
    eLpNorm_comp_measurePreserving hfgm (measurePreserving_sub_right _ z)
  have hsplit : (fun x => f (x - z) - f x) =
      ((fun x => (f - g) (x - z)) + fun x => g (x - z) - g x) + (g - f) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [hsplit]
  calc _ ≤ eLpNorm ((fun x => (f - g) (x - z)) + fun x => g (x - z) - g x) (ENNReal.ofReal p)
          volume + eLpNorm (g - f) (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
    _ ≤ (eLpNorm (fun x => (f - g) (x - z)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => g (x - z) - g x) (ENNReal.ofReal p) volume) +
          eLpNorm (g - f) (ENNReal.ofReal p) volume := by gcongr; exact eLpNorm_add_le hp1
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by rw [hshift]; gcongr
    _ = ε := ENNReal.add_thirds ε

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 3: `(ψ ⋆ f)(x) - f(x)` as an average
of the translation differences, `∫ ψ(z) (f(x - z) - f(x)) dz`, for `∫ ψ = 1`). -/
theorem mollify_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p)) {ψ : Rd d → ℝ}
    (hψc : Continuous ψ) (hψk : HasCompactSupport ψ) (hψ1 : ∫ x, ψ x = 1) (x : Rd d) :
    (∫ y, ψ (x - y) • f y) - f x = ∫ z, ψ z • (f (x - z) - f x) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (ENNReal.one_le_ofReal.2 hp)
  have hψx : HasCompactSupport fun y => ψ (x - y) :=
    hψk.comp_homeomorph (Homeomorph.subLeft x)
  have hI : Integrable (fun y => ψ (x - y) • f y) :=
    hfl.integrable_smul_left_of_hasCompactSupport (hψc.comp (continuous_sub_left x)) hψx
  have hI' : Integrable (fun z => ψ z • f (x - z)) := by
    have := hI.comp_sub_left x
    simpa only [sub_sub_cancel] using this
  have hψi : Integrable ψ := integrable_of_integral_eq_one hψ1
  have h1 : ∫ y, ψ (x - y) • f y = ∫ z, ψ z • f (x - z) := by
    rw [← integral_sub_left_eq_self (fun y => ψ (x - y) • f y) volume x]
    simp only [sub_sub_cancel]
  have h2 : f x = ∫ z, ψ z • f x := by rw [integral_smul_const, hψ1, one_smul]
  simp_rw [smul_sub]
  rw [integral_sub hI' (hψi.smul_const _), h1, ← h2]

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 3: Minkowski's integral inequality,
`‖ψ ⋆ f - f‖_p ≤ sup_{|z| < r} ‖f(· - z) - f‖_p` for a mollifier `ψ ≥ 0`, `∫ ψ = 1`,
supported in `B(0, r)`). -/
theorem eLpNorm_mollify_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p)) {ψ : Rd d → ℝ}
    (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x = 1) {r : ℝ}
    (hψs : Function.support ψ ⊆ Metric.ball 0 r) :
    eLpNorm (fun x => (∫ y, ψ (x - y) • f y) - f x) (ENNReal.ofReal p) volume ≤
      ⨆ z ∈ Metric.ball (0 : Rd d) r,
        eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hψk : HasCompactSupport ψ :=
    (isCompact_closedBall (0 : Rd d) r).of_isClosed_subset isClosed_closure
      (closure_minimal (hψs.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (ENNReal.one_le_ofReal.2 hp)
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  set S := ⨆ z ∈ Metric.ball (0 : Rd d) r,
    eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume
  -- measurability of the left side: a convolution with a continuous compactly supported kernel
  have hconv : (fun x => ∫ y, ψ (x - y) • f y) =
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    funext x; rw [convolution_lsmul_swap]
  have hLm : AEStronglyMeasurable (fun x => (∫ y, ψ (x - y) • f y) - f x) volume := by
    have hc : Continuous fun x => ∫ y, ψ (x - y) • f y := by
      rw [hconv]; exact hψk.continuous_convolution_left _ hψc hfl
    exact hc.aestronglyMeasurable.sub hfm
  -- the joint integrand
  set Φ : Rd d → Rd d → ℝ≥0∞ := fun x z => ENNReal.ofReal (ψ z) * ‖f (x - z) - f x‖ₑ
  have hΦm : AEMeasurable (Function.uncurry Φ) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : Rd d × Rd d => f (q.1 - q.2)) (volume.prod volume) :=
      hfm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant _ _)
    have h2 : AEStronglyMeasurable (fun q : Rd d × Rd d => f q.1) (volume.prod volume) :=
      hfm.comp_fst
    have h3 : AEMeasurable (fun q : Rd d × Rd d => ENNReal.ofReal (ψ q.2)) (volume.prod volume) :=
      (ENNReal.continuous_ofReal.comp (hψc.comp continuous_snd)).measurable.aemeasurable
    exact h3.mul (h1.sub h2).enorm
  have hpt : ∀ x, ‖(∫ y, ψ (x - y) • f y) - f x‖ₑ ≤ ∫⁻ z, Φ x z := by
    intro x
    rw [mollify_sub_eq hp hf hψc hψk hψ1 x]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    rw [enorm_smul, Real.enorm_of_nonneg (hψ0 z)]
  have hgm : ∀ z, AEStronglyMeasurable (fun x => f (x - z) - f x) volume := fun z =>
    (hfm.comp_measurePreserving (measurePreserving_sub_right _ z)).sub hfm
  have hinner : ∀ z, (∫⁻ x, Φ x z ^ p) ^ p⁻¹ = ENNReal.ofReal (ψ z) *
      eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume := by
    intro z
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top (hgm z), hpr]
    simp_rw [Φ, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp0.le),
      ENNReal.rpow_rpow_inv hp0.ne', one_div]
  have hz : ∀ z, ENNReal.ofReal (ψ z) *
      eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (ψ z) * S := by
    intro z
    by_cases hzb : z ∈ Metric.ball (0 : Rd d) r
    · gcongr; exact le_iSup₂ (f := fun z (_ : z ∈ Metric.ball (0 : Rd d) r) =>
        eLpNorm (fun x => f (x - z) - f x) (ENNReal.ofReal p) volume) z hzb
    · have : ψ z = 0 := Function.notMem_support.1 fun h => hzb (hψs h)
      simp [this]
  have hψl : ∫⁻ z, ENNReal.ofReal (ψ z) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hψ1)
      (Eventually.of_forall hψ0), hψ1, ENNReal.ofReal_one]
  calc eLpNorm (fun x => (∫ y, ψ (x - y) • f y) - f x) (ENNReal.ofReal p) volume
      = (∫⁻ x, ‖(∫ y, ψ (x - y) • f y) - f x‖ₑ ^ p) ^ p⁻¹ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hLm, hpr, one_div]
    _ ≤ (∫⁻ x, (∫⁻ z, Φ x z) ^ p) ^ p⁻¹ := by
        gcongr with x; exact hpt x
    _ ≤ ∫⁻ z, (∫⁻ x, Φ x z ^ p) ^ p⁻¹ := lintegral_lintegral_pow_swap hp hΦm
    _ ≤ ∫⁻ z, ENNReal.ofReal (ψ z) * S := by
        refine lintegral_mono fun z => ?_; rw [hinner]; exact hz z
    _ = S := by
        rw [lintegral_mul_const S (f := fun z => ENNReal.ofReal (ψ z))
          (ENNReal.continuous_ofReal.comp hψc).measurable, hψl, one_mul]

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 3: mollification converges in `L^p`,
`‖ψ_n ⋆ f - f‖_p → 0`). -/
theorem tendsto_eLpNorm_mollify_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p))
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => eLpNorm (fun x => (∫ y, ψ n (x - y) • f y) - f x) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_comp_sub_sub hp hf)) ε hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (eLpNorm_mollify_sub_le hp hf (hψc n) (hψ0 n) (hψ1 n) (hψs n)).trans (iSup₂_le ?_)
  intro z hz
  refine hball z (Metric.ball_subset_ball ?_ hz)
  refine le_trans ?_ hN.le
  gcongr

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 1: a `W^{k,q}` function, `k ≥ 1`, has
a weak gradient, assembled from its first-order weak derivatives). -/
theorem exists_isWeakGradient_of_memW {k : ℕ} (hk : 1 ≤ k) {q : ℝ≥0∞} {F : Rd d → ℝ}
    (hF : MemW k q F) : ∃ G : Rd d → Rd d, IsWeakGradient F G := by
  have h : ∀ i : Fin d, ∃ g : Rd d → ℝ, IsWeakDerivative (Pi.single i 1) F g := by
    intro i
    have hord : IsWeakDerivative.order (Pi.single i 1 : Fin d → ℕ) ≤ k := by
      simpa [IsWeakDerivative.order] using hk
    obtain ⟨g, hg, -⟩ := hF.2 _ hord
    exact ⟨g, hg⟩
  choose g hg using h
  refine ⟨fun x => WithLp.toLp 2 (fun i => g i x), fun i => ?_⟩
  simpa [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right] using hg i

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 1: the Hessian of the mollification is
the mollified weak Hessian, `∇²(F ⋆ ψ) = H ⋆ ψ`). -/
theorem smoothHessian_convolution {F : Rd d → ℝ} {G : Rd d → Rd d}
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hG : IsWeakGradient F G) (hH : IsWeakHessian F H)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (x : Rd d) :
    smoothHessian (fun z => ∫ y, F y * ψ (z - y)) x = ∫ y, ψ (x - y) • H y := by
  obtain ⟨hC2, hder⟩ := theorem_2_1_second.hessian_convolution hG hH hψ hψc
  set u : Rd d → ℝ := fun z => ∫ y, F y * ψ (z - y)
  set M : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j =>
    (EuclideanSpace.proj j : Rd d →L[ℝ] ℝ).smulRight (Rd.basisVec i)
  have hrep : ∀ A : Rd d →L[ℝ] Rd d, A = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) • M i j := by
    intro A
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun k => ?_
    ext l
    simp [M, Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Pi.single_apply]
  have hext : ∀ A B : Rd d →L[ℝ] Rd d,
      (∀ i j, Rd.coord i (A (Rd.basisVec j)) = Rd.coord i (B (Rd.basisVec j))) → A = B := by
    intro A B h
    rw [hrep A, hrep B]
    simp_rw [h]
  have hψx : Continuous fun y => ψ (x - y) := hψ.continuous.comp (continuous_sub_left x)
  have hψxc : HasCompactSupport fun y => ψ (x - y) := hψc.comp_homeomorph (Homeomorph.subLeft x)
  have hent : ∀ i j, Integrable (fun y => ψ (x - y) • Rd.coord i (H y (Rd.basisVec j))) :=
    fun i j => (hH i j).2.1.integrable_smul_left_of_hasCompactSupport hψx hψxc
  have hInt : Integrable (fun y => ψ (x - y) • H y) := by
    have hfun : (fun y => ψ (x - y) • H y) =
        fun y => ∑ i, ∑ j, (ψ (x - y) • Rd.coord i (H y (Rd.basisVec j))) • M i j := by
      funext y
      conv_lhs => rw [hrep (H y)]
      simp only [Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [hfun]
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hent i j).smul_const _
  refine hext _ _ fun i j => ?_
  -- left side: second derivative of the mollification
  have hd1 : Differentiable ℝ (fderiv ℝ u) :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hL : Rd.coord i (smoothHessian u x (Rd.basisVec j)) =
      ∫ y, Rd.coord i (H y (Rd.basisVec j)) * ψ (x - y) := by
    rw [PathwiseSobolevSpace.coord_smoothHessian hC2 i j x]
    rw [fderiv_clm_apply (hd1 x) (differentiableAt_const _)]
    rw [fderiv_const_apply]
    simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact hder x j i
  -- right side: coordinates commute with the Bochner integral
  have hR : Rd.coord i ((∫ y, ψ (x - y) • H y) (Rd.basisVec j)) =
      ∫ y, Rd.coord i (H y (Rd.basisVec j)) * ψ (x - y) := by
    rw [ContinuousLinearMap.integral_apply hInt]
    have hI2 : Integrable (fun y => (ψ (x - y) • H y) (Rd.basisVec j)) :=
      (ContinuousLinearMap.apply ℝ (Rd d) (Rd.basisVec j)).integrable_comp hInt
    have := (innerSL ℝ (Rd.basisVec i)).integral_comp_comm hI2
    simp only [innerSL_apply_apply] at this
    simp only [Rd.coord]
    rw [real_inner_comm, ← this]
    congr 1; funext y
    simp [real_inner_comm, real_inner_smul_right, mul_comm]
  rw [hL, hR]

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 4: the weak Hessian of a `W^{2,p}`
function is in `L^p`, by uniqueness of weak derivatives). -/
theorem memLp_of_isWeakHessian {p : ℝ} {F : Rd d → ℝ} (hF : MemW 2 (ENNReal.ofReal p) F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) : MemLp H (ENNReal.ofReal p) := by
  set M : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j =>
    (EuclideanSpace.proj j : Rd d →L[ℝ] ℝ).smulRight (Rd.basisVec i)
  have hrep : ∀ A : Rd d →L[ℝ] Rd d, A = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) • M i j := by
    intro A
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun k => ?_
    ext l
    simp [M, Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Pi.single_apply]
  have hent : ∀ i j, MemLp (fun z => Rd.coord i (H z (Rd.basisVec j))) (ENNReal.ofReal p) := by
    intro i j
    have hord : IsWeakDerivative.order (Pi.single i 1 + Pi.single j 1 : Fin d → ℕ) ≤ 2 := by
      simp [IsWeakDerivative.order, Finset.sum_add_distrib]
    obtain ⟨g, hg, hgL⟩ := hF.2 _ hord
    exact hgL.ae_eq (theorem_5_1.isWeakDerivative_ae_unique hg (hH i j))
  have hterm : ∀ i j, MemLp (fun z => Rd.coord i (H z (Rd.basisVec j)) • M i j)
      (ENNReal.ofReal p) := by
    intro i j
    have hfun : (fun z => Rd.coord i (H z (Rd.basisVec j)) • M i j) =
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (M i j)) ∘
          fun z => Rd.coord i (H z (Rd.basisVec j)) := by
      funext z; simp only [Function.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply]
    rw [hfun]
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (M i j)).comp_memLp' (hent i j)
  have hrow : ∀ i, MemLp (fun z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • M i j)
      (ENNReal.ofReal p) := fun i =>
    memLp_finsetSum (f := fun j z => Rd.coord i (H z (Rd.basisVec j)) • M i j) Finset.univ
      fun j _ => hterm i j
  have hall : MemLp (fun z => ∑ i, ∑ j, Rd.coord i (H z (Rd.basisVec j)) • M i j)
      (ENNReal.ofReal p) :=
    memLp_finsetSum (f := fun i z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • M i j)
      Finset.univ fun i _ => hrow i
  have hH' : H = fun z => ∑ i, ∑ j, Rd.coord i (H z (Rd.basisVec j)) • M i j :=
    funext fun z => hrep (H z)
  rw [hH']
  exact hall

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: Tonelli in difference coordinates
for a.e.-measurable integrands, `∫∫ Φ(x, y) dy dx = ∫∫ Φ(x, x + h) dx dh`). -/
theorem lintegral_lintegral_eq_add' {Φ : Rd d → Rd d → ℝ≥0∞}
    (hΦ : AEMeasurable (fun q : Rd d × Rd d => Φ q.1 (q.1 + q.2)) (volume.prod volume)) :
    ∫⁻ x, ∫⁻ y, Φ x y = ∫⁻ h, ∫⁻ x, Φ x (x + h) := by
  have h1 : ∀ x, ∫⁻ y, Φ x y = ∫⁻ h, Φ x (x + h) := fun x =>
    (lintegral_add_left_eq_self (fun y => Φ x y) x).symm
  simp_rw [h1]
  exact lintegral_lintegral_swap hΦ

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: for a fixed shift `h`, the
difference `a_n(x + h) - a_n(x)` of `a_n := ψ_n ⋆ f - f` tends to `0` in `L^p`). -/
theorem tendsto_lintegral_shift_mollify_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p))
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) (h : Rd d) :
    Tendsto (fun n => ∫⁻ x, ‖((∫ y, ψ n (x + h - y) • f y) - f (x + h)) -
      ((∫ y, ψ n (x - y) • f y) - f x)‖ₑ ^ p) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  set a : ℕ → Rd d → E := fun n x => (∫ y, ψ n (x - y) • f y) - f x
  set e : ℕ → ℝ≥0∞ := fun n => eLpNorm (a n) (ENNReal.ofReal p) volume
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have ham : ∀ n, AEStronglyMeasurable (a n) volume := by
    intro n
    have hψk : HasCompactSupport (ψ n) :=
      (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
        (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
    have hconv : (fun x => ∫ y, ψ n (x - y) • f y) =
        (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
      funext x; rw [convolution_lsmul_swap]
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • f y := by
      rw [hconv]; exact hψk.continuous_convolution_left _ (hψc n) hfl
    exact hc.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hbound : ∀ n, ∫⁻ x, ‖a n (x + h) - a n x‖ₑ ^ p ≤ (2 * e n) ^ p := by
    intro n
    have hm : AEStronglyMeasurable (fun x => a n (x + h) - a n x) volume :=
      ((ham n).comp_measurePreserving (measurePreserving_add_right volume h)).sub (ham n)
    have hle : eLpNorm (fun x => a n (x + h) - a n x) (ENNReal.ofReal p) volume ≤ 2 * e n := by
      have hsub : (fun x => a n (x + h) - a n x) = (fun x => a n (x + h)) + fun x => -a n x := by
        funext x; simp [sub_eq_add_neg]
      rw [hsub, two_mul]
      refine (eLpNorm_add_le hp1).trans ?_
      have h1 : eLpNorm (fun x => a n (x + h)) (ENNReal.ofReal p) volume = e n :=
        eLpNorm_comp_measurePreserving (ham n) (measurePreserving_add_right volume h)
      rw [h1, show (fun x => -a n x) = -a n from rfl, eLpNorm_neg]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hm, hpr] at hle
    have := ENNReal.rpow_le_rpow hle hp0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at this
  have hlim : Tendsto (fun n => (2 * e n) ^ p) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul
        (tendsto_eLpNorm_mollify_sub hp hf hψc hψ0 hψ1 hψs) (Or.inr (ENNReal.ofNat_ne_top (n := 2)))
      simpa using this
    have := (ENNReal.continuous_rpow_const (y := p)).tendsto 0 |>.comp h2
    rw [ENNReal.zero_rpow_of_pos hp0] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) hbound

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: domination,
`‖a_n(· + h) - a_n‖_p^p ≤ 2^p ‖f(· + h) - f‖_p^p`). -/
theorem lintegral_shift_mollify_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : ℝ} (hp : 1 ≤ p) {f : Rd d → E} (hf : MemLp f (ENNReal.ofReal p))
    {ψ : ℕ → Rd d → ℝ} (hψc : ∀ n, Continuous (ψ n)) (hψ0 : ∀ n x, 0 ≤ ψ n x)
    (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) (n : ℕ) (h : Rd d) :
    ∫⁻ x, ‖((∫ y, ψ n (x + h - y) • f y) - f (x + h)) - ((∫ y, ψ n (x - y) • f y) - f x)‖ₑ ^ p ≤
      2 ^ p * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  set g : Rd d → E := fun x => f (x + h) - f x
  have hfh : MemLp (fun x => f (x + h)) (ENNReal.ofReal p) :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have hg : MemLp g (ENNReal.ofReal p) := hfh.sub hf
  have hgm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  -- the shifted difference is the mollifier defect of `g`
  have hshift : ∀ x, ∫ y, ψ n (x + h - y) • f y = ∫ y, ψ n (x - y) • f (y + h) := by
    intro x
    rw [← integral_add_right_eq_self (fun y => ψ n (x + h - y) • f y) h]
    congr 1; funext y; congr 2; abel
  have hψk : HasCompactSupport (ψ n) :=
    (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
      (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hfhl : LocallyIntegrable (fun x => f (x + h)) volume := hfh.locallyIntegrable hp1
  have hI1 : ∀ x, Integrable (fun y => ψ n (x - y) • f (y + h)) := fun x =>
    hfhl.integrable_smul_left_of_hasCompactSupport ((hψc n).comp (continuous_sub_left x))
      (hψk.comp_homeomorph (Homeomorph.subLeft x))
  have hI2 : ∀ x, Integrable (fun y => ψ n (x - y) • f y) := fun x =>
    hfl.integrable_smul_left_of_hasCompactSupport ((hψc n).comp (continuous_sub_left x))
      (hψk.comp_homeomorph (Homeomorph.subLeft x))
  have hfun : ∀ x, ((∫ y, ψ n (x + h - y) • f y) - f (x + h)) -
      ((∫ y, ψ n (x - y) • f y) - f x) = (∫ y, ψ n (x - y) • g y) - g x := by
    intro x
    rw [hshift x]
    simp only [g, smul_sub]
    rw [integral_sub (hI1 x) (hI2 x)]
    abel
  simp_rw [hfun]
  -- measurability of the mollifier defect of `g`
  have hconv : (fun x => ∫ y, ψ n (x - y) • g y) =
      (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
    funext x; rw [convolution_lsmul_swap]
  have hLm : AEStronglyMeasurable (fun x => (∫ y, ψ n (x - y) • g y) - g x) volume := by
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • g y := by
      rw [hconv]; exact hψk.continuous_convolution_left _ (hψc n) (hg.locallyIntegrable hp1)
    exact hc.aestronglyMeasurable.sub hgm
  have hsup : ⨆ z ∈ Metric.ball (0 : Rd d) (1 / ((n : ℝ) + 1)),
      eLpNorm (fun x => g (x - z) - g x) (ENNReal.ofReal p) volume ≤
        2 * eLpNorm g (ENNReal.ofReal p) volume := by
    refine iSup₂_le fun z _ => ?_
    have hsub : (fun x => g (x - z) - g x) = (fun x => g (x - z)) + fun x => -g x := by
      funext x; simp [sub_eq_add_neg]
    rw [hsub, two_mul]
    refine (eLpNorm_add_le hp1).trans ?_
    have h1 : eLpNorm (fun x => g (x - z)) (ENNReal.ofReal p) volume =
        eLpNorm g (ENNReal.ofReal p) volume :=
      eLpNorm_comp_measurePreserving hgm (measurePreserving_sub_right volume z)
    rw [h1, show (fun x => -g x) = -g from rfl, eLpNorm_neg]
  have hle := (eLpNorm_mollify_sub_le hp hg (hψc n) (hψ0 n) (hψ1 n) (hψs n)).trans hsup
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hLm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hgm, hpr] at hle
  have := ENNReal.rpow_le_rpow hle hp0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne',
    ENNReal.rpow_one] at this
  exact this

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: the weak Hessian is unique a.e.,
entrywise by uniqueness of weak derivatives). -/
theorem ae_eq_of_isWeakHessian {F : Rd d → ℝ} {H H' : Rd d → (Rd d →L[ℝ] Rd d)}
    (hH : IsWeakHessian F H) (hH' : IsWeakHessian F H') : H =ᵐ[volume] H' := by
  set M : Fin d → Fin d → (Rd d →L[ℝ] Rd d) := fun i j =>
    (EuclideanSpace.proj j : Rd d →L[ℝ] ℝ).smulRight (Rd.basisVec i)
  have hrep : ∀ A : Rd d →L[ℝ] Rd d, A = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) • M i j := by
    intro A
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun k => ?_
    ext l
    simp [M, Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Pi.single_apply]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    theorem_5_1.isWeakDerivative_ae_unique (hH i j) (hH' i j)] with x hx
  rw [hrep (H x), hrep (H' x)]
  simp_rw [hx]

/-- **Subgoal** (Appendix C, `tendsto_mollify_hessian`, step 5: the Gagliardo double integral in
difference coordinates, `∫∫ ‖A x - A y‖^p / |x - y|^r = ∫ (∫ ‖A(x + h) - A x‖^p dx) / |h|^r dh`). -/
theorem lintegral_gagliardo_eq_shift {E : Type*} [NormedAddCommGroup E] {A : Rd d → E}
    (hA : AEStronglyMeasurable A volume) (p r : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖A x - A y‖ₑ ^ p / edist x y ^ r =
      ∫⁻ h, (∫⁻ x, ‖A (x + h) - A x‖ₑ ^ p) / ‖h‖ₑ ^ r := by
  have hsh : AEStronglyMeasurable (fun q : Rd d × Rd d => A (q.1 + q.2)) (volume.prod volume) :=
    hA.comp_snd.comp_measurePreserving (measurePreserving_prod_add volume volume)
  have hΦ : AEMeasurable (fun q : Rd d × Rd d =>
      ‖A q.1 - A (q.1 + q.2)‖ₑ ^ p / edist q.1 (q.1 + q.2) ^ r) (volume.prod volume) := by
    refine ((hA.comp_fst.sub hsh).enorm.pow_const p).div ?_
    exact ((continuous_fst.edist (continuous_fst.add continuous_snd)).measurable.pow_const
      r).aemeasurable
  rw [theorem_5_2.lintegral_lintegral_eq_add' (Φ := fun x y => ‖A x - A y‖ₑ ^ p / edist x y ^ r) hΦ]
  refine lintegral_congr fun h => ?_
  have he : ∀ x : Rd d, edist x (x + h) = ‖h‖ₑ := by
    intro x; rw [edist_comm, edist_eq_enorm_sub, add_sub_cancel_left]
  simp_rw [he, div_eq_mul_inv]
  have hm : AEMeasurable (fun x => ‖A (x + h) - A x‖ₑ ^ p) volume :=
    ((hA.comp_measurePreserving (measurePreserving_add_right volume h)).sub hA).enorm.pow_const p
  rw [← lintegral_mul_const'' _ hm]
  refine lintegral_congr fun x => ?_
  rw [enorm_sub_rev]

/-- **Subgoal** (Appendix C, mollification converges in `W^{2+s,p}`: `u_m → 0` in `L^p` and in
the Gagliardo seminorm `[·]_{W^{s,p}}`). -/
theorem tendsto_mollify_hessian {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2PlusS s p F) {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H)
    {ψ : ℕ → Rd d → ℝ} (hψ : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n))
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => eLpNorm (fun x => smoothHessian (fun z => ∫ y, F y * ψ n (z - y)) x - H x)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x, ∫⁻ y,
        ‖‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) x - H x‖ -
          ‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) y - H y‖‖ₑ ^ p /
            edist x y ^ (s * p + d)) atTop (𝓝 0) := by
  have : CompleteSpace (Rd d →L[ℝ] Rd d) := FiniteDimensional.complete ℝ _
  have hp1 : 1 ≤ p := hp.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) < s * p + d := by positivity
  obtain ⟨G, hG⟩ := exists_isWeakGradient_of_memW (k := 2) (by norm_num) hF.1
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).continuous
  have hψk : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (isCompact_closedBall (0 : Rd d) _).of_isClosed_subset isClosed_closure
      (closure_minimal ((hψs n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hsH : ∀ n x, smoothHessian (fun z => ∫ y, F y * ψ n (z - y)) x =
      ∫ y, ψ n (x - y) • H y := fun n x =>
    smoothHessian_convolution hG hH (hψ n) (hψk n) x
  have hHL : MemLp H (ENNReal.ofReal p) := memLp_of_isWeakHessian hF.1 hH
  have hHm : AEStronglyMeasurable H volume := hHL.aestronglyMeasurable
  simp_rw [hsH]
  refine ⟨tendsto_eLpNorm_mollify_sub hp1 hHL hψc hψ0 hψ1 hψs, ?_⟩
  -- the mollifier defect `A n` of `H`
  set A : ℕ → Rd d → (Rd d →L[ℝ] Rd d) := fun n x => (∫ y, ψ n (x - y) • H y) - H x
  have hAm : ∀ n, AEStronglyMeasurable (A n) volume := by
    intro n
    have hconv : (fun x => ∫ y, ψ n (x - y) • H y) =
        (ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) := by
      funext x; rw [convolution_lsmul_swap]
    have hc : Continuous fun x => ∫ y, ψ n (x - y) • H y := by
      rw [hconv]
      exact (hψk n).continuous_convolution_left _ (hψc n)
        (hHL.locallyIntegrable (ENNReal.one_le_ofReal.2 hp1))
    exact hc.aestronglyMeasurable.sub hHm
  set r : ℝ := s * p + d
  -- reverse triangle inequality, then difference coordinates
  have hle : ∀ n, ∫⁻ x, ∫⁻ y, ‖‖A n x‖ - ‖A n y‖‖ₑ ^ p / edist x y ^ r ≤
      ∫⁻ h, (∫⁻ x, ‖A n (x + h) - A n x‖ₑ ^ p) / ‖h‖ₑ ^ r := by
    intro n
    rw [← lintegral_gagliardo_eq_shift (hAm n) p r]
    refine lintegral_mono fun x => lintegral_mono fun y => ?_
    gcongr
    exact enorm_le_iff_norm_le.2 (by simpa [Real.norm_eq_abs] using abs_norm_sub_norm_le _ _)
  -- dominated convergence in the shift `h`
  have hbound_eq : ∫⁻ h, 2 ^ p * (∫⁻ x, ‖H (x + h) - H x‖ₑ ^ p) / ‖h‖ₑ ^ r =
      2 ^ p * ∫⁻ x, ∫⁻ y, ‖H x - H y‖ₑ ^ p / edist x y ^ r := by
    rw [lintegral_gagliardo_eq_shift hHm p r, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofNat_ne_top)]
    simp_rw [mul_div_assoc]
  obtain ⟨H', hH', hfin⟩ := hF.2
  have hae := ae_eq_of_isWeakHessian hH hH'
  have hcongr : ∫⁻ x, ∫⁻ y, ‖H x - H y‖ₑ ^ p / edist x y ^ r =
      ∫⁻ x, ∫⁻ y, ‖H' x - H' y‖ₑ ^ p / edist x y ^ r := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hx, hy]
  have hdom : Tendsto (fun n => ∫⁻ h, (∫⁻ x, ‖A n (x + h) - A n x‖ₑ ^ p) / ‖h‖ₑ ^ r)
      atTop (𝓝 0) := by
    have h0 : (∫⁻ _h : Rd d, (0 : ℝ≥0∞)) = 0 := lintegral_zero
    rw [← h0]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun h => 2 ^ p * (∫⁻ x, ‖H (x + h) - H x‖ₑ ^ p) / ‖h‖ₑ ^ r) (fun n => ?_)
      (fun n => Eventually.of_forall fun h => ?_) ?_ ?_
    · have hj : AEMeasurable (fun q : Rd d × Rd d => ‖A n (q.1 + q.2) - A n q.1‖ₑ ^ p)
          (volume.prod volume) :=
        ((((hAm n).comp_snd.comp_measurePreserving (measurePreserving_prod_add volume volume)).sub
          (hAm n).comp_fst).enorm.pow_const p)
      exact hj.lintegral_prod_left'.div (continuous_enorm.measurable.pow_const r).aemeasurable
    · dsimp only
      exact ENNReal.div_le_div_right (lintegral_shift_mollify_sub_le hp1 hHL hψc hψ0 hψ1 hψs n h) _
    · rw [hbound_eq, hcongr]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofNat_ne_top)
        hfin.ne
    · refine Eventually.of_forall fun h => ?_
      by_cases hh : h = 0
      · subst hh
        simp [hp0]
        exact Or.inl (Or.inl (by rw [enorm_eq_nnnorm]; simp))
      have hb : ‖h‖ₑ ^ r ≠ 0 :=
        (ENNReal.rpow_pos (enorm_pos.2 hh) enorm_ne_top).ne'
      have := ENNReal.Tendsto.div_const
        (tendsto_lintegral_shift_mollify_sub hp1 hHL hψc hψ0 hψ1 hψs h) (Or.inr hb)
      rwa [ENNReal.zero_div] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom
    (fun n => bot_le) hle

/-- **Subgoal** (Appendix C, Hardy–Littlewood: `M_1` is bounded on `L^p`, `p > 1`). -/
theorem eLpNorm_maximal_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    eLpNorm (localMaximalFunction 1 f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  set K : ℝ≥0∞ := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) *
    (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hp0 : (0 : ℝ) < p := by linarith
  have hKp : K ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK
  refine ⟨(K ^ (1 / p)).toNNReal + 1, fun f => ?_⟩
  have hC0 : (((K ^ (1 / p)).toNNReal + 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp
  have hKC : K ^ (1 / p) ≤ (((K ^ (1 / p)).toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hKp]; exact le_self_add
  by_cases hf : AEStronglyMeasurable f volume
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]; exact le_top
  set g := hf.mk f
  have hg : Measurable g := hf.stronglyMeasurable_mk.measurable
  rw [localMaximalFunction.congr_ae hf.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  have hp1 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  simp_rw [enorm_eq_self]
  calc (∫⁻ x, localMaximalFunction 1 g x ^ p) ^ (1 / p)
      ≤ (K * ∫⁻ y, ‖g y‖ₑ ^ p) ^ (1 / p) := by
        gcongr; exact hardyLittlewood.lintegral_rpow_le hg hp
    _ = K ^ (1 / p) * (∫⁻ y, ‖g y‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ _ := by gcongr
  all_goals first
    | exact hg.aestronglyMeasurable
    | exact (localMaximalFunction.measurable g).aestronglyMeasurable

/-- **Subgoal** (Appendix C, `M_1` commutes with translations: `M_1(f(· + h))(x) = M_1 f(x + h)`). -/
theorem localMaximalFunction_comp_add (f : Rd d → ℝ) (h x : Rd d) :
    localMaximalFunction 1 (fun z => f (z + h)) x = localMaximalFunction 1 f (x + h) := by
  unfold localMaximalFunction
  congr 1; funext r; congr 1; funext hr; congr 1; funext _
  have hpre : (· + h) ⁻¹' Metric.ball (x + h) r = Metric.ball x r := by
    rw [Metric.preimage_add_right_ball, add_sub_cancel_right]
  have hint : ∫⁻ z in Metric.ball x r, ‖f (z + h)‖ₑ = ∫⁻ z in Metric.ball (x + h) r, ‖f z‖ₑ := by
    rw [← hpre]
    exact (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight h) (fun z => ‖f z‖ₑ) _
  rw [laverage_eq, laverage_eq, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hint,
    Measure.addHaar_ball_center volume x r, Measure.addHaar_ball_center volume (x + h) r]

/-- **Subgoal** (Appendix C, sublinearity of `M_1` at two points:
`|M_1 f(x) - M_1 f(x + h)| ≤ M_1(f - f(· + h))(x)` where both values are finite). -/
theorem enorm_toReal_sub_le {f : Rd d → ℝ} (hf : Measurable f) {x h : Rd d}
    (hx : localMaximalFunction 1 f x ≠ ⊤) (hxh : localMaximalFunction 1 f (x + h) ≠ ⊤) :
    ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f (x + h)).toReal‖ₑ ≤
      localMaximalFunction 1 (fun z => f z - f (z + h)) x := by
  set a := localMaximalFunction 1 f x
  set b := localMaximalFunction 1 f (x + h)
  set c := localMaximalFunction 1 (fun z => f z - f (z + h)) x
  have hb : localMaximalFunction 1 (fun z => f (z + h)) x = b := localMaximalFunction_comp_add f h x
  have h1 : a ≤ b + c := by
    rw [← hb]
    refine localMaximalFunction.le_add (hf.comp (measurable_add_const h)) (fun z => ?_) x
    calc ‖f z‖ₑ = ‖f (z + h) + (f z - f (z + h))‖ₑ := by ring_nf
      _ ≤ _ := enorm_add_le _ _
  have h2 : b ≤ a + c := by
    rw [← hb]
    refine localMaximalFunction.le_add hf (fun z => ?_) x
    calc ‖f (z + h)‖ₑ = ‖f z - (f z - f (z + h))‖ₑ := by ring_nf
      _ ≤ _ := enorm_sub_le
  rcases eq_or_ne c ⊤ with hc | hc
  · rw [hc]; exact le_top
  have h1' : a.toReal ≤ b.toReal + c.toReal := by
    rw [← ENNReal.toReal_add hxh hc]; exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxh, hc⟩) h1
  have h2' : b.toReal ≤ a.toReal + c.toReal := by
    rw [← ENNReal.toReal_add hx hc]; exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hx, hc⟩) h2
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal hc]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)

/-- **Subgoal** (Appendix C, `M_1 f < ∞` a.e. for `f ∈ L^p`, `p > 1`). -/
theorem ae_localMaximalFunction_ne_top {p : ℝ} (hp : 1 < p) {f : Rd d → ℝ} (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p)) : ∀ᵐ x, localMaximalFunction 1 f x ≠ ⊤ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hI : ∫⁻ y, ‖f y‖ₑ ^ p < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hfp.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  have hK : ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hM : ∫⁻ x, localMaximalFunction 1 f x ^ p ≠ ⊤ :=
    ((hardyLittlewood.lintegral_rpow_le hf hp).trans_lt (ENNReal.mul_lt_top hK.lt_top hI)).ne
  filter_upwards [ae_lt_top ((localMaximalFunction.measurable f).pow_const p) hM]
    with x hx hxt
  rw [hxt, ENNReal.top_rpow_of_pos hp0] at hx
  exact lt_irrefl _ hx

/-- **Subgoal** (Appendix C, Tonelli in difference coordinates:
`∫∫ Φ(x, y) dy dx = ∫∫ Φ(x, x + h) dx dh`). -/
theorem lintegral_lintegral_eq_add {Φ : Rd d → Rd d → ℝ≥0∞}
    (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ x, ∫⁻ y, Φ x y = ∫⁻ h, ∫⁻ x, Φ x (x + h) := by
  have h1 : ∀ x, ∫⁻ y, Φ x y = ∫⁻ h, Φ x (x + h) := fun x =>
    (lintegral_add_left_eq_self (fun y => Φ x y) x).symm
  simp_rw [h1]
  have hm : Measurable (Function.uncurry fun x h : Rd d => Φ x (x + h)) :=
    hΦ.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  exact lintegral_lintegral_swap hm.aemeasurable

/-- **Subgoal** (Appendix C, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}` for measurable `f ∈ L^p`, with
the Hardy–Littlewood constant of `hardyLittlewood.lintegral_rpow_le`). -/
theorem gagliardo_maximal_le_of_measurable {s p : ℝ} (hp : 1 < p) {f : Rd d → ℝ}
    (hf : Measurable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
        edist x y ^ (s * p + d) ≤
      ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
        ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  set K := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  set e : ℝ := s * p + d
  have hM := localMaximalFunction.measurable f
  have hed : Measurable fun z : Rd d × Rd d => edist z.1 z.2 ^ e :=
    (measurable_fst.edist measurable_snd).pow_const e
  have hΦ : Measurable (Function.uncurry fun x y : Rd d =>
      ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
        edist x y ^ e) :=
    ((((hM.comp measurable_fst).ennreal_toReal.sub
      (hM.comp measurable_snd).ennreal_toReal).enorm).pow_const p).div hed
  have hΨ : Measurable (Function.uncurry fun x y : Rd d => ‖f x - f y‖ₑ ^ p / edist x y ^ e) :=
    ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).enorm).pow_const p).div hed
  rw [lintegral_lintegral_eq_add hΦ, lintegral_lintegral_eq_add hΨ, ← lintegral_const_mul' _ _ hK]
  refine lintegral_mono fun h => ?_
  have hedh : ∀ x : Rd d, edist x (x + h) = ‖h‖ₑ := fun x => by
    rw [edist_eq_enorm_sub, sub_add_cancel_left, enorm_neg]
  simp_rw [hedh, div_eq_mul_inv]
  set c := (‖h‖ₑ ^ e)⁻¹
  have hD : Measurable fun z => f z - f (z + h) := hf.sub (hf.comp (measurable_add_const h))
  have hfin := ae_localMaximalFunction_ne_top hp hf hfp
  have hfin' : ∀ᵐ x, localMaximalFunction 1 f (x + h) ≠ ⊤ :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hfin
  calc ∫⁻ x, ‖(localMaximalFunction 1 f x).toReal -
          (localMaximalFunction 1 f (x + h)).toReal‖ₑ ^ p * c
      ≤ ∫⁻ x, localMaximalFunction 1 (fun z => f z - f (z + h)) x ^ p * c := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfin, hfin'] with x hx hxh
        gcongr
        exact enorm_toReal_sub_le hf hx hxh
    _ = (∫⁻ x, localMaximalFunction 1 (fun z => f z - f (z + h)) x ^ p) * c :=
        lintegral_mul_const _ ((localMaximalFunction.measurable _).pow_const p)
    _ ≤ (K * ∫⁻ x, ‖f x - f (x + h)‖ₑ ^ p) * c := by
        gcongr; exact hardyLittlewood.lintegral_rpow_le hD hp
    _ = K * ∫⁻ x, ‖f x - f (x + h)‖ₑ ^ p * c := by
        rw [mul_assoc, lintegral_mul_const _ (hD.enorm.pow_const p)]

/-- **Subgoal** (Appendix C, `M_1` is bounded on `W^{s,p}`: translation invariance and
sublinearity, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}`). -/
theorem gagliardo_maximal_le {s p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    MemLp f (ENNReal.ofReal p) →
      ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
          edist x y ^ (s * p + d) ≤
        C * ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  set K := ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1))
  have hK : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))) ?_
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  refine ⟨K.toNNReal, fun f hfp => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  set g := hfp.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hfp.aestronglyMeasurable.ae_eq_mk
  have hg : Measurable g := hfp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgp : MemLp g (ENNReal.ofReal p) := hfp.ae_eq hfg
  rw [localMaximalFunction.congr_ae hfg]
  have hR : ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) =
      ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) :=
    lintegral_congr_ae (hfg.mono fun x hx => lintegral_congr_ae (hfg.mono fun y hy => by
      simp only [hx, hy]))
  rw [hR]
  exact gagliardo_maximal_le_of_measurable hp hg hgp

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: mean value bound
`|a^p - b^p| ≤ p |a - b| (a^{p-1} + b^{p-1})` for `a, b ≥ 0`, `p ≥ 1`). -/
theorem enorm_rpow_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a ^ p - b ^ p‖ₑ ≤ ENNReal.ofReal p * ‖a - b‖ₑ * (‖a‖ₑ ^ (p - 1) + ‖b‖ₑ ^ (p - 1)) := by
  have key : ∀ {x y : ℝ}, 0 ≤ y → y ≤ x → x ^ p - y ^ p ≤ p * x ^ (p - 1) * (x - y) := by
    intro x y hy hyx
    rcases (hy.trans hyx).eq_or_lt with hx0 | hx0
    · have : y = 0 := le_antisymm (hx0 ▸ hyx) hy
      subst this; rw [← hx0]; simp
    have hB := one_add_mul_self_le_rpow_one_add (s := y / x - 1)
      (by have := div_nonneg hy hx0.le; linarith) hp
    rw [add_sub_cancel, Real.div_rpow hy hx0.le, le_div_iff₀ (by positivity)] at hB
    have hxp : x ^ p = x ^ (p - 1) * x := by rw [Real.rpow_sub_one hx0.ne']; field_simp
    have : (1 + p * (y / x - 1)) * x ^ p = x ^ p + p * x ^ (p - 1) * (y - x) := by
      rw [hxp]; field_simp
    nlinarith
  have hpp : 0 ≤ p - 1 := by linarith
  have hpos : 0 ≤ p := by linarith
  have hR : |a ^ p - b ^ p| ≤ p * |a - b| * (a ^ (p - 1) + b ^ (p - 1)) := by
    have h1 := Real.rpow_nonneg ha (p - 1)
    have h2 := Real.rpow_nonneg hb (p - 1)
    rcases le_total b a with hba | hab
    · have := key hb hba
      have hm : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb hba (by linarith)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hpos (sub_nonneg.2 hba)) h2]
    · have := key ha hab
      have hm : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha hab (by linarith)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hpos (sub_nonneg.2 hab)) h1]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    ENNReal.ofReal_rpow_of_nonneg ha hpp, ENNReal.ofReal_rpow_of_nonneg hb hpp,
    ← ENNReal.ofReal_add (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _),
    ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hR

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the kernel `|x - y|^{-β}`, `β < d`, has
uniformly bounded integrals over a compact set `K`). -/
theorem exists_lintegral_edist_rpow_le {β : ℝ} (hβ : β < d) {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x ∈ K, ∫⁻ y in K, edist x y ^ (-β) ≤ C := by
  obtain ⟨R, hR0, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hdist : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 2 * R := fun x hx y hy => by
    have := dist_triangle x 0 y
    have h1 := Metric.mem_closedBall.1 (hKR hx); have h2 := Metric.mem_closedBall.1 (hKR hy)
    rw [dist_comm 0 y] at this; linarith
  have hKf : volume K ≠ ⊤ := hK.measure_lt_top.ne
  rcases le_or_gt β 0 with hb | hb
  · refine ⟨ENNReal.ofReal (2 * R) ^ (-β) * volume K,
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hKf,
      fun x hx => ?_⟩
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun y hy => ?_
    refine ENNReal.rpow_le_rpow ?_ (by linarith)
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (hdist x hx y hy)
  · have hd : 1 ≤ Module.finrank ℝ (Rd d) := by
      rw [finrank_euclideanSpace_fin]; exact_mod_cast (show (0 : ℝ) < d by linarith)
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Rd d) (lt_of_lt_of_le zero_lt_one hd)
    set r : ℝ := 2 * R + 1
    set G : Rd d → ℝ≥0∞ := fun z => ‖z‖ₑ ^ (-β)
    refine ⟨∫⁻ z in Metric.ball 0 r, G z, ?_, fun x hx => ?_⟩
    · have hI : IntegrableOn (fun z : Rd d => ‖z‖ ^ (-β)) (Metric.ball 0 r) volume :=
        integrableOn_ball_of_norm_le_rpow (C := 1) hd (by rwa [finrank_euclideanSpace_fin])
          (Filter.Eventually.of_forall fun z => by
            rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
          (continuous_norm.measurable.pow_const (-β)).aestronglyMeasurable
      refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr_ae ?_) hI.2)
      have hne : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : Rd d) r)), z ≠ 0 :=
        ae_restrict_of_ae (ae_iff.2 (by simp))
      filter_upwards [hne] with z hz
      rw [Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hz), ofReal_norm]
    · calc ∫⁻ y in K, edist x y ^ (-β)
          ≤ ∫⁻ y, (Metric.ball 0 r).indicator G (x - y) := by
            rw [← lintegral_indicator hK.measurableSet]
            refine lintegral_mono fun y => ?_
            by_cases hy : y ∈ K
            · rw [indicator_of_mem hy, indicator_of_mem, edist_eq_enorm_sub]
              rw [mem_ball_zero_iff, ← dist_eq_norm]; linarith [hdist x hx y hy]
            · rw [indicator_of_notMem hy]; exact bot_le
        _ = ∫⁻ z in Metric.ball 0 r, G z := by
            rw [lintegral_sub_left_eq_self, lintegral_indicator measurableSet_ball]

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: Young's inequality off the diagonal,
`a c^{p-1} / e^d ≤ a^p / e^{sp+d} + c^p / e^{d - sp/(p-1)}`). -/
theorem mul_rpow_div_le_add {s p : ℝ} (hp : 1 < p) {a c e : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ⊤) :
    a * c ^ (p - 1) / e ^ (d : ℝ) ≤
      a ^ p / e ^ (s * p + d) + c ^ p / e ^ ((d : ℝ) - s * p / (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set u : ℝ := (s * p + d) / p
  set v : ℝ := (d : ℝ) - u
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hY := ENNReal.young_inequality (a / e ^ u) (c ^ (p - 1) / e ^ v) hpq
  have hed : e ^ (d : ℝ) = e ^ u * e ^ v := by
    rw [← ENNReal.rpow_add _ _ he0 het]; congr 1; simp [v]
  have hu0 : e ^ u ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 he0) het).ne'
  have hut : e ^ u ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero he0 het
  have hL : a * c ^ (p - 1) / e ^ (d : ℝ) = a / e ^ u * (c ^ (p - 1) / e ^ v) := by
    rw [hed, ENNReal.mul_div_mul_comm (Or.inl hu0) (Or.inl hut)]
  have hA : (a / e ^ u) ^ p = a ^ p / e ^ (s * p + d) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
    congr 2; simp only [u]; field_simp
  have hB : (c ^ (p - 1) / e ^ v) ^ (p / (p - 1)) = c ^ p / e ^ ((d : ℝ) - s * p / (p - 1)) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 2
    · field_simp
    · simp only [v, u]; field_simp; ring
  rw [hL]
  refine hY.trans (add_le_add ?_ ?_)
  · rw [hA]
    exact ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by simp [hp.le]))
  · rw [hB]
    refine ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' ?_)
    rw [ENNReal.one_le_ofReal, one_le_div hp1]; linarith

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the piece with `g(x)^{p-1}` is finite). -/
theorem lintegral_mul_rpow_div_lt_top {s p : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (hp : 1 < p)
    {g : Rd d → ℝ} (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) < ⊤ := by
  have hp1 : 0 < p - 1 := by linarith
  set β : ℝ := (d : ℝ) - s * p / (p - 1)
  have hβ : β < d := by
    have : 0 < s * p / (p - 1) := by positivity
    simp only [β]; linarith
  obtain ⟨C, hCt, hC⟩ := exists_lintegral_edist_rpow_le hβ hK
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Rd d)
    (by rw [finrank_euclideanSpace_fin]; omega)
  set A : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d)
  have hinner : ∀ x, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) ≤
      (∫⁻ y, A x y) + ‖g x‖ₑ ^ p * ∫⁻ y in K, edist x y ^ (-β) := by
    intro x
    calc _ ≤ ∫⁻ y in K, (A x y + ‖g x‖ₑ ^ p * edist x y ^ (-β)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae (ae_iff.2 (by simp) : ∀ᵐ y ∂volume, y ≠ x)] with y hy
          refine (mul_rpow_div_le_add (s := s) hp ((edist_pos.2 hy.symm).ne') (edist_ne_top x y)).trans_eq ?_
          rw [ENNReal.rpow_neg, div_eq_mul_inv _ (edist x y ^ β)]
      _ = (∫⁻ y in K, A x y) + ‖g x‖ₑ ^ p * ∫⁻ y in K, edist x y ^ (-β) := by
          rw [lintegral_add_right _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  have hLp : ∫⁻ x, ‖g x‖ₑ ^ p < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (by simp; linarith) ENNReal.ofReal_ne_top hgp
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  calc _ ≤ ∫⁻ x in K, ((∫⁻ y, A x y) + ‖g x‖ₑ ^ p * C) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact (hinner x).trans (by gcongr; exact hC x hx)
    _ = (∫⁻ x in K, ∫⁻ y, A x y) + (∫⁻ x in K, ‖g x‖ₑ ^ p) * C := by
        rw [lintegral_add_right _ (by fun_prop), lintegral_mul_const _ (by fun_prop)]
    _ ≤ (∫⁻ x, ∫⁻ y, A x y) + (∫⁻ x, ‖g x‖ₑ ^ p) * C := by
        gcongr <;> exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hgs, ENNReal.mul_lt_top hLp hCt.lt_top⟩

/-- **Subgoal** (Appendix C, `lintegral_rpow_sub_le`: the piece with `g(y)^{p-1}` is finite, by
symmetry and Tonelli). -/
theorem lintegral_mul_rpow_div_lt_top' {s p : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (hp : 1 < p)
    {g : Rd d → ℝ} (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x - g y‖ₑ * ‖g y‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ) < ⊤ := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  convert lintegral_mul_rpow_div_lt_top hd hs hp hgm hgp hgs hK using 3 with x
  refine lintegral_congr fun y => ?_
  rw [enorm_sub_rev, edist_comm]

/-- **Subgoal** (Appendix C, second hypothesis of Lemma B.2 for `h = g^p`: Hölder on `K × K`). -/
theorem lintegral_rpow_sub_le {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {g : Rd d → ℝ}
    (hg0 : 0 ≤ g) (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) < ⊤ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h : ∀ x y : Rd 0, ‖g x ^ p - g y ^ p‖ₑ = 0 := fun x y => by
      rw [Subsingleton.elim x y, sub_self, enorm_zero]
    simp [h]
  set f₁ : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ * ‖g x‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ)
  set f₂ : Rd d → Rd d → ℝ≥0∞ := fun x y => ‖g x - g y‖ₑ * ‖g y‖ₑ ^ (p - 1) / edist x y ^ (d : ℝ)
  have hpt : ∀ x y, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) ≤
      ENNReal.ofReal p * (f₁ x y + f₂ x y) := fun x y => by
    calc _ ≤ ENNReal.ofReal p * ‖g x - g y‖ₑ * (‖g x‖ₑ ^ (p - 1) + ‖g y‖ₑ ^ (p - 1)) /
          edist x y ^ (d : ℝ) := by
          gcongr; exact enorm_rpow_sub_rpow_le hp.le (hg0 x) (hg0 y)
      _ = _ := by simp only [f₁, f₂]; rw [← ENNReal.add_div, ← mul_div_assoc, mul_assoc, mul_add]
  have hm₁ : Measurable (Function.uncurry f₁) := by fun_prop
  have hm₂ : Measurable (Function.uncurry f₂) := by fun_prop
  calc _ ≤ ∫⁻ x in K, ∫⁻ y in K, ENNReal.ofReal p * (f₁ x y + f₂ x y) := by
        gcongr with x y; exact hpt x y
    _ = ∫⁻ x in K, ENNReal.ofReal p * ((∫⁻ y in K, f₁ x y) + ∫⁻ y in K, f₂ x y) :=
        lintegral_congr fun x => by
          rw [← lintegral_add_left (by fun_prop : Measurable (f₁ x)),
            ← lintegral_const_mul _ (by fun_prop : Measurable fun y => f₁ x y + f₂ x y)]
    _ = ENNReal.ofReal p * ((∫⁻ x in K, ∫⁻ y in K, f₁ x y) + ∫⁻ x in K, ∫⁻ y in K, f₂ x y) := by
        have h₁ : Measurable fun x => ∫⁻ y in K, f₁ x y := hm₁.lintegral_prod_right'
        have h₂ : Measurable fun x => ∫⁻ y in K, f₂ x y := hm₂.lintegral_prod_right'
        rw [← lintegral_add_left h₁]
        exact lintegral_const_mul _ (h₁.add h₂)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
        ⟨lintegral_mul_rpow_div_lt_top hd hs hp hgm hgp hgs hK,
          lintegral_mul_rpow_div_lt_top' hd hs hp hgm hgp hgs hK⟩)

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null`: a finite product of absolutely
continuous measures on `ℝ` is absolutely continuous with respect to the product). -/
theorem pi_absolutelyContinuous {n : ℕ} {μ ν : Fin n → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero => rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove μ 0).symm
    have hν := (measurePreserving_piFinSuccAbove ν 0).symm
    rw [← hμ.map_eq, ← hν.map_eq]
    exact ((h 0).prod (ih fun j => h _)).map (MeasurableEquiv.measurable _)

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null`: in coordinates, the preimage of a
Lebesgue-null set under `v ↦ x₀ + ∑_i v^i e_i` is Lebesgue-null in `ℝ^{Fin d}`). -/
theorem volume_coords_preimage_null (x₀ : Rd d) {N : Set (Rd d)} (hN : volume N = 0) :
    volume {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N} = 0 := by
  have hsum : ∀ v : Fin d → ℝ, ∑ i, v i • Rd.basisVec i = MeasurableEquiv.toLp 2 (Fin d → ℝ) v := by
    intro v; ext j; simp [Rd.basisVec, Pi.single_apply]
  have hset : {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N} =
      MeasurableEquiv.toLp 2 (Fin d → ℝ) ⁻¹' ((x₀ + ·) ⁻¹' N) := by
    ext v; simp [hsum]
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
    |>.measure_preimage_equiv ((x₀ + ·) ⁻¹' N)
  rw [MeasurableEquiv.symm_symm] at h
  rw [hset, h, measure_preimage_add, hN]

/-- **Subgoal** (Appendix C, `ae_forall_mem_not_mem_null` at one time: for `0 < t ≤ T`,
`ℙ_{x₀}(B(t) ∈ N) = 0` for a Lebesgue-null `N`, since the coordinates of `B(t) - x₀` are
independent `N(0, t)`). -/
theorem measure_path_mem_null (x₀ : Rd d) {N : Set (Rd d)} (hN : volume N = 0) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) :
    CanonicalWienerSpace.P (T := T) x₀ {ω | CanonicalWienerSpace.path ω t ∈ N} = 0 := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x₀
  have htI : t ∈ Icc 0 T := ⟨ht.le, htT⟩
  set N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  refine measure_mono_null (t := {ω | CanonicalWienerSpace.path ω t ∈ N'})
    (fun ω hω => subset_toMeasurable volume N hω) ?_
  set g : Ω' → CanonicalWienerSpace d T := fun ω' =>
    CanonicalWienerSpace.ofCoords x₀ (fun i t => W i t ω') fun i => hW i ω' with hgdef
  have hg : AEMeasurable g Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [hgdef, CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  have hev : Measurable fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩ :=
    (continuous_eval_const (⟨t, htI⟩ : Icc (0 : ℝ) T)).measurable
  have hA : {ω : CanonicalWienerSpace d T | CanonicalWienerSpace.path ω t ∈ N'} =
      (fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩) ⁻¹' N' := by
    ext ω; simp [CanonicalWienerSpace.path, CanonicalWienerSpace.B, htI]
  rw [hA, hP, Measure.map_apply_of_aemeasurable hg (hev (measurableSet_toMeasurable _ _))]
  set V : Ω' → Fin d → ℝ := fun ω' i => W i t.toNNReal ω'
  have hpre : g ⁻¹' ((fun ω : CanonicalWienerSpace d T => ω ⟨t, htI⟩) ⁻¹' N') =
      V ⁻¹' {v | x₀ + ∑ i, v i • Rd.basisVec i ∈ N'} := by
    ext ω'; simp [g, V, CanonicalWienerSpace.ofCoords]
  have hVlaw : ProbabilityTheory.HasLaw V
      (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 t.toNNReal) Q :=
    (hind.comp (fun _ (f : ℝ≥0 → ℝ) => f t.toNNReal) fun _ => measurable_pi_apply _).hasLaw_pi
      fun i => (hB i).toIsPreBrownianReal.hasLaw_eval _
  have hM : MeasurableSet {v : Fin d → ℝ | x₀ + ∑ i, v i • Rd.basisVec i ∈ N'} :=
    (measurableSet_toMeasurable _ _).preimage (by fun_prop)
  rw [hpre, ← Measure.map_apply_of_aemeasurable hVlaw.aemeasurable hM, hVlaw.map_eq]
  have hac : Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 t.toNNReal) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous fun _ =>
      ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (by simpa using ht)
  exact hac (volume_coords_preimage_null x₀ hN')

/-- **Subgoal** (Appendix C, Brownian motion has a density at positive times: it a.s. avoids a
Lebesgue-null set at countably many positive times, e.g. the partition points `t^n_i > 0`). -/
theorem ae_forall_mem_not_mem_null {N : Set (Rd d)} (hN : volume N = 0) {S : Set ℝ}
    (hS : S.Countable) (hpos : ∀ t ∈ S, 0 < t ∧ t ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ S, CanonicalWienerSpace.path ω t ∉ N :=
  (ae_ball_iff hS).2 fun t ht => measure_eq_zero_iff_ae_notMem.1
    (measure_path_mem_null x₀ hN (hpos t ht).1 (hpos t ht).2)

end theorem_5_2

end WeakPathwiseIto
