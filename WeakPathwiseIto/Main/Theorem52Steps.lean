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
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.Theorem21Second
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace

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
  sorry

/-- **Subgoal** (Appendix C, mollification: `F_m(x) → F̃(x)` at every Lebesgue point). -/
theorem tendsto_mollify_of_isLebesguePoint {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)))
    (hψb : ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d) {x : Rd d}
    (hx : IsLebesguePoint F x) :
    Tendsto (fun n => ∫ y, F y * ψ n (x - y)) atTop (𝓝 (preciseRepresentative F x)) := by
  sorry

/-- **Subgoal** (Appendix C, `E₁` is polar: Theorem 2.9, [AM71, Thm. 1], [Fuk93]). -/
theorem isBrownianPolar_nonLebesgue (hT : 0 < T) {p : ℝ} (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2Plus p F) : IsBrownianPolar d T {x | ¬ IsLebesguePoint F x} := by
  sorry

/-- **Subgoal** (Appendix C, Brownian motion does not enter a polar set at positive times). -/
theorem ae_forall_path_not_mem {E : Set (Rd d)} (hE : IsBrownianPolar d T E) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ Ioc 0 T,
      CanonicalWienerSpace.path ω t ∉ E := by
  sorry

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
  sorry

/-- **Subgoal** (Appendix C, Hardy–Littlewood: `M_1` is bounded on `L^p`, `p > 1`). -/
theorem eLpNorm_maximal_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    eLpNorm (localMaximalFunction 1 f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

/-- **Subgoal** (Appendix C, `M_1` is bounded on `W^{s,p}`: translation invariance and
sublinearity, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}`). -/
theorem gagliardo_maximal_le {s p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    MemLp f (ENNReal.ofReal p) →
      ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
          edist x y ^ (s * p + d) ≤
        C * ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  sorry

/-- **Subgoal** (Appendix C, second hypothesis of Lemma B.2 for `h = g^p`: Hölder on `K × K`). -/
theorem lintegral_rpow_sub_le {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {g : Rd d → ℝ}
    (hg0 : 0 ≤ g) (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) < ⊤ := by
  sorry

/-- **Subgoal** (Appendix C, Brownian motion has a density at positive times: it a.s. avoids a
Lebesgue-null set at countably many positive times, e.g. the partition points `t^n_i > 0`). -/
theorem ae_forall_mem_not_mem_null {N : Set (Rd d)} (hN : volume N = 0) {S : Set ℝ}
    (hS : S.Countable) (hpos : ∀ t ∈ S, 0 < t ∧ t ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ S, CanonicalWienerSpace.path ω t ∉ N := by
  sorry

end theorem_5_2

end WeakPathwiseIto
