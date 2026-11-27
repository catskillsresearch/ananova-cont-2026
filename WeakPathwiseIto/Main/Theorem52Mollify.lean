/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import Carleson.ToMathlib.RealInterpolation.Minkowski
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.Theorem21Second

/-! # Mollification steps of the proof of Theorem 5.2 (Appendix C)

The purely analytic mollification lemmas of Appendix C (`F_m := η_m ⋆ F` is `C²_b ∩ W^{2,1}`,
`∇²(F ⋆ ψ) = H ⋆ ψ`, translation continuity and `‖ψ_n ⋆ f - f‖_p → 0`), split out of
`Main.Theorem52Steps` unchanged so that they do not depend on the probabilistic steps. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace Convolution

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ}

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

end theorem_5_2

end WeakPathwiseIto
