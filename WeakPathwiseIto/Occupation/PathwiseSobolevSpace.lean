/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Occupation.ApproximatingSequence

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The pathwise Sobolev space `𝓦^2_{ω,π}` (Definition 4.3, eq. (9)): functions
`F ∈ W^{2,1}(ℝ^d)` admitting an approximating sequence satisfying (8). -/
def PathwiseSobolevSpace {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (ω : ℝ → Rd d) : Set (Rd d → ℝ) :=
  {F | MemW 2 1 F ∧ ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H ∧
    Nonempty (ApproximatingSequence π ω F H)}

namespace PathwiseSobolevSpace

variable {T : ℝ} {d : ℕ}

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: the multi-index
`e_i + e_j`): for `i ≤ j` the direction list of `e_i + e_j` is `[e_i, e_j]`. -/
theorem directions_single_add_single {i j : Fin d} (hij : i ≤ j) :
    IsWeakDerivative.directions (Pi.single i 1 + Pi.single j 1 : Fin d → ℕ) =
      [Rd.basisVec i, Rd.basisVec j] := by
  sorry

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: the test derivative):
`D^{e_i + e_j} φ = ∂_i ∂_j φ` for a smooth `φ`. -/
theorem testDeriv_single_add_single {φ : Rd d → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (i j : Fin d) (x : Rd d) :
    IsWeakDerivative.testDeriv (Pi.single i 1 + Pi.single j 1) φ x =
      fderiv ℝ (fun y => fderiv ℝ φ y (Rd.basisVec j)) x (Rd.basisVec i) := by
  have key : ∀ (a b : Rd d) (l : List (Rd d)), l = [a, b] →
      iteratedFDeriv ℝ l.length φ x (fun k => l.get k) = fderiv ℝ (fderiv ℝ φ) x a b := by
    rintro a b l rfl
    exact iteratedFDeriv_two_apply _ _ _
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.of_le (WithTop.coe_le_coe.2 le_top) : ContDiff ℝ 2 φ).fderiv_right (m := 1)
      (by norm_num)).differentiable one_ne_zero x
  have hR : fderiv ℝ (fun y => fderiv ℝ φ y (Rd.basisVec j)) x (Rd.basisVec i) =
      fderiv ℝ (fderiv ℝ φ) x (Rd.basisVec i) (Rd.basisVec j) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [hR]
  rcases le_total i j with h | h
  · exact key _ _ _ (directions_single_add_single h)
  · rw [add_comm]
    rw [IsWeakDerivative.testDeriv, key _ _ _ (directions_single_add_single h)]
    exact hφ.contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: integration by parts
twice): `∫ F ∂_u ∂_v φ = ∫ (∂_v ∂_u F) φ` for `F ∈ C²` and a smooth compactly supported `φ`. -/
theorem integral_mul_fderiv_fderiv {F φ : Rd d → ℝ} (hF : ContDiff ℝ 2 F)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) (u v : Rd d) :
    ∫ x, F x * fderiv ℝ (fun y => fderiv ℝ φ y v) x u =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ F y u) x v * φ x := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (m := 1) (by norm_num)
  have hG : ContDiff ℝ 1 (fun y => fderiv ℝ F y u) := hF1.clm_apply contDiff_const
  have hψ : ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) := hφ1.clm_apply contDiff_const
  have hψc : HasCompactSupport (fun y => fderiv ℝ φ y v) := hφc.fderiv_apply (𝕜 := ℝ) v
  have cF : Continuous F := hF.continuous
  have cG := hG.continuous
  have cG' : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ F y u) x v) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cψ := hψ.continuous
  have cψ' : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x u) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cφ := hφ2.continuous
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F)
    (g := fun y => fderiv ℝ φ y v) (v := u)
    ((cG.mul cψ).integrable_of_hasCompactSupport hψc.mul_left)
    ((cF.mul cψ').integrable_of_hasCompactSupport (hψc.fderiv_apply (𝕜 := ℝ) u).mul_left)
    ((cF.mul cψ).integrable_of_hasCompactSupport hψc.mul_left)
    (fun x _ => (hF.differentiable two_ne_zero) x)
    (fun x _ => (hψ.differentiable one_ne_zero) x)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => fderiv ℝ F y u) (g := φ) (v := v)
    ((cG'.mul cφ).integrable_of_hasCompactSupport hφc.mul_left)
    ((cG.mul cψ).integrable_of_hasCompactSupport hψc.mul_left)
    ((cG.mul cφ).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hG.differentiable one_ne_zero) x)
    (fun x _ => (hφ2.differentiable two_ne_zero) x)
  beta_reduce at h1 h2
  rw [h1, h2, neg_neg]

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: Hessian entries):
`⟨∇²F(x) e_j, e_i⟩ = ∂_j ∂_i F(x)` for `F ∈ C²`. -/
theorem coord_smoothHessian {F : Rd d → ℝ} (hF : ContDiff ℝ 2 F) (i j : Fin d) (x : Rd d) :
    Rd.coord i (smoothHessian F x (Rd.basisVec j)) =
      fderiv ℝ (fun y => fderiv ℝ F y (Rd.basisVec i)) x (Rd.basisVec j) := by
  let L : StrongDual ℝ (Rd d) ≃ₗᵢ[ℝ] Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm
  have hg : gradient F = L ∘ fderiv ℝ F := rfl
  have hH : smoothHessian F x (Rd.basisVec j) = L (fderiv ℝ (fderiv ℝ F) x (Rd.basisVec j)) := by
    unfold smoothHessian
    rw [hg, L.comp_fderiv]
    rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [Rd.coord, hH, fderiv_clm_apply hd (differentiableAt_const _)]
  change ⟪(InnerProductSpace.toDual ℝ (Rd d)).symm _, _⟫ = _
  rw [InnerProductSpace.toDual_symm_apply]
  simp

/-- **Subgoal** (Definition 4.3 proof): the classical Hessian of a `C²` function is a weak
Hessian. -/
theorem isWeakHessian_smoothHessian {F : Rd d → ℝ} (hF : ContDiff ℝ 2 F) :
    IsWeakHessian F (smoothHessian F) := by
  sorry

/-- **Subgoal** (Definition 4.3 proof, the constant approximating sequence `F_m = F`): the
seminorm `‖·‖_{W^0_{ω,π}}` vanishes on `0`. -/
theorem occupationSeminorm_sub_self (π : ℕ → Partition T) (ω : ℝ → Rd d)
    (G : Rd d → (Rd d →L[ℝ] Rd d)) : occupationSeminorm π ω (fun x => G x - G x) = 0 := by
  have h : ∀ n, ∫⁻ x, ‖G x - G x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x) = 0 :=
    fun n => by simp only [sub_self, enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero, zero_mul, lintegral_zero]
  unfold occupationSeminorm
  simp only [h]
  exact limsup_const 0

/-- **Subgoal** (Definition 4.3). Section 4.2: `C^2_b(ℝ^d) ∩ W^{2,1}(ℝ^d) ⊂ 𝓦^2_{ω,π}`. -/
theorem contDiffBounded_subset (π : ℕ → Partition T) (ω : ℝ → Rd d) :
    {F : Rd d → ℝ | ContDiffBounded 2 F ∧ MemW 2 1 F} ⊆ PathwiseSobolevSpace π ω := by
  sorry

end PathwiseSobolevSpace

end WeakPathwiseIto
