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
  sorry

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: integration by parts
twice): `∫ F ∂_u ∂_v φ = ∫ (∂_v ∂_u F) φ` for `F ∈ C²` and a smooth compactly supported `φ`. -/
theorem integral_mul_fderiv_fderiv {F φ : Rd d → ℝ} (hF : ContDiff ℝ 2 F)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) (u v : Rd d) :
    ∫ x, F x * fderiv ℝ (fun y => fderiv ℝ φ y v) x u =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ F y u) x v * φ x := by
  sorry

/-- **Subgoal** (Definition 4.3 proof, `C²` functions have a weak Hessian: Hessian entries):
`⟨∇²F(x) e_j, e_i⟩ = ∂_j ∂_i F(x)` for `F ∈ C²`. -/
theorem coord_smoothHessian {F : Rd d → ℝ} (hF : ContDiff ℝ 2 F) (i j : Fin d) (x : Rd d) :
    Rd.coord i (smoothHessian F x (Rd.basisVec j)) =
      fderiv ℝ (fun y => fderiv ℝ F y (Rd.basisVec i)) x (Rd.basisVec j) := by
  sorry

/-- **Subgoal** (Definition 4.3 proof): the classical Hessian of a `C²` function is a weak
Hessian. -/
theorem isWeakHessian_smoothHessian {F : Rd d → ℝ} (hF : ContDiff ℝ 2 F) :
    IsWeakHessian F (smoothHessian F) := by
  sorry

/-- **Subgoal** (Definition 4.3 proof, the constant approximating sequence `F_m = F`): the
seminorm `‖·‖_{W^0_{ω,π}}` vanishes on `0`. -/
theorem occupationSeminorm_sub_self (π : ℕ → Partition T) (ω : ℝ → Rd d)
    (G : Rd d → (Rd d →L[ℝ] Rd d)) : occupationSeminorm π ω (fun x => G x - G x) = 0 := by
  sorry

/-- **Subgoal** (Definition 4.3). Section 4.2: `C^2_b(ℝ^d) ∩ W^{2,1}(ℝ^d) ⊂ 𝓦^2_{ω,π}`. -/
theorem contDiffBounded_subset (π : ℕ → Partition T) (ω : ℝ → Rd d) :
    {F : Rd d → ℝ | ContDiffBounded 2 F ∧ MemW 2 1 F} ⊆ PathwiseSobolevSpace π ω := by
  sorry

end PathwiseSobolevSpace

end WeakPathwiseIto
