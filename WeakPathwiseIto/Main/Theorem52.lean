/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Sobolev.MemW2Plus
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay
public import WeakPathwiseIto.Main.Theorem52Steps
public import WeakPathwiseIto.Main.Theorem52PathSteps

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

/-- **Theorem 5.2.** Let `π` satisfy Assumptions 1 and 2 and
`F ∈ W^{2+,p}(ℝ^d) ∩ W^{2,1}(ℝ^d)`, `1 < p < ∞`, with `F` equal to its precise
representative `F̃` at every Lebesgue point (the paper's implicit convention; see
`WeakPathwiseIto.md`, "Theorem 5.2 and Proposition 5.3: representative of F"). Then there is a polar set `E` such that for
every starting point `x₀ ∉ E`, `ℙ_{x₀}(F ∈ 𝓦^2_{B,π}) = 1`. -/
theorem theorem_5_2 {π : ℕ → Partition T} (hT : 0 < T)
    (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {p : ℝ} (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2Plus p F) (hF1 : MemW 2 1 F)
    (hFrep : ∀ x, IsLebesguePoint F x → F x = preciseRepresentative F x) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
      ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), F ∈ PathwiseSobolevSpace π (CanonicalWienerSpace.path ω) := by
  sorry

/-- **Theorem 5.2** (equivalent form): for `x₀ ∉ E` a single deterministic sequence
`F_m ∈ C^2_b ∩ W^{2,1}` works `ℙ_{x₀}`-almost surely. -/
theorem theorem_5_2_deterministic {π : ℕ → Partition T}
    (hT : 0 < T) (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {p : ℝ} (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2Plus p F) (hF1 : MemW 2 1 F)
    (hFrep : ∀ x, IsLebesguePoint F x → F x = preciseRepresentative F x) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
      ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H ∧ ∃ Fm : ℕ → Rd d → ℝ,
        (∀ m, 1 ≤ m → ContDiffBounded 2 (Fm m) ∧ MemW 2 1 (Fm m)) ∧ ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀),
          (∀ t ∈ Icc 0 T, Tendsto (fun m => Fm m (CanonicalWienerSpace.path ω t)) atTop
            (𝓝 (F (CanonicalWienerSpace.path ω t)))) ∧
          Tendsto (fun m => occupationSeminorm π (CanonicalWienerSpace.path ω)
            (fun x => smoothHessian (Fm m) x - H x)) atTop (𝓝 0) := by
  sorry

end WeakPathwiseIto
