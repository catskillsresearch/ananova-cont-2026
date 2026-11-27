/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Main.Theorem52
public import WeakPathwiseIto.Main.IsItoIntegral
public import WeakPathwiseIto.Main.WeakPathwiseIntegral
public import WeakPathwiseIto.Main.WeakCovariation
public import WeakPathwiseIto.Sobolev.MemWLoc
public import WeakPathwiseIto.Sobolev.IsWeakGradient

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

/-- **Proposition 5.3** (pathwise Föllmer–Protter formula). Let `π` satisfy Assumptions 1 and 2
and `F ∈ W^{2+,p} ∩ W^{2,1} ∩ W^{1,2}_loc`, `1 < p < ∞`, with weak gradient `∇F`, and `F` equal to its precise representative `F̃` at every
Lebesgue point (as in Theorem 5.2). Outside a
polar set `E` of starting points, the pathwise integral of Theorem 5.1 agrees `ℙ_x`-a.s. with
the stochastic Itô integral, and for every `t ∈ [0, T]`
`F(B(t)) - F(B(0)) = ∫_0^t ∇F(B(s)) dB(s) + ½ [∇F(B), B]_π(t)`, `ℙ_x`-a.s. -/
theorem proposition_5_3 {π : ℕ → Partition T} (hT : 0 < T)
    (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {p : ℝ} (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2Plus p F) (hF1 : MemW 2 1 F) (hFloc : MemWLoc 1 2 F)
    {G : Rd d → Rd d} (hG : IsWeakGradient F G)
    (hFrep : ∀ x, IsLebesguePoint F x → F x = preciseRepresentative F x) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
      ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H ∧ ∃ Fm : ℕ → Rd d → ℝ,
        ∀ t ∈ Icc 0 T, ∃ I : CanonicalWienerSpace d T → ℝ, IsItoIntegral x₀ G t I ∧
          ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∃ A : ApproximatingSequence π (CanonicalWienerSpace.path ω) F H,
            A.seq = Fm ∧ weakPathwiseIntegral A t = I ω ∧
            F (CanonicalWienerSpace.path ω t) - F (CanonicalWienerSpace.path ω 0) = I ω + 1 / 2 * weakCovariation A t := by
  sorry

end WeakPathwiseIto
