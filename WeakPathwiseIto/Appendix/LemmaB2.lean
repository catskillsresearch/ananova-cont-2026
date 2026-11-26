/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Occupation.DiscreteSeminorm
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Lemma B.2.** Let `π` satisfy Assumptions 1 and 2 and `(h_m) ⊂ L^1(ℝ^d)` be nonnegative
finite-valued Borel functions with `‖h_m‖_{L^1} → 0` and, for every compact `K`,
`∫_K ∫_K |h_m(x) - h_m(y)| / |x - y|^d dx dy < ∞`. Then there are a polar set `E` and a
subsequence `(h_{m_k})` with `lim_k limsup_n ‖h_{m_k}‖_{n,1,B} = 0`, `ℙ_{x₀}`-a.s. for every
`x₀ ∉ E`. -/
theorem lemma_B_2 {T : ℝ} {d : ℕ} (W : CanonicalWienerSpace d) {π : ℕ → Partition T}
    (hT : 0 < T) (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {h : ℕ → Rd d → ℝ}
    (hmeas : ∀ m, Measurable (h m)) (hnonneg : ∀ m, 0 ≤ h m) (hint : ∀ m, Integrable (h m))
    (hL1 : Tendsto (fun m => eLpNorm (h m) 1 volume) atTop (𝓝 0))
    (hreg : ∀ m, ∀ K : Set (Rd d), IsCompact K →
      ∫⁻ x in K, ∫⁻ y in K, ‖h m x - h m y‖ₑ / edist x y ^ (d : ℝ) < ⊤) :
    ∃ E : Set (Rd d), IsBrownianPolar W E ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x₀ ∉ E,
      ∀ᵐ ω ∂(W.P x₀), Tendsto
        (fun k => limsup (fun n => discreteSeminorm (π n) 1 (fun x => ‖h (φ k) x‖ₑ)
          (CanonicalWienerSpace.pathOn ω)) atTop) atTop (𝓝 0) := by
  sorry

end WeakPathwiseIto
