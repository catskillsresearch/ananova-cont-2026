/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.IsItoIntegral

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace WeakPathwiseIto

/-- A process `H : [0, ∞) × Ω → ℝ^d` is progressively measurable for the natural filtration
`𝓕_r = σ(B(v) : v ≤ r)` of the canonical process: for every `r ≥ 0`, `(u, ω) ↦ H(u, ω)` on
`[0, r] × Ω` is `𝓑([0, r]) ⊗ 𝓕_r`-measurable (the class of integrands of the standard Itô
integral used in the proof of Proposition 5.3). -/
def IsProgressive {d : ℕ} {T : ℝ} (H : ℝ → CanonicalWienerSpace d T → Rd d) : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    Measurable[MeasurableSpace.prod (inferInstance : MeasurableSpace (Icc (0 : ℝ) r))
      (IsItoIntegral.naturalSigma d T r)] (fun p : Icc (0 : ℝ) r × CanonicalWienerSpace d T =>
        H p.1 p.2)

end WeakPathwiseIto
