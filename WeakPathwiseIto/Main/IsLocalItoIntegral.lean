/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.ExitTime
public import WeakPathwiseIto.Main.IsL2ItoIntegral

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The integrand stopped at `τ_R`: `H(u) 1_{u ≤ τ_R}`, so that
`∫_0^{t ∧ τ_R} H dB = ∫_0^t H(u) 1_{u ≤ τ_R} dB(u)`. -/
def stoppedIntegrand {d : ℕ} {T : ℝ} (H : ℝ → CanonicalWienerSpace d T → Rd d) (R : ℝ)
    (u : ℝ) (ω : CanonicalWienerSpace d T) : Rd d :=
  if ENNReal.ofReal u ≤ CanonicalWienerSpace.exitTime R ω then H u ω else 0

/-- `J` is the local Itô integral `J(t) = ∫_0^t H(s) · dB(s)`, `t ∈ [0, T]`, under `ℙ_x`, as
constructed in the proof of Proposition 5.3: with the exit times `τ_R`,
* `E ∫_0^{T ∧ τ_R} |H(s)|² ds < ∞` for every integer `R ≥ 1`;
* the stopped integrals `J^R(t) := ∫_0^{t ∧ τ_R} H dB` are `L²` stochastic integrals
  (`IsL2ItoIntegral`), taken in versions with continuous paths on `[0, T]`;
* the family `(J^R)_{R ≥ 1}` is consistent under stopping;
* `τ_R ↑ ∞` almost surely (on `Ω = C([0, T], ℝ^d)`: almost every path has `τ_R = ∞`, i.e.
  stays in `B_R` on `[0, T]`, for some integer `R`);
* `J` has continuous paths on `[0, T]` and `J(t) = J^R(t)` for `t ≤ τ_R`. -/
def IsLocalItoIntegral {d : ℕ} {T : ℝ} (x : Rd d) (H : ℝ → CanonicalWienerSpace d T → Rd d)
    (J : ℝ → CanonicalWienerSpace d T → ℝ) : Prop :=
  ∃ JR : ℕ → ℝ → CanonicalWienerSpace d T → ℝ,
    (∀ R : ℕ, 1 ≤ R → (∫⁻ ω, (∫⁻ u in Ioc 0 T, ‖stoppedIntegrand H R u ω‖ₑ ^ 2)
      ∂CanonicalWienerSpace.P (T := T) x) < ∞) ∧
    (∀ R : ℕ, 1 ≤ R → ∀ t ∈ Icc 0 T, IsL2ItoIntegral x (stoppedIntegrand H R) t (JR R t)) ∧
    (∀ R : ℕ, 1 ≤ R → ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x,
      ContinuousOn (fun t => JR R t ω) (Icc 0 T)) ∧
    (∀ R R' : ℕ, 1 ≤ R → R ≤ R' → ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ∀ t ∈ Icc 0 T,
      ENNReal.ofReal t ≤ CanonicalWienerSpace.exitTime R ω → JR R t ω = JR R' t ω) ∧
    (∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ∃ R : ℕ, 1 ≤ R ∧
      CanonicalWienerSpace.exitTime R ω = ⊤) ∧
    (∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => J t ω) (Icc 0 T)) ∧
    (∀ R : ℕ, 1 ≤ R → ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ∀ t ∈ Icc 0 T,
      ENNReal.ofReal t ≤ CanonicalWienerSpace.exitTime R ω → J t ω = JR R t ω)

end WeakPathwiseIto
