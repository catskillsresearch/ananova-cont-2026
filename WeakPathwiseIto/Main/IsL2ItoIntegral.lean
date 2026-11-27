/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.IsItoIntegral

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- `I` is (a version of) the `L²` stochastic integral `∫_0^t H(s) · dB(s)` under `ℙ_x` of an
integrand `H` with `E ∫_0^t |H(s)|² ds < ∞` (the integral used for the stopped integrals
`J^R(t)` in the proof of Proposition 5.3): there are elementary predictable integrands
`H_n = ∑_j ξ_{n,j} 1_{(s_{n,j}, s_{n,j+1}]}` on grids `0 = s_{n,0} ≤ … ≤ s_{n,k_n} = t`, with
`ξ_{n,j} ∈ L²(ℙ_x)` `𝓕_{s_{n,j}}`-measurable, such that `H_n → H` in `L²(dℙ_x ⊗ ds)` on
`(0, t]` and `∫ H_n dB → I` in `L²(ℙ_x)` (the limit through the Itô isometry). -/
def IsL2ItoIntegral {d : ℕ} {T : ℝ} (x : Rd d) (H : ℝ → CanonicalWienerSpace d T → Rd d)
    (t : ℝ) (I : CanonicalWienerSpace d T → ℝ) : Prop :=
  (∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x) < ∞ ∧
  ∃ (k : ℕ → ℕ) (s : ∀ n, Fin (k n + 1) → ℝ)
    (ξ : ∀ n, Fin (k n) → CanonicalWienerSpace d T → Rd d),
    (∀ n, Monotone (s n) ∧ s n 0 = 0 ∧ s n (Fin.last (k n)) = t) ∧
    (∀ n j, Measurable[IsItoIntegral.naturalSigma d T (s n j.castSucc)] (ξ n j)) ∧
    (∀ n j, MemLp (ξ n j) 2 (CanonicalWienerSpace.P (T := T) x)) ∧
    Tendsto (fun n => ∫⁻ ω, (∫⁻ u in Ioc 0 t,
        ‖IsItoIntegral.elementaryValue (s n) (ξ n) u ω - H u ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (IsItoIntegral.elementaryIntegral (s n) (ξ n) - I) 2
        (CanonicalWienerSpace.P (T := T) x)) atTop (𝓝 0)

end WeakPathwiseIto
