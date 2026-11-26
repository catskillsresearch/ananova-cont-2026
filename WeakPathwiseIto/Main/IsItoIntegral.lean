/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace IsItoIntegral

variable {d : ℕ}

set_option warn.classDefReducibility false in
/-- The natural `σ`-algebra `𝓕_u = σ(B(v) : v ≤ u)` of the canonical process. -/
def naturalSigma (d : ℕ) (u : ℝ≥0) : MeasurableSpace (ℝ≥0 → Rd d) :=
  MeasurableSpace.comap (fun ω (v : Iic u) => ω v) inferInstance

/-- Value at time `u` of the elementary predictable integrand
`∑_j ξ_j 1_{(s_j, s_{j+1}]}(u)`. -/
def elementaryValue {k : ℕ} (s : Fin (k + 1) → ℝ≥0) (ξ : Fin k → (ℝ≥0 → Rd d) → Rd d)
    (u : ℝ≥0) (ω : ℝ≥0 → Rd d) : Rd d :=
  ∑ j : Fin k, (Ioc (s j.castSucc) (s j.succ)).indicator (fun _ => ξ j ω) u

/-- Elementary stochastic integral `∑_j ⟨ξ_j, B(s_{j+1}) - B(s_j)⟩`. -/
def elementaryIntegral {k : ℕ} (s : Fin (k + 1) → ℝ≥0) (ξ : Fin k → (ℝ≥0 → Rd d) → Rd d)
    (ω : ℝ≥0 → Rd d) : ℝ :=
  ∑ j : Fin k, ⟪ξ j ω, ω (s j.succ) - ω (s j.castSucc)⟫

end IsItoIntegral

/-- `I` is (a version of) the stochastic Itô integral `∫_0^t G(B(s)) dB(s)` under `ℙ_x`
(used in Proposition 5.3): there are elementary predictable integrands `H_n` on `[0, t]` with
`∫_0^t |H_n(s) - G(B(s))|² ds → 0` in `ℙ_x`-probability whose elementary integrals converge to
`I` in `ℙ_x`-probability. -/
def IsItoIntegral {d : ℕ} (W : CanonicalWienerSpace d) (x : Rd d) (G : Rd d → Rd d) (t : ℝ≥0)
    (I : (ℝ≥0 → Rd d) → ℝ) : Prop :=
  ∃ (k : ℕ → ℕ) (s : ∀ n, Fin (k n + 1) → ℝ≥0) (ξ : ∀ n, Fin (k n) → (ℝ≥0 → Rd d) → Rd d),
    (∀ n, Monotone (s n) ∧ s n 0 = 0 ∧ s n (Fin.last (k n)) = t) ∧
    (∀ n j, Measurable[IsItoIntegral.naturalSigma d (s n j.castSucc)] (ξ n j)) ∧
    TendstoInMeasure (W.P x)
      (fun n ω => ∫ u in (0 : ℝ)..(t : ℝ),
        ‖IsItoIntegral.elementaryValue (s n) (ξ n) u.toNNReal ω - G (ω u.toNNReal)‖ ^ 2)
      atTop (fun _ => 0) ∧
    TendstoInMeasure (W.P x) (fun n => IsItoIntegral.elementaryIntegral (s n) (ξ n)) atTop I

end WeakPathwiseIto
