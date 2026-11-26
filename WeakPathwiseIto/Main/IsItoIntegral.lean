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

variable {d : ℕ} {T : ℝ}

set_option warn.classDefReducibility false in
/-- The natural `σ`-algebra `𝓕_u = σ(B(v) : 0 ≤ v ≤ u)` of the canonical process on `Ω`. -/
def naturalSigma (d : ℕ) (T u : ℝ) : MeasurableSpace (CanonicalWienerSpace d T) :=
  MeasurableSpace.comap (fun ω (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ u}) => ω v) inferInstance

/-- Value at time `u` of the elementary predictable integrand
`∑_j ξ_j 1_{(s_j, s_{j+1}]}(u)`. -/
def elementaryValue {k : ℕ} (s : Fin (k + 1) → ℝ) (ξ : Fin k → CanonicalWienerSpace d T → Rd d)
    (u : ℝ) (ω : CanonicalWienerSpace d T) : Rd d :=
  ∑ j : Fin k, (Ioc (s j.castSucc) (s j.succ)).indicator (fun _ => ξ j ω) u

/-- Elementary stochastic integral `∑_j ⟨ξ_j, B(s_{j+1}) - B(s_j)⟩`. -/
def elementaryIntegral {k : ℕ} (s : Fin (k + 1) → ℝ)
    (ξ : Fin k → CanonicalWienerSpace d T → Rd d) (ω : CanonicalWienerSpace d T) : ℝ :=
  ∑ j : Fin k, ⟪ξ j ω, CanonicalWienerSpace.path ω (s j.succ) -
    CanonicalWienerSpace.path ω (s j.castSucc)⟫

end IsItoIntegral

/-- `I` is (a version of) the stochastic Itô integral `∫_0^t G(B(s)) · dB(s)` under `ℙ_x`
(Proposition 5.3), for the `d`-dimensional Brownian motion `B` and its natural filtration: there
are elementary predictable integrands `H_n` on `[0, t]` with `∫_0^t |H_n(s) - G(B(s))|² ds → 0`
in `ℙ_x`-probability whose elementary integrals converge to `I` in `ℙ_x`-probability (the
localised `L²_loc` Itô integral, [KS91, §3.2.D], [RY99, IV.2]). -/
def IsItoIntegral {d : ℕ} {T : ℝ} (x : Rd d) (G : Rd d → Rd d) (t : ℝ)
    (I : CanonicalWienerSpace d T → ℝ) : Prop :=
  ∃ (k : ℕ → ℕ) (s : ∀ n, Fin (k n + 1) → ℝ)
    (ξ : ∀ n, Fin (k n) → CanonicalWienerSpace d T → Rd d),
    (∀ n, Monotone (s n) ∧ s n 0 = 0 ∧ s n (Fin.last (k n)) = t) ∧
    (∀ n j, Measurable[IsItoIntegral.naturalSigma d T (s n j.castSucc)] (ξ n j)) ∧
    TendstoInMeasure (CanonicalWienerSpace.P x)
      (fun n ω => ∫ u in (0 : ℝ)..t,
        ‖IsItoIntegral.elementaryValue (s n) (ξ n) u ω - G (CanonicalWienerSpace.path ω u)‖ ^ 2)
      atTop (fun _ => 0) ∧
    TendstoInMeasure (CanonicalWienerSpace.P x)
      (fun n => IsItoIntegral.elementaryIntegral (s n) (ξ n)) atTop I

end WeakPathwiseIto
