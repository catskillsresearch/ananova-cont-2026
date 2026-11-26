/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.DiscreteOccupationDensity
public import WeakPathwiseIto.Occupation.NormalizedQuadraticDensity
public import WeakPathwiseIto.Occupation.DiscreteSeminorm
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Smooth.PathOscillation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The seminorm `‖f‖_{W^0_{ω,π}} := limsup_n ∫ |f(x)| 𝓛^{π_n}_ω(x) dx` (Section 4.2). -/
def occupationSeminorm {T : ℝ} {d : ℕ} {F : Type*} [NormedAddCommGroup F] (π : ℕ → Partition T)
    (ω : ℝ → Rd d) (f : Rd d → F) : ℝ≥0∞ :=
  limsup (fun n => ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) atTop

namespace occupationSeminorm

variable {T : ℝ} {d : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- **Subgoal** (Section 4.2 seminorm). -/
theorem add_le (π : ℕ → Partition T) (ω : ℝ → Rd d) (f g : Rd d → F) :
    occupationSeminorm π ω (f + g) ≤ occupationSeminorm π ω f + occupationSeminorm π ω g := by
  sorry

/-- **Subgoal** (Eq. (10)). Estimate (10): if `osc(ω, π_n) ≤ 1` then
`∫ |f| 𝓛^{π_n}_ω ≤ C_d ∑_i (M_1 f(ω(t_{i+1})) + M_1 f(ω(t_i))) |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem lintegral_le_maximal (d : ℕ) : ∃ C : ℝ≥0, ∀ (π : Partition T) (ω : ℝ → Rd d)
    (f : Rd d → ℝ), LocallyIntegrable f → pathOscillation ω π ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x) ≤
      C * ∑ i : Fin π.m, (localMaximalFunction 1 f (ω (π.right i)) +
        localMaximalFunction 1 f (ω (π.left i))) * ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2) := by
  sorry

/-- **Subgoal** (Eq. (11)). Estimate (11): if `osc(ω, π_n) → 0` and `sup_n ‖ρ_{n,ω}‖_{L^q([0,T])} < ∞` with
`1/p + 1/q = 1`, then `‖f‖_{W^0_{ω,π}} ≤ C_{p,ω} limsup_n ‖M_1 f‖_{n,p,ω}`. -/
theorem le_limsup_discreteSeminorm {p q : ℝ} (hpq : p.HolderConjugate q) (π : ℕ → Partition T)
    (ω : ℝ → Rd d) (hosc : pathOscillation.Vanishes ω π)
    (hρ : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) ω) (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K)
    (f : Rd d → ℝ) (hf : LocallyIntegrable f) : ∃ C : ℝ≥0∞, C < ⊤ ∧
    occupationSeminorm π ω f ≤
      C * limsup (fun n => discreteSeminorm (π n) p (localMaximalFunction 1 f) ω) atTop := by
  sorry

end occupationSeminorm

end WeakPathwiseIto
