/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition
public import WeakPathwiseIto.Appendix.PotentialProfile
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Gaussian heat kernel `p_s(x) := (2πs)^{-d/2} e^{-|x|²/(2s)}` (Appendix B). -/
def heatKernel (d : ℕ) (s : ℝ) (x : Rd d) : ℝ :=
  (2 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * s))

namespace heatKernel

variable {d : ℕ}

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (32) [FP00]: `∫_0^T p_s(x) ds ≤ C(R) ν(|x|)` for `|x| ≤ R`. -/
theorem integral_le_potentialProfile (T R : ℝ) : ∃ C : ℝ, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ R →
    ∫ s in Ioc 0 T, heatKernel d s x ≤ C * potentialProfile d ‖x‖ := by
  sorry

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (34): `∫_0^T p_s(x) / s ds ≤ C |x|^{-d}`. -/
theorem integral_div_le (T : ℝ) : ∃ C : ℝ, ∀ x : Rd d, x ≠ 0 →
    ∫ s in Ioc 0 T, heatKernel d s x / s ≤ C * ‖x‖ ^ (-(d : ℝ)) := by
  sorry

/-- **Subgoal** (Lemma B.2 proof, eqs. (32)–(35)). Eq. (35) [FP00]: under Assumptions 1 and 2,
`∑_i p_{t_i}(x) (t_{i+1} - t_i) ≤ C(R) ν(|x|)` for `|x| ≤ R`. -/
theorem riemannSum_le_potentialProfile {T : ℝ} {π : ℕ → Partition T}
    (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) (R : ℝ) :
    ∃ C : ℝ, ∀ n, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ R →
      ∑ i : Fin (π n).m, heatKernel d ((π n).left i) x * ((π n).right i - (π n).left i) ≤
        C * potentialProfile d ‖x‖ := by
  sorry

end heatKernel

end WeakPathwiseIto
