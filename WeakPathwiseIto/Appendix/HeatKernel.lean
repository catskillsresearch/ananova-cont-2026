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

/-- **Subgoal** (Lemma B.2 proof, eq. (34), scaling `s = |x|² u`):
`p_{|x|² u}(x) / (|x|² u) = |x|^{-d} |x|^{-2} · (2πu)^{-d/2} e^{-1/(2u)} / u`. -/
theorem div_scaling (x : Rd d) (hx : x ≠ 0) {u : ℝ} (hu : 0 < u) :
    heatKernel d (‖x‖ ^ 2 * u) x / (‖x‖ ^ 2 * u) =
      ‖x‖ ^ (-(d : ℝ)) / ‖x‖ ^ 2 *
        ((2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  unfold heatKernel
  have h1 : 2 * Real.pi * (‖x‖ ^ 2 * u) = ‖x‖ ^ 2 * (2 * Real.pi * u) := by ring
  have h2 : (‖x‖ ^ 2) ^ (-(d : ℝ) / 2) = ‖x‖ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have h3 : -‖x‖ ^ 2 / (2 * (‖x‖ ^ 2 * u)) = -1 / (2 * u) := by
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), h2, h3]
  field_simp

/-- **Subgoal** (Lemma B.2 proof, eq. (34), unit profile): for `d ≥ 1`,
`u ↦ (2πu)^{-d/2} e^{-1/(2u)} / u` is integrable on `(0, ∞)` (substitute `v = 1/u`, Gamma
integral). -/
theorem integrableOn_unitProfile (hd : 0 < d) :
    IntegrableOn (fun u : ℝ => (2 * Real.pi * u) ^ (-(d : ℝ) / 2) * Real.exp (-1 / (2 * u)) / u)
      (Ioi 0) := by
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
