/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Occupation.NormalizedQuadraticDensity
public import WeakPathwiseIto.Appendix.GaussianMoment

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

/-- **Lemma A.1.** If `∑_{n ≥ 1} |π_n| < ∞` and `q > 1`, then
`‖ρ_{n,B}‖^q_{L^q([0,T])} → c_{q,d} T`, `ℙ_x`-almost surely. -/
theorem lemma_A_1 {π : ℕ → Partition T}
    (hπ : Summable fun n => (π (n + 1)).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x), Tendsto
      (fun n => ∫ t in Icc 0 T, |normalizedQuadraticDensity (π n) (CanonicalWienerSpace.path ω) t| ^ q)
      atTop (𝓝 (gaussianMoment d q * T)) := by
  sorry

/-- **Lemma A.1** (consequence): `sup_n ‖ρ_{n,B}‖_{L^q([0,T])} < ∞`, `ℙ_x`-almost surely. -/
theorem lemma_A_1_bounded {π : ℕ → Partition T}
    (hπ : Summable fun n => (π (n + 1)).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) (CanonicalWienerSpace.path ω))
        (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K := by
  filter_upwards [lemma_A_1 hπ hq x] with ω hω
  obtain ⟨B, hB⟩ := hω.bddAbove_range
  refine ⟨ENNReal.ofReal (max B 0 ^ q⁻¹), ENNReal.ofReal_lt_top, fun n => ?_⟩
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [(normalizedQuadraticDensity.memLp (π n) _ _).eLpNorm_eq_integral_rpow_norm hq0
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) ?_
    (by have : 0 < q := by linarith
        positivity))
  simp only [Real.norm_eq_abs]
  exact (hB ⟨n, rfl⟩).trans (le_max_left _ _)

end WeakPathwiseIto
