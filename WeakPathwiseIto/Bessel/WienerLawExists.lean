/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace CanonicalWienerSpace

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Section 2.2 Wiener space): the law `ℙ_x` of Brownian motion started at `x`
exists on `C([0, T], ℝ^d)`. To be proved from the vendored `BrownianMotion` construction
(`ProbabilityTheory.brownian`, `isBrownianReal_brownian`, `continuous_brownian`) on the product
`Measure.pi` of `d` copies of `gaussianLimit`. -/
theorem exists_isLaw (x : Rd d) : ∃ P : Measure (CanonicalWienerSpace d T), IsLaw x P := by
  refine ⟨_, Fin d → (ℝ≥0 → ℝ), inferInstance,
    Measure.pi fun _ => ProbabilityTheory.gaussianLimit,
    fun i t ω' => ProbabilityTheory.brownian t (ω' i),
    fun i ω' => ProbabilityTheory.continuous_brownian (ω' i), inferInstance, fun i => ?_, ?_, rfl⟩
  · exact
      { hasLaw := fun I => (ProbabilityTheory.isBrownianReal_brownian.hasLaw I).comp
          (measurePreserving_eval (μ := fun _ : Fin d => ProbabilityTheory.gaussianLimit) i).hasLaw
        cont := Filter.Eventually.of_forall fun ω' => ProbabilityTheory.continuous_brownian (ω' i) }
  · exact ProbabilityTheory.iIndepFun_pi (X := fun (_ : Fin d) ω t => ProbabilityTheory.brownian t ω)
      fun _ => (measurable_pi_iff.mpr ProbabilityTheory.measurable_brownian).aemeasurable

/-- **Subgoal** (Section 2.2 Wiener space): the law of Brownian motion is unique (finite
dimensional distributions determine the law on `C([0, T], ℝ^d)`). -/
theorem isLaw_unique {x : Rd d} {P P' : Measure (CanonicalWienerSpace d T)} (h : IsLaw x P)
    (h' : IsLaw x P') : P = P' := by
  sorry

/-- **Subgoal** (Section 2.2 Wiener space): `ℙ_x` is the law of Brownian motion started at `x`. -/
theorem isLaw_P (x : Rd d) : IsLaw x (P (T := T) x) :=
  Classical.epsilon_spec (exists_isLaw x)

/-- **Subgoal** (Section 2.2 Wiener space): `ℙ_x` is a probability measure. -/
theorem isProbabilityMeasure_P (x : Rd d) : IsProbabilityMeasure (P (T := T) x) := by
  sorry

end CanonicalWienerSpace

end WeakPathwiseIto
