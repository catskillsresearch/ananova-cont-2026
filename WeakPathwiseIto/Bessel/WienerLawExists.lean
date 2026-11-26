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

/-- **Subgoal** (Section 2.2 Wiener space, measurability of `ω' ↦ x + W(ω')` in `Ω`): a map into
`C(X, Y)` whose evaluations are all a.e.-measurable is a.e.-measurable (evaluate on a countable
dense set, then pass to limits). -/
theorem aemeasurable_of_aemeasurable_eval {X Y Z : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y] [RegularSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [MeasurableSpace Z] {μ : Measure Z} {g : Z → C(X, Y)}
    (hg : ∀ x, AEMeasurable (fun z => g z x) μ) : AEMeasurable g μ := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z₀⟩⟩
  · exact Subsingleton.measurable.aemeasurable
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have := hDc.to_subtype
  set m : D → Z → Y := fun q => (hg q).mk _
  have hm : ∀ q, Measurable (m q) := fun q => (hg q).measurable_mk
  have hae : ∀ᵐ z ∂μ, ∀ q : D, g z q = m q z := ae_all_iff.2 fun q => (hg q).ae_eq_mk
  set N := toMeasurable μ {z | ¬ ∀ q : D, g z q = m q z}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hae
  have hgood : ∀ z, z ∉ N → ∀ q : D, g z q = m q z := fun z hz => by
    by_contra h; exact hz (subset_toMeasurable _ _ h)
  set g' : Z → C(X, Y) := fun z => if z ∈ N then g z₀ else g z
  have hg' : Measurable g' := by
    refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
    have hx : x ∈ closure D := hDd.closure_eq ▸ Set.mem_univ x
    obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 hx
    refine measurable_of_tendsto_metrizable (f := fun n z => g' z (u n)) (fun n => ?_)
      (tendsto_pi_nhds.2 fun z => ((g' z).continuous.tendsto x).comp hu)
    have : (fun z => g' z (u n)) = N.piecewise (fun _ => g z₀ (u n)) (m ⟨u n, huD n⟩) := by
      funext z
      by_cases hz : z ∈ N
      · simp [g', hz, Set.piecewise]
      · simp only [g', hz, if_false, Set.piecewise]
        exact hgood z hz ⟨u n, huD n⟩
    rw [this]
    exact Measurable.piecewise hN measurable_const (hm _)
  refine ⟨g', hg', ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with z hz
  simp [g', hz]

/-- **Subgoal** (Section 2.2 Wiener space): `ℙ_x` is a probability measure. -/
theorem isProbabilityMeasure_P (x : Rd d) : IsProbabilityMeasure (P (T := T) x) := by
  sorry

end CanonicalWienerSpace

end WeakPathwiseIto
