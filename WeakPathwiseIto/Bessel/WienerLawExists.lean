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

/-- **Subgoal** (Section 2.2 Wiener space, uniqueness step 1: Borel = cylinder σ-algebra): the
Borel σ-algebra of `Ω = C([0, T], ℝ^d)` is the one induced by the coordinate maps, i.e. the
pull-back of the product σ-algebra on `[0, T] → ℝ^d` (Mathlib's
`ContinuousMap.measurableSpace_eq_iSup_comap_eval`). -/
theorem measurableSpace_eq_comap_coe :
    (inferInstance : MeasurableSpace (CanonicalWienerSpace d T)) =
      MeasurableSpace.comap (fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d))
        MeasurableSpace.pi := by
  change ContinuousMap.measurableSpace = _
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- **Subgoal** (Section 2.2 Wiener space, uniqueness step 2): a measure on `Ω` is determined by
the law of the coordinate process `(B(t))_{t ∈ [0, T]}` on the product space. -/
theorem ext_of_map_coe {μ ν : Measure (CanonicalWienerSpace d T)}
    (h : μ.map (fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d)) =
      ν.map (fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d))) : μ = ν := by
  have hm : Measurable fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  ext s hs
  have hs' : MeasurableSet[MeasurableSpace.comap
      (fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d)) MeasurableSpace.pi] s :=
    measurableSpace_eq_comap_coe (d := d) (T := T) ▸ hs
  obtain ⟨S, hS, rfl⟩ := hs'
  rw [← Measure.map_apply hm hS, h, Measure.map_apply hm hS]

/-- **Subgoal** (Section 2.2 Wiener space, uniqueness step 3: finite-dimensional distributions of
`d` independent Brownian motions): for independent real Brownian motions `W^1, …, W^d` and a
finite set of times `I`, `(W^i_s)_{i, s ∈ I}` has law `⊗_i` (Brownian f.d.d. on `I`). -/
theorem map_coords_restrict {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Fin d → ℝ≥0 → Ω' → ℝ}
    (hB : ∀ i, ProbabilityTheory.IsBrownianReal (W i) Q)
    (hind : ProbabilityTheory.iIndepFun (fun i ω' t => W i t ω') Q) (I : Finset ℝ≥0) :
    Q.map (fun ω' (i : Fin d) (s : I) => W i s ω') =
      Measure.pi fun _ : Fin d => ProbabilityTheory.BrownianReal.projectiveFamily I := by
  have hR : ∀ i, AEMeasurable (fun ω' (s : I) => W i s ω') Q := fun i =>
    ((hB i).toIsPreBrownianReal.hasLaw I).aemeasurable
  have hind' : ProbabilityTheory.iIndepFun (fun i ω' (s : I) => W i s ω') Q :=
    hind.comp (fun _ f (s : I) => f s) fun _ => measurable_pi_iff.2 fun s => measurable_pi_apply _
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hR).1 hind']
  congr 1
  funext i
  exact ((hB i).toIsPreBrownianReal.hasLaw I).map_eq

/-- **Subgoal** (Section 2.2 Wiener space, uniqueness step 4: f.d.d. of `ℙ`): if `P` is a law of
Brownian motion started at `x`, its finite-dimensional distribution on `J ⊂ [0, T]` is the image
of the Brownian f.d.d. at the times `J` under `v ↦ (x + ∑_i v^i_t e_i)_{t ∈ J}`. -/
theorem map_restrict_eq {x : Rd d} {P : Measure (CanonicalWienerSpace d T)} (h : IsLaw x P)
    (J : Finset (Icc (0 : ℝ) T)) :
    (P.map fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d)).map J.restrict =
      (Measure.pi fun _ : Fin d =>
          ProbabilityTheory.BrownianReal.projectiveFamily (J.image fun s : Icc (0 : ℝ) T => (s : ℝ).toNNReal)).map
        fun (v : Fin d → (J.image fun s : Icc (0 : ℝ) T => (s : ℝ).toNNReal) → ℝ) (j : J) => x + ∑ i, v i ⟨(j : ℝ).toNNReal, Finset.mem_image_of_mem _ j.2⟩ •
          Rd.basisVec i := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, rfl⟩ := h
  set I : Finset ℝ≥0 := J.image fun s : Icc (0 : ℝ) T => (s : ℝ).toNNReal with hI
  have hG : AEMeasurable (fun ω' => ofCoords (T := T) x (fun i t => W i t ω') fun i => hW i ω') Q := by
    refine aemeasurable_of_aemeasurable_eval fun s => ?_
    simp only [ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  have hm : Measurable fun ω : CanonicalWienerSpace d T => (ω : Icc (0 : ℝ) T → Rd d) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  have hV : AEMeasurable (fun ω' (i : Fin d) (s : I) => W i s ω') Q :=
    AEMeasurable.of_eval fun i => ((hB i).toIsPreBrownianReal.hasLaw I).aemeasurable
  have hF : Measurable fun (v : Fin d → I → ℝ) (j : J) =>
      x + ∑ i, v i ⟨(j : ℝ).toNNReal, Finset.mem_image_of_mem _ j.2⟩ • Rd.basisVec i := by
    fun_prop
  rw [← map_coords_restrict hB hind I, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hV,
    AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hG,
    AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable
      (hm.aemeasurable.comp_aemeasurable hG)]
  rfl

/-- **Subgoal** (Section 2.2 Wiener space): the law of Brownian motion is unique (finite
dimensional distributions determine the law on `C([0, T], ℝ^d)`). -/
theorem isLaw_unique {x : Rd d} {P P' : Measure (CanonicalWienerSpace d T)} (h : IsLaw x P)
    (h' : IsLaw x P') : P = P' := by
  apply ext_of_map_coe
  exact IsProjectiveLimit.unique (fun J => map_restrict_eq h J) (fun J => map_restrict_eq h' J)

/-- **Subgoal** (Section 2.2 Wiener space): `ℙ_x` is the law of Brownian motion started at `x`. -/
theorem isLaw_P (x : Rd d) : IsLaw x (P (T := T) x) :=
  Classical.epsilon_spec (exists_isLaw x)

/-- **Subgoal** (Section 2.2 Wiener space): `ℙ_x` is a probability measure. -/
theorem isProbabilityMeasure_P (x : Rd d) : IsProbabilityMeasure (P (T := T) x) := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, -, hP⟩ := isLaw_P (T := T) x
  rw [hP]
  refine (Measure.isProbabilityMeasure_map_iff (aemeasurable_of_aemeasurable_eval fun s => ?_)).2 hQ
  simp only [ofCoords, ContinuousMap.coe_mk]
  exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
    ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)

end CanonicalWienerSpace

end WeakPathwiseIto
