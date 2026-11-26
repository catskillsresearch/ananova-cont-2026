/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.DiscreteOccupationDensity
public import WeakPathwiseIto.Occupation.WeightedOccupationMeasure
public import WeakPathwiseIto.Smooth.PathOscillation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace lemma_4_2

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}

open scoped Classical in
/-- **Subgoal** (Lemma 4.2 proof: discrete trace): for `t ∈ [0, T]`,
`∑_{t_{i+1} ≤ t} |ω(t_{i+1}) - ω(t_i)|² → tr[ω]_π(t)`. -/
theorem tendsto_discreteTrace (hQV : HasQuadraticVariation π ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ t),
      ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2) atTop (𝓝 (hQV.trace t)) := by
  have hcoord : ∀ (j : Fin d) (v w : Rd d), Rd.coord j v - Rd.coord j w = (v - w) j := by
    intro j v w
    simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]
  have e : ∀ n, (∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ t),
      ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2) =
      ∑ j, discreteQuadraticVariation (π n) (fun s => Rd.coord j (ω s)) t := by
    intro n
    unfold discreteQuadraticVariation
    simp_rw [EuclideanSpace.real_norm_sq_eq, hcoord]
    exact Finset.sum_comm
  simp_rw [e]
  unfold HasQuadraticVariation.trace
  exact tendsto_finset_sum _ fun j _ => (hQV.coord j).tendsto t ht

/-- **Subgoal** (Lemma 4.2 proof: total discrete quadratic variation):
`∑_i |ω(t_{i+1}) - ω(t_i)|² → tr[ω]_π(T)`. -/
theorem tendsto_sum_sq (hQV : HasQuadraticVariation π ω) :
    Tendsto (fun n => ∑ i, ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2) atTop
      (𝓝 (hQV.trace T)) := by
  have hT : T ∈ Icc 0 T := ⟨(π 0).nonneg, le_rfl⟩
  refine (tendsto_discreteTrace hQV hT).congr fun n => ?_
  rw [Finset.filter_true_of_mem fun i _ => ((π n).t_mem i.succ).2]

/-- **Subgoal** (Lemma 4.2 proof: increments are bounded by the oscillation):
`|ω(t_{i+1}) - ω(t_i)| ≤ osc(ω, π_n)`. -/
theorem norm_increment_le (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T) (i : Fin p.m) :
    ‖ω (p.right i) - ω (p.left i)‖ ≤ pathOscillation ω p := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hω).isBounded.exists_norm_le
  set C' := max C 0 with hC'
  have hsub : ∀ j : Fin p.m, Icc (p.left j) (p.right j) ⊆ Icc 0 T := fun j s hs =>
    ⟨(p.t_mem j.castSucc).1.trans hs.1, hs.2.trans (p.t_mem j.succ).2⟩
  have hb : ∀ s ∈ Icc 0 T, ‖ω s‖ ≤ C' := fun s hs =>
    (hC _ (Set.mem_image_of_mem ω hs)).trans (le_max_left _ _)
  have h3 : ∀ (j : Fin p.m) (s : ℝ),
      (⨆ (_ : s ∈ Icc (p.left j) (p.right j)), ‖ω s - ω (p.left j)‖) ≤ 2 * C' := by
    intro j s
    refine Real.iSup_le (fun hs => ?_) (by positivity)
    have h1 := hb s (hsub j hs)
    have h2 := hb (p.left j) (hsub j ⟨le_rfl, (p.left_lt_right j).le⟩)
    calc ‖ω s - ω (p.left j)‖ ≤ ‖ω s‖ + ‖ω (p.left j)‖ := norm_sub_le _ _
      _ ≤ 2 * C' := by linarith
  have hbdd2 : ∀ j : Fin p.m, BddAbove (range fun s : ℝ =>
      ⨆ (_ : s ∈ Icc (p.left j) (p.right j)), ‖ω s - ω (p.left j)‖) :=
    fun j => ⟨2 * C', Set.forall_mem_range.2 (h3 j)⟩
  have hbdd1 : BddAbove (range fun j : Fin p.m => ⨆ (s : ℝ)
      (_ : s ∈ Icc (p.left j) (p.right j)), ‖ω s - ω (p.left j)‖) :=
    (Set.finite_range _).bddAbove
  have hmem : p.right i ∈ Icc (p.left i) (p.right i) := ⟨(p.left_lt_right i).le, le_rfl⟩
  unfold pathOscillation
  refine le_ciSup_of_le hbdd1 i (le_ciSup_of_le (hbdd2 i) (p.right i) ?_)
  exact le_ciSup (f := fun _ : p.right i ∈ Icc (p.left i) (p.right i) =>
    ‖ω (p.right i) - ω (p.left i)‖) (Set.finite_range _).bddAbove hmem

/-- **Subgoal** (Lemma 4.2 proof: Stieltjes measure of an interval): for `0 ≤ a ≤ b ≤ T`,
`d tr[ω]_π((a, b]) = tr[ω]_π(b) - tr[ω]_π(a)`, and `d tr[ω]_π` does not charge `{0}`. -/
theorem traceMeasure_Ioc (hQV : HasQuadraticVariation π ω) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ T) :
    hQV.traceMeasure.real (Ioc a b) = hQV.trace b - hQV.trace a ∧
      hQV.traceMeasure {0} = 0 := by
  have hT : 0 ≤ T := (π 0).nonneg
  have hcl : ∀ i, Continuous (hQV.coord i).qvExt := fun i => by
    unfold HasScalarQuadraticVariation.qvExt
    exact (hQV.coord i).continuousOn.comp_continuous
      (by fun_prop : Continuous fun t : ℝ => max 0 (min t T))
      (fun t => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩)
  have hc : Continuous hQV.traceExt := by
    unfold HasQuadraticVariation.traceExt
    exact continuous_finset_sum _ fun i _ => hcl i
  set F := hQV.traceExt_monotone.stieltjesFunction with hFdef
  have hF : ∀ x, F x = hQV.traceExt x := fun x => by
    rw [hFdef, Monotone.stieltjesFunction_eq]
    exact (hQV.traceExt_monotone.continuousWithinAt_Ioi_iff_rightLim_eq).1 hc.continuousWithinAt
  have hFc : Continuous F := by
    have : (F : ℝ → ℝ) = hQV.traceExt := funext hF
    rw [this]; exact hc
  have hclamp : ∀ t ∈ Icc 0 T, hQV.traceExt t = hQV.trace t := fun t ht => by
    unfold HasQuadraticVariation.traceExt HasQuadraticVariation.trace
      HasScalarQuadraticVariation.qvExt
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hmeas : hQV.traceMeasure = F.measure := rfl
  constructor
  · rw [Measure.real_def, hmeas, StieltjesFunction.measure_Ioc, hF, hF,
      ENNReal.toReal_ofReal (sub_nonneg.2 (hQV.traceExt_monotone hab)),
      hclamp b ⟨ha.trans hab, hb⟩, hclamp a ⟨ha, hab.trans hb⟩]
  · rw [hmeas, StieltjesFunction.measure_singleton,
      (F.mono.continuousWithinAt_Iio_iff_leftLim_eq).1 hFc.continuousWithinAt, sub_self,
      ENNReal.ofReal_zero]

/-- **Subgoal** (Lemma 4.2 proof: Riemann–Stieltjes convergence): for `g` continuous on `[0, T]`,
`∑_i g(t_{i+1}) |ω(t_{i+1}) - ω(t_i)|² → ∫_{[0,T]} g d tr[ω]_π` (weak convergence of the
discrete quadratic-variation measures, from pointwise convergence of their distribution
functions to the continuous `tr[ω]_π`). -/
theorem tendsto_riemannStieltjes (hQV : HasQuadraticVariation π ω) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) :
    Tendsto (fun n => ∑ i, g ((π n).right i) * ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)
      atTop (𝓝 (∫ t in Icc 0 T, g t ∂hQV.traceMeasure)) := by
  sorry

/-- **Subgoal** (Lemma 4.2 proof, first display): if `|φ(x) - φ(y)| ≤ ε` whenever
`|x - y| ≤ osc(ω, π_n)`, then
`|∫ φ 𝓛^{π_n}_ω - ∑_i φ(ω(t_i)) |ω(t_{i+1}) - ω(t_i)|²| ≤ ε ∑_i |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem abs_integral_sub_le (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hmod : ∀ x y, ‖x - y‖ ≤ pathOscillation ω p → |φ x - φ y| ≤ ε) :
    |(∫ x, φ x * discreteOccupationDensity p ω x) -
        ∑ i, φ (ω (p.left i)) * ‖ω (p.right i) - ω (p.left i)‖ ^ 2| ≤
      ε * ∑ i, ‖ω (p.right i) - ω (p.left i)‖ ^ 2 := by
  sorry

/-- **Subgoal** (Lemma 4.2 proof, last display): with `φ` uniformly continuous and (6),
`∑_i φ(ω(t_i)) |ω(t_{i+1}) - ω(t_i)|² → ∫_0^T φ(ω(t)) d tr[ω]_π(t)`. -/
theorem tendsto_sum_left (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {φ : Rd d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∑ i, φ (ω ((π n).left i)) * ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)
      atTop (𝓝 (∫ t in Icc 0 T, φ (ω t) ∂hQV.traceMeasure)) := by
  sorry

end lemma_4_2

/-- **Lemma 4.2.** For `ω ∈ Q_π([0,T], ℝ^d)` satisfying (6), the densities `𝓛^{π_n}_ω` converge
weakly to the weighted occupation measure `μ^T_ω`: for every `φ ∈ C_c(ℝ^d)`,
`∫ φ 𝓛^{π_n}_ω dx → ∫ φ dμ^T_ω`. -/
theorem lemma_4_2 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {φ : Rd d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, φ x * discreteOccupationDensity (π n) ω x) atTop
      (𝓝 (∫ x, φ x ∂weightedOccupationMeasure hQV)) := by
  rw [weightedOccupationMeasure.integral_eq hω hQV hφ]
  set S : ℕ → ℝ := fun n => ∑ i, ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 with hSdef
  set b : ℕ → ℝ := fun n =>
    ∑ i, φ (ω ((π n).left i)) * ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 with hbdef
  set a : ℕ → ℝ := fun n => ∫ x, φ x * discreteOccupationDensity (π n) ω x with hadef
  have hS := lemma_4_2.tendsto_sum_sq hQV
  set M : ℝ := |hQV.trace T| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hevS : ∀ᶠ n in atTop, S n ≤ M := (hS.eventually (gt_mem_nhds
    (show hQV.trace T < M by rw [hM]; linarith [le_abs_self (hQV.trace T)]))).mono fun n h => h.le
  have hu := hφc.uniformContinuous_of_continuous hφ
  have hdiff : Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.1 hu (ε / (2 * M)) (by positivity)
    filter_upwards [hevS, hosc.eventually (gt_mem_nhds hδ)] with n hn hon
    have hmod : ∀ x y, ‖x - y‖ ≤ pathOscillation ω (π n) → |φ x - φ y| ≤ ε / (2 * M) :=
      fun x y hxy => by
        have := hδφ (show dist x y < δ by rw [dist_eq_norm]; linarith)
        rw [Real.dist_eq] at this
        exact this.le
    have hle := lemma_4_2.abs_integral_sub_le hω (π n) hφ hφc hmod
    have hS0 : 0 ≤ S n := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.dist_eq, sub_zero]
    calc |a n - b n| ≤ ε / (2 * M) * S n := by simp only [hadef, hbdef, hSdef]; exact hle
      _ ≤ ε / (2 * M) * M := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have h := (lemma_4_2.tendsto_sum_left hω hQV hosc hφ hφc).add hdiff
  rw [add_zero] at h
  exact h.congr fun n => by simp only [hadef, hbdef]; ring

end WeakPathwiseIto
