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
  sorry

/-- **Subgoal** (Lemma 4.2 proof: increments are bounded by the oscillation):
`|ω(t_{i+1}) - ω(t_i)| ≤ osc(ω, π_n)`. -/
theorem norm_increment_le (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T) (i : Fin p.m) :
    ‖ω (p.right i) - ω (p.left i)‖ ≤ pathOscillation ω p := by
  sorry

/-- **Subgoal** (Lemma 4.2 proof: Stieltjes measure of an interval): for `0 ≤ a ≤ b ≤ T`,
`d tr[ω]_π((a, b]) = tr[ω]_π(b) - tr[ω]_π(a)`, and `d tr[ω]_π` does not charge `{0}`. -/
theorem traceMeasure_Ioc (hQV : HasQuadraticVariation π ω) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ T) :
    hQV.traceMeasure.real (Ioc a b) = hQV.trace b - hQV.trace a ∧
      hQV.traceMeasure {0} = 0 := by
  sorry

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
    |∫ x, φ x * discreteOccupationDensity p ω x -
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
  sorry

end WeakPathwiseIto
