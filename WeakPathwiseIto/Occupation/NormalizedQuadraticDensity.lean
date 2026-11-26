/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The normalised discrete quadratic-variation density of eq. (28) (also used for (11)):
`ρ_{n,ω}(t) := ∑_i |ω(t_{i+1}) - ω(t_i)|² / (t_{i+1} - t_i) · 1_{[t_i, t_{i+1})}(t)`. -/
def normalizedQuadraticDensity {T : ℝ} {d : ℕ} (π : Partition T) (ω : ℝ → Rd d) (t : ℝ) : ℝ :=
  ∑ i : Fin π.m, (Ico (π.left i) (π.right i)).indicator
    (fun _ => ‖ω (π.right i) - ω (π.left i)‖ ^ 2 / (π.right i - π.left i)) t

namespace normalizedQuadraticDensity

/-- **Subgoal** (Lemma A.1, finiteness of `‖ρ_n‖_{L^q}`): `ρ_{n,ω}` is a bounded measurable step
function, hence in every `L^p([0, T])`. -/
theorem memLp {T : ℝ} {d : ℕ} (π : Partition T) (ω : ℝ → Rd d) (p : ℝ≥0∞) :
    MemLp (normalizedQuadraticDensity π ω) p (volume.restrict (Icc 0 T)) := by
  refine MemLp.of_bound ?_ (∑ i : Fin π.m, ‖ω (π.right i) - ω (π.left i)‖ ^ 2 /
    (π.right i - π.left i)) (Eventually.of_forall fun t => ?_)
  · exact (Finset.measurable_sum _ fun i _ =>
      measurable_const.indicator measurableSet_Ico).aestronglyMeasurable
  · unfold normalizedQuadraticDensity
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
    have := π.left_lt_right i
    exact Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))

end normalizedQuadraticDensity

end WeakPathwiseIto
