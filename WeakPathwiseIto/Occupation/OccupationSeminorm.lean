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

/-- **Subgoal** (Section 4.2 seminorm): subadditivity. The measurability hypotheses are the paper's
standing assumption (the seminorm is only applied to Hessians of Sobolev functions); without them
the statement is false, since Lean's `∫⁻` is only superadditive on non-measurable integrands
(e.g. indicators of a Bernstein set and its complement). -/
theorem add_le (π : ℕ → Partition T) (ω : ℝ → Rd d) {f g : Rd d → F}
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    occupationSeminorm π ω (f + g) ≤ occupationSeminorm π ω f + occupationSeminorm π ω g := by
  unfold occupationSeminorm
  have hL : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) :=
    fun n => by
      unfold discreteOccupationDensity
      exact (integrable_finset_sum _ fun i _ =>
        discreteOccupationDensity.integrable_piece _ _).aemeasurable.ennreal_ofReal
  have key : ∀ u v : ℕ → ℝ≥0∞, limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop := by
    intro u v
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    have h2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.2 hε.ne')).ne'
    have hu : limsup u atTop < limsup u atTop + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).1.ne h2
    have hv : limsup v atTop < limsup v atTop + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 hlt).2.ne h2
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_lt_of_limsup_lt hu, eventually_lt_of_limsup_lt hv] with n h1 h3
    calc (u + v) n = u n + v n := rfl
      _ ≤ (limsup u atTop + (ε : ℝ≥0∞) / 2) + (limsup v atTop + (ε : ℝ≥0∞) / 2) :=
          add_le_add h1.le h3.le
      _ = limsup u atTop + limsup v atTop + ε := by
          rw [add_add_add_comm, ENNReal.add_halves]
  refine (limsup_le_limsup (Eventually.of_forall fun n => ?_)).trans (key _ _)
  rw [Pi.add_apply]
  calc _ ≤ ∫⁻ x, (‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x) +
        ‖g x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) :=
        lintegral_mono fun x => by
          rw [← add_mul, Pi.add_apply]
          exact mul_le_mul_left (enorm_add_le (f x) (g x)) _
    _ = _ := lintegral_add_left' (hf.enorm.mul (hL n)) _

namespace eq_10

/-- **Subgoal** (Eq. (10) proof, maximal function on a closed ball): for `0 < ρ ≤ 1`,
`∫_{B̄(a,ρ)} |f| ≤ |B(a,ρ)| M_1 f(a)`. -/
theorem lintegral_closedBall_le (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ ≤
      volume (Metric.ball a ρ) * localMaximalFunction 1 f a := by
  sorry

/-- **Subgoal** (Eq. (10) proof, `d ≤ 2`): on `B̄(a,ρ)` the kernel `|x-a|^{2-d}` is at most
`ρ^{2-d}`, so `∫_{B̄(a,ρ)} |f| |x-a|^{2-d} ≤ C ρ² M_1 f(a)`. -/
theorem lintegral_kernel_le_of_le_two (hd : d ≤ 2) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d)
    {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      C * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
  sorry

/-- **Subgoal** (Eq. (10) proof, `d ≥ 3`, dyadic shell): on the shell
`ρ 2^{-(k+1)} < |x-a| ≤ ρ 2^{-k}` the kernel is at most `(ρ 2^{-(k+1)})^{2-d}`, so the integral
is at most `(ρ 2^{-(k+1)})^{2-d} |B(a, ρ 2^{-k})| M_1 f(a)`. -/
theorem lintegral_shell_le (hd : 3 ≤ d) (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (k : ℕ) :
    ∫⁻ x in {x | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k},
        ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) *
        volume (Metric.ball a (ρ / 2 ^ k)) * localMaximalFunction 1 f a := by
  sorry

/-- **Subgoal** (Eq. (10) proof, `d ≥ 3`): summing the dyadic shells (a geometric series),
`∫_{B̄(a,ρ)} |f| |x-a|^{2-d} ≤ C ρ² M_1 f(a)`. -/
theorem lintegral_kernel_le_of_three_le (hd : 3 ≤ d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d)
    {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      C * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
  sorry

/-- **Subgoal** (Eq. (10) proof, one increment): if `|b - a| ≤ 1` then
`∫ |f| 𝓛^{n,i}_ω ≤ C (M_1 f(b) + M_1 f(a)) |b - a|²`, since `Q ⊆ B̄(a,|b-a|) ∩ B̄(b,|b-a|)`. -/
theorem lintegral_piece_le (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a b : Rd d), ‖b - a‖ ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      C * (localMaximalFunction 1 f b + localMaximalFunction 1 f a) *
        ENNReal.ofReal (‖b - a‖ ^ 2) := by
  sorry

end eq_10

/-- **Subgoal** (Eq. (10)). Estimate (10): if `osc(ω, π_n) ≤ 1` then
`∫ |f| 𝓛^{π_n}_ω ≤ C_d ∑_i (M_1 f(ω(t_{i+1})) + M_1 f(ω(t_i))) |ω(t_{i+1}) - ω(t_i)|²`.
The continuity of `ω` is the paper's standing assumption of Section 4.1 (`ω ∈ C[0,T]`); without it
`osc(ω, π_n) ≤ 1` can hold vacuously (the `iSup` of an unbounded family is `0`) and (10) fails. -/
theorem lintegral_le_maximal (d : ℕ) : ∃ C : ℝ≥0, ∀ (π : Partition T) (ω : ℝ → Rd d)
    (f : Rd d → ℝ), ContinuousOn ω (Icc 0 T) → LocallyIntegrable f → pathOscillation ω π ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x) ≤
      C * ∑ i : Fin π.m, (localMaximalFunction 1 f (ω (π.right i)) +
        localMaximalFunction 1 f (ω (π.left i))) * ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2) := by
  sorry

/-- **Subgoal** (Eq. (11)). Estimate (11): if `osc(ω, π_n) → 0` and `sup_n ‖ρ_{n,ω}‖_{L^q([0,T])} < ∞` with
`1/p + 1/q = 1`, then `‖f‖_{W^0_{ω,π}} ≤ C_{p,ω} limsup_n ‖M_1 f‖_{n,p,ω}`.
The continuity of `ω` is the paper's standing assumption of Section 4.1 (`ω ∈ C[0,T]`), needed
for (10). -/
theorem le_limsup_discreteSeminorm {p q : ℝ} (hpq : p.HolderConjugate q) (π : ℕ → Partition T)
    (ω : ℝ → Rd d) (hω : ContinuousOn ω (Icc 0 T)) (hosc : pathOscillation.Vanishes ω π)
    (hρ : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) ω) (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K)
    (f : Rd d → ℝ) (hf : LocallyIntegrable f) : ∃ C : ℝ≥0∞, C < ⊤ ∧
    occupationSeminorm π ω f ≤
      C * limsup (fun n => discreteSeminorm (π n) p (localMaximalFunction 1 f) ω) atTop := by
  sorry

end occupationSeminorm

end WeakPathwiseIto
