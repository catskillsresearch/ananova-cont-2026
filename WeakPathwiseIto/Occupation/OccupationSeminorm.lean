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
  set ν := volume.withDensity (fun x => ‖f x‖ₑ) with hνdef
  have hν : ∀ s, MeasurableSet s → ∫⁻ x in s, ‖f x‖ₑ = ν s := fun s hs =>
    (withDensity_apply _ hs).symm
  rw [hν _ Metric.isClosed_closedBall.measurableSet]
  have hsph : ν (Metric.sphere a ρ) = 0 := by
    rw [← hν _ Metric.isClosed_sphere.measurableSet]
    apply setLIntegral_measure_zero
    rcases subsingleton_or_nontrivial (Rd d) with h | h
    · have : Metric.sphere a ρ = ∅ := by
        ext x
        simp [Subsingleton.elim x a, hρ.ne, hρ.ne']
      rw [this, measure_empty]
    · exact Measure.addHaar_sphere volume a ρ
  have hcb : ν (Metric.closedBall a ρ) ≤ ν (Metric.ball a ρ) := by
    rw [← Metric.ball_union_sphere]
    exact (measure_union_le _ _).trans (by rw [hsph, add_zero])
  refine hcb.trans ?_
  have hU : Metric.ball a ρ = ⋃ n : ℕ, Metric.ball a (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ => Metric.ball a (ρ - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
    Metric.ball_subset_ball (by
      have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      have := one_div_le_one_div_of_le (by positivity) this
      linarith)
  conv_lhs => rw [hU]
  rw [hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  by_cases hr : ρ - 1 / ((n : ℝ) + 1) ≤ 0
  · rw [Metric.ball_eq_empty.2 hr, measure_empty]; exact bot_le
  push Not at hr
  rw [← hν _ Metric.isOpen_ball.measurableSet]
  have : Fact (volume (Metric.ball a (ρ - 1 / ((n : ℝ) + 1))) < ⊤) := ⟨measure_ball_lt_top⟩
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hlt : ENNReal.ofReal (ρ - 1 / ((n : ℝ) + 1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  have hM : laverage (volume.restrict (Metric.ball a (ρ - 1 / ((n : ℝ) + 1)))) (fun y => ‖f y‖ₑ) ≤
      localMaximalFunction 1 f a := by
    unfold localMaximalFunction
    exact le_iSup_of_le (ρ - 1 / ((n : ℝ) + 1)) (le_iSup_of_le hr (le_iSup_of_le hlt le_rfl))
  rw [← measure_mul_laverage, Measure.restrict_apply_univ]
  exact mul_le_mul' (measure_mono (Metric.ball_subset_ball (by linarith))) hM

/-- **Subgoal** (Eq. (10) proof, scaling of balls): `|B(a,ρ)| = ρ^d |B(0,1)|` for `ρ > 0`, in every
dimension (including `d = 0`). -/
theorem volume_ball_eq (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (Metric.ball a ρ) = ENNReal.ofReal (ρ ^ d) * volume (Metric.ball (0 : Rd d) 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h : ∀ (b : Rd 0) (r : ℝ), 0 < r → Metric.ball b r = univ := fun b r hr => by
      ext x
      simp [Metric.mem_ball, EuclideanSpace.dist_eq, hr]
    rw [h a ρ hρ, h 0 1 one_pos, pow_zero, ENNReal.ofReal_one, one_mul]
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    rw [Measure.addHaar_ball volume a hρ.le, finrank_euclideanSpace_fin]

/-- **Subgoal** (Eq. (10) proof, `d ≤ 2`): on `B̄(a,ρ)` the kernel `|x-a|^{2-d}` is at most
`ρ^{2-d}`, so `∫_{B̄(a,ρ)} |f| |x-a|^{2-d} ≤ C ρ² M_1 f(a)`. -/
theorem lintegral_kernel_le_of_le_two (hd : d ≤ 2) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d)
    {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      C * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
  refine ⟨(volume (Metric.ball (0 : Rd d) 1)).toNNReal, fun f a ρ hρ hρ1 => ?_⟩
  have hC : ((volume (Metric.ball (0 : Rd d) 1)).toNNReal : ℝ≥0∞) =
      volume (Metric.ball (0 : Rd d) 1) := ENNReal.coe_toNNReal measure_ball_lt_top.ne
  have he : (0 : ℝ) ≤ 2 - (d : ℝ) := by
    have : (d : ℝ) ≤ 2 := by exact_mod_cast hd
    linarith
  calc _ ≤ ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (ρ ^ (2 - (d : ℝ))) :=
        setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun x hx => by
          rw [Metric.mem_closedBall, dist_eq_norm] at hx
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (norm_nonneg _) hx he)) _
    _ = (∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ) * ENNReal.ofReal (ρ ^ (2 - (d : ℝ))) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ (volume (Metric.ball a ρ) * localMaximalFunction 1 f a) *
          ENNReal.ofReal (ρ ^ (2 - (d : ℝ))) :=
        mul_le_mul_left (lintegral_closedBall_le f a hρ hρ1) _
    _ = _ := by
        have hsplit : ρ ^ 2 = ρ ^ (2 - (d : ℝ)) * ρ ^ d := by
          rw [← Real.rpow_natCast ρ d, ← Real.rpow_add hρ]; norm_num
        rw [volume_ball_eq a hρ, hC, hsplit,
          ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
        ring

/-- **Subgoal** (Eq. (10) proof, `d ≥ 3`, dyadic shell): on the shell
`ρ 2^{-(k+1)} < |x-a| ≤ ρ 2^{-k}` the kernel is at most `(ρ 2^{-(k+1)})^{2-d}`, so the integral
is at most `(ρ 2^{-(k+1)})^{2-d} |B(a, ρ 2^{-k})| M_1 f(a)`. -/
theorem lintegral_shell_le (hd : 3 ≤ d) (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (k : ℕ) :
    ∫⁻ x in {x | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k},
        ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) *
        volume (Metric.ball a (ρ / 2 ^ k)) * localMaximalFunction 1 f a := by
  have hpos : 0 < ρ / 2 ^ (k + 1) := by positivity
  have hpos' : 0 < ρ / 2 ^ k := by positivity
  have hle1 : ρ / 2 ^ k ≤ 1 :=
    (div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hρ1
  have he : 2 - (d : ℝ) ≤ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hS : MeasurableSet {x : Rd d | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k} :=
    (measurableSet_lt measurable_const (measurable_norm.comp (measurable_id.sub_const a))).inter
      (measurableSet_le (measurable_norm.comp (measurable_id.sub_const a)) measurable_const)
  have hsub : {x : Rd d | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k} ⊆
      Metric.closedBall a (ρ / 2 ^ k) := fun x hx => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.2
  calc _ ≤ ∫⁻ x in {x | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k},
        ‖f x‖ₑ * ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) :=
        setLIntegral_mono' hS fun x hx =>
          mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos hpos hx.1.le he)) _
    _ = (∫⁻ x in {x | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k}, ‖f x‖ₑ) *
          ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ (∫⁻ x in Metric.closedBall a (ρ / 2 ^ k), ‖f x‖ₑ) *
          ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) :=
        mul_le_mul_left (lintegral_mono_set hsub) _
    _ ≤ (volume (Metric.ball a (ρ / 2 ^ k)) * localMaximalFunction 1 f a) *
          ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) :=
        mul_le_mul_left (lintegral_closedBall_le f a hpos' hle1) _
    _ = _ := by ring

/-- **Subgoal** (Eq. (10) proof, `d ≥ 3`): summing the dyadic shells (a geometric series),
`∫_{B̄(a,ρ)} |f| |x-a|^{2-d} ≤ C ρ² M_1 f(a)`. -/
theorem lintegral_kernel_le_of_three_le (hd : 3 ≤ d) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d)
    {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
      C * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
  refine ⟨(volume (Metric.ball (0 : Rd d) 1)).toNNReal * 2 ^ d * 2, fun f a ρ hρ hρ1 => ?_⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set V := volume (Metric.ball (0 : Rd d) 1) with hV
  have hVc : ((V.toNNReal : ℝ≥0) : ℝ≥0∞) = V := ENNReal.coe_toNNReal measure_ball_lt_top.ne
  set S : ℕ → Set (Rd d) := fun k => {x | ρ / 2 ^ (k + 1) < ‖x - a‖ ∧ ‖x - a‖ ≤ ρ / 2 ^ k}
    with hSdef
  have hcover : Metric.closedBall a ρ ⊆ {a} ∪ ⋃ k, S k := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    right
    have hr : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
    have hxr : ‖x - a‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hx
    have hex : ∃ k : ℕ, ρ / 2 ^ (k + 1) < ‖x - a‖ := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ρ / ‖x - a‖) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hr] at hn
      rw [div_lt_iff₀ (by positivity), pow_succ]
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith
    classical
    refine mem_iUnion.2 ⟨Nat.find hex, show _ ∧ _ from ⟨Nat.find_spec hex, ?_⟩⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, div_one]; exact hxr
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      rw [hj]; exact not_lt.1 this
  have hterm : ∀ k : ℕ, ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) *
      volume (Metric.ball a (ρ / 2 ^ k)) * localMaximalFunction 1 f a ≤
      V * 2 ^ d * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a * 2⁻¹ ^ k := fun k => by
    have hu : 0 < ρ / 2 ^ (k + 1) := by positivity
    have h1 : ρ / 2 ^ k = 2 * (ρ / 2 ^ (k + 1)) := by rw [pow_succ]; field_simp
    have hA : (ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ)) * (ρ / 2 ^ (k + 1)) ^ d = (ρ / 2 ^ (k + 1)) ^ 2 := by
      rw [← Real.rpow_natCast (ρ / 2 ^ (k + 1)) d, ← Real.rpow_add hu,
        show (2 - (d : ℝ)) + d = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2k : (2 : ℝ) ^ k ≤ (2 ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hAB : (ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ)) * (ρ / 2 ^ k) ^ d ≤
        2 ^ d * ρ ^ 2 * (1 / 2) ^ k := by
      rw [h1, mul_pow, mul_left_comm, hA, div_pow, one_div_pow, mul_assoc, mul_one_div]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2k) (by positivity)
    have hhalf : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    have hE : ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) * ENNReal.ofReal ((ρ / 2 ^ k) ^ d) ≤
        2 ^ d * ENNReal.ofReal (ρ ^ 2) * 2⁻¹ ^ k := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
      refine (ENNReal.ofReal_le_ofReal hAB).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), hhalf,
        ENNReal.ofReal_ofNat]
    rw [volume_ball_eq a (by positivity)]
    calc _ = (ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) *
          ENNReal.ofReal ((ρ / 2 ^ k) ^ d)) * V * localMaximalFunction 1 f a := by ring
      _ ≤ (2 ^ d * ENNReal.ofReal (ρ ^ 2) * 2⁻¹ ^ k) * V * localMaximalFunction 1 f a :=
          mul_le_mul_left (mul_le_mul_left hE _) _
      _ = _ := by ring
  have h0 : volume ({a} : Set (Rd d)) = 0 := measure_singleton a
  calc _ ≤ ∫⁻ x in {a} ∪ ⋃ k, S k, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ x in {a}, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
          ∫⁻ x in ⋃ k, S k, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ x in ⋃ k, S k, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) := by
        rw [setLIntegral_measure_zero _ _ h0, zero_add]
    _ ≤ ∑' k, ∫⁻ x in S k, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k, ENNReal.ofReal ((ρ / 2 ^ (k + 1)) ^ (2 - (d : ℝ))) *
          volume (Metric.ball a (ρ / 2 ^ k)) * localMaximalFunction 1 f a :=
        ENNReal.tsum_le_tsum fun k => lintegral_shell_le hd f a hρ hρ1 k
    _ ≤ ∑' k, V * 2 ^ d * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a * 2⁻¹ ^ k :=
        ENNReal.tsum_le_tsum hterm
    _ = V * 2 ^ d * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a * 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    _ = _ := by
        push_cast
        rw [hVc]
        ring

/-- **Subgoal** (Eq. (10) proof, one increment): if `|b - a| ≤ 1` then
`∫ |f| 𝓛^{n,i}_ω ≤ C (M_1 f(b) + M_1 f(a)) |b - a|²`, since `Q ⊆ B̄(a,|b-a|) ∩ B̄(b,|b-a|)`.
(`f` is assumed a.e.-strongly measurable, as for every `f ∈ L¹_loc` in (10).) -/
theorem lintegral_piece_le (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a b : Rd d),
    AEStronglyMeasurable f → ‖b - a‖ ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      C * (localMaximalFunction 1 f b + localMaximalFunction 1 f a) *
        ENNReal.ofReal (‖b - a‖ ^ 2) := by
  have hK : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
      ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
        K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
    rcases le_or_gt d 2 with h | h
    · exact lintegral_kernel_le_of_le_two h
    · exact lintegral_kernel_le_of_three_le (by omega)
  obtain ⟨K, hK⟩ := hK
  refine ⟨(occupationConstant d).toNNReal * K, fun f a b hf hab => ?_⟩
  by_cases h : a = b
  · subst h; simp [discreteOccupationDensity.piece]
  set ρ := ‖b - a‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
  have hc : 0 ≤ occupationConstant d := by unfold occupationConstant; positivity
  have hρd : dist a b = ρ := by rw [hρdef, dist_comm, dist_eq_norm]
  have hQ : MeasurableSet (incrementBall a b) := measurableSet_closedBall
  have hQa : incrementBall a b ⊆ Metric.closedBall a ρ := by
    intro x hx
    simp only [incrementBall, Metric.mem_closedBall] at hx ⊢
    calc dist x a ≤ dist x (midpoint ℝ a b) + dist (midpoint ℝ a b) a := dist_triangle _ _ _
      _ ≤ dist a b / 2 + dist a b / 2 := by
          gcongr
          rw [dist_midpoint_left]; norm_num; ring_nf; rfl
      _ = ρ := by rw [hρd]; ring
  have hQb : incrementBall a b ⊆ Metric.closedBall b ρ := by
    intro x hx
    simp only [incrementBall, Metric.mem_closedBall] at hx ⊢
    calc dist x b ≤ dist x (midpoint ℝ a b) + dist (midpoint ℝ a b) b := dist_triangle _ _ _
      _ ≤ dist a b / 2 + dist a b / 2 := by
          gcongr
          rw [dist_midpoint_right]; norm_num; ring_nf; rfl
      _ = ρ := by rw [hρd]; ring
  have hpt : ∀ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) =
      (incrementBall a b).indicator (fun x => ENNReal.ofReal (occupationConstant d) *
        (‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) +
          ‖f x‖ₑ * ENNReal.ofReal (‖x - b‖ ^ (2 - (d : ℝ))))) x := by
    intro x
    simp only [discreteOccupationDensity.piece, h, if_false]
    by_cases hx : x ∈ incrementBall a b
    · rw [indicator_of_mem hx, indicator_of_mem hx, ENNReal.ofReal_mul hc,
        ENNReal.ofReal_add (by positivity) (by positivity)]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  have hma : AEMeasurable (fun x => ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) :=
    hf.enorm.mul (by fun_prop)
  calc ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x)
      = ∫⁻ x in incrementBall a b, ENNReal.ofReal (occupationConstant d) *
          (‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) +
            ‖f x‖ₑ * ENNReal.ofReal (‖x - b‖ ^ (2 - (d : ℝ)))) := by
        simp_rw [hpt]; exact lintegral_indicator hQ _
    _ = ENNReal.ofReal (occupationConstant d) *
          ((∫⁻ x in incrementBall a b, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
            ∫⁻ x in incrementBall a b, ‖f x‖ₑ * ENNReal.ofReal (‖x - b‖ ^ (2 - (d : ℝ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hma.restrict]
    _ ≤ ENNReal.ofReal (occupationConstant d) *
          ((∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
            ∫⁻ x in Metric.closedBall b ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - b‖ ^ (2 - (d : ℝ)))) := by
        exact mul_le_mul_right (add_le_add (lintegral_mono_set hQa) (lintegral_mono_set hQb)) _
    _ ≤ ENNReal.ofReal (occupationConstant d) *
          (K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a +
            K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f b) := by
        gcongr
        · exact hK f a hρ hab
        · exact hK f b hρ hab
    _ = _ := by
        rw [ENNReal.coe_mul, show (((occupationConstant d).toNNReal : ℝ≥0) : ℝ≥0∞) =
          ENNReal.ofReal (occupationConstant d) from rfl]
        ring

/-- **Subgoal** (Eq. (10) proof: increments are bounded by the oscillation):
`|ω(t_{i+1}) - ω(t_i)| ≤ osc(ω, π_n)`. (Same statement as `lemma_4_2.norm_increment_le`,
restated here so that this module does not import `Occupation.Lemma42`.) -/
theorem norm_increment_le {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T) (i : Fin p.m) :
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
  obtain ⟨C, hC⟩ := eq_10.lintegral_piece_le d
  refine ⟨C, fun π ω f hω hf hosc => ?_⟩
  have hc : 0 ≤ occupationConstant d := by unfold occupationConstant; positivity
  have hnn : ∀ (a b x : Rd d), 0 ≤ discreteOccupationDensity.piece a b x := by
    intro a b x
    unfold discreteOccupationDensity.piece
    split_ifs
    · exact le_rfl
    · exact indicator_nonneg (fun y _ => mul_nonneg hc (by positivity)) _
  have hmeas : ∀ (a b : Rd d), Measurable (discreteOccupationDensity.piece a b) := by
    intro a b
    unfold discreteOccupationDensity.piece
    split_ifs
    · exact measurable_const
    · exact Measurable.indicator (by fun_prop) measurableSet_closedBall
  have hfm : AEStronglyMeasurable f := hf.aestronglyMeasurable
  calc ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x)
      = ∫⁻ x, ∑ i : Fin π.m, ‖f x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x) := by
        congr 1; funext x
        rw [discreteOccupationDensity, ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn _ _ x),
          Finset.mul_sum]
    _ = ∑ i : Fin π.m, ∫⁻ x, ‖f x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x) :=
        lintegral_finset_sum' _ (fun i _ =>
          hfm.enorm.mul (ENNReal.measurable_ofReal.comp (hmeas _ _)).aemeasurable)
    _ ≤ ∑ i : Fin π.m, C * ((localMaximalFunction 1 f (ω (π.right i)) +
          localMaximalFunction 1 f (ω (π.left i))) *
            ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2)) := by
        gcongr with i
        rw [← mul_assoc]
        exact hC f _ _ hfm ((eq_10.norm_increment_le hω π i).trans hosc)
    _ = _ := by rw [Finset.mul_sum]

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
