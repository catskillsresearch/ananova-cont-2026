/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.Remark44
public import WeakPathwiseIto.Occupation.DiscreteLocalTime
public import WeakPathwiseIto.Main.Theorem51

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {π : ℕ → Partition T} {ω : ℝ → Rd 1}

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): the coordinate of `v ∈ ℝ^1` is `v 0`. -/
theorem Rd.coord_one_apply (v : Rd 1) : Rd.coord 0 v = v 0 := by
  simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): `|v| = |v^0|` on `ℝ^1`. -/
theorem Rd.norm_one_eq (v : Rd 1) : ‖v‖ = |Rd.coord 0 v| := by
  rw [Rd.coord_one_apply]
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- **Subgoal** (Remark 4.5, identifying `ℝ` with `ℝ^1`): the coordinate map `ℝ^1 → ℝ` is
injective. -/
theorem Rd.coord_one_injective : Function.Injective (Rd.coord (d := 1) 0) := fun v w h => by
  rw [Rd.coord_one_apply, Rd.coord_one_apply] at h
  ext i; fin_cases i; exact h

/-- **Subgoal** (Remark 4.5, eq. (7) for `d = 1`): `c_1 = 2 / |B(0,1)| = 1`. -/
theorem occupationConstant_one : occupationConstant 1 = 1 := by
  set e : Rd 1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ) with he
  have hmp : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
      (volume_preserving_funUnique (Fin 1) ℝ)
  have hnorm : ∀ x : Rd 1, ‖x‖ = |e x| := fun x => by
    simp [he, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have hball : e.symm ⁻¹' Metric.ball 0 1 = Ioo (-1) 1 := by
    ext t
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hnorm,
      MeasurableEquiv.apply_symm_apply, Set.mem_Ioo, abs_lt]
  have hvol : volume (Metric.ball (0 : Rd 1) 1) = volume (Ioo (-1 : ℝ) 1) := by
    rw [← hball, hmp.symm.measure_preimage measurableSet_ball.nullMeasurableSet]
  rw [occupationConstant, hvol, Real.volume_Ioo]
  norm_num

/-- **Subgoal** (Remark 4.5, eq. (7) for `d = 1`): the increment ball `Q` from `a` to `b` in `ℝ^1`
is the closed interval `[a ∧ b, a ∨ b]` (in coordinates). -/
theorem incrementBall_one_iff (a b x : Rd 1) : x ∈ incrementBall a b ↔
    Rd.coord 0 x ∈ Icc (min (Rd.coord 0 a) (Rd.coord 0 b)) (max (Rd.coord 0 a) (Rd.coord 0 b)) := by
  have hc : ∀ v w : Rd 1, Rd.coord 0 (v - w) = Rd.coord 0 v - Rd.coord 0 w := fun v w => by
    simp [Rd.coord_one_apply]
  have hm : Rd.coord 0 (midpoint ℝ a b) = (Rd.coord 0 a + Rd.coord 0 b) / 2 := by
    simp [Rd.coord_one_apply, midpoint_eq_smul_add]; ring
  rw [incrementBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, Rd.norm_one_eq,
    Rd.norm_one_eq,
    hc, hc, hm, mem_Icc]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := abs_le.1 h
    rcases le_total (Rd.coord 0 a) (Rd.coord 0 b) with hab | hab
    · rw [abs_sub_comm (Rd.coord 0 a),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 b - Rd.coord 0 a)] at h1 h2
      rw [min_eq_left hab, max_eq_right hab]; constructor <;> linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 a - Rd.coord 0 b)] at h1 h2
      rw [min_eq_right hab, max_eq_left hab]; constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases le_total (Rd.coord 0 a) (Rd.coord 0 b) with hab | hab
    · rw [min_eq_left hab] at h1; rw [max_eq_right hab] at h2
      rw [abs_sub_comm (Rd.coord 0 a),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 b - Rd.coord 0 a)]
      rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right hab] at h1; rw [max_eq_left hab] at h2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Rd.coord 0 a - Rd.coord 0 b)]
      rw [abs_le]; constructor <;> linarith

/-- **Subgoal** (Remark 4.5, eq. (7) for `d = 1`): the single-increment density from `a` to `b`
is `(|u - a| + |u - b|) 1_{[a ∧ b, a ∨ b]}(u)` at the level `u = x^0` (`c_1 = 1`). -/
theorem discreteOccupationDensity.piece_one (a b x : Rd 1) : discreteOccupationDensity.piece a b x =
    (Icc (min (Rd.coord 0 a) (Rd.coord 0 b)) (max (Rd.coord 0 a) (Rd.coord 0 b))).indicator
      (fun u => |u - Rd.coord 0 a| + |u - Rd.coord 0 b|) (Rd.coord 0 x) := by
  have hc : ∀ v w : Rd 1, Rd.coord 0 (v - w) = Rd.coord 0 v - Rd.coord 0 w := fun v w => by
    simp [Rd.coord_one_apply]
  unfold discreteOccupationDensity.piece
  split_ifs with hab
  · subst hab
    by_cases hx : Rd.coord 0 x ∈
        Icc (min (Rd.coord 0 a) (Rd.coord 0 a)) (max (Rd.coord 0 a) (Rd.coord 0 a))
    · rw [indicator_of_mem hx]
      rw [min_self, max_self, Icc_self, mem_singleton_iff] at hx
      simp [hx]
    · rw [indicator_of_notMem hx]
  · by_cases hx : x ∈ incrementBall a b
    · rw [indicator_of_mem hx, indicator_of_mem ((incrementBall_one_iff a b x).1 hx),
        occupationConstant_one, Rd.norm_one_eq, Rd.norm_one_eq, hc, hc]
      norm_num
    · rw [indicator_of_notMem hx,
        indicator_of_notMem (fun h => hx ((incrementBall_one_iff a b x).2 h))]

/-- **Subgoal** (Remarks 4.1 and 4.5): the `j`-th left endpoint of `←π` is `T - t_{m-j}`. -/
theorem Partition.reverse_left {T : ℝ} (π : Partition T) (j : Fin π.m) :
    π.reverse.left j = T - π.right (Fin.rev j) := by
  simp [Partition.left, Partition.right, Partition.reverse, Fin.rev_castSucc]

/-- **Subgoal** (Remarks 4.1 and 4.5): the `j`-th right endpoint of `←π` is `T - t_{m-j-1}`. -/
theorem Partition.reverse_right {T : ℝ} (π : Partition T) (j : Fin π.m) :
    π.reverse.right j = T - π.left (Fin.rev j) := by
  simp [Partition.left, Partition.right, Partition.reverse, Fin.rev_succ]

/-- **Subgoal** (Remark 4.5, `λ^{n,-}_T`): reindexing `j ↦ m-1-j`, the reversed increment from
`b = x(t_{i+1})` to `a = x(t_i)` contributes `2 |a - u| 1_{[a ∧ b, a ∨ b)}(u)`. -/
theorem discreteLocalTime.reversed_eq {T : ℝ} (π : Partition T) (x : ℝ → ℝ) (u : ℝ) :
    discreteLocalTime.reversed π x u = ∑ i : Fin π.m,
      (Ico (min (x (π.left i)) (x (π.right i))) (max (x (π.left i)) (x (π.right i)))).indicator
        (fun u => 2 * |x (π.left i) - u|) u := by
  simp only [discreteLocalTime.reversed, discreteLocalTime, discreteLocalTime.reversePath]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  rw [Fin.revPerm_apply, Partition.reverse_left π j, Partition.reverse_right π j, sub_sub_cancel,
    sub_sub_cancel,
    min_comm, max_comm]
  rfl

/-- **Subgoal** (Remark 4.5, identity off the endpoints): if `u ≠ a, b` then
`(|u-a|+|u-b|) 1_{[a∧b, a∨b]}(u) = ½ (2|b-u| + 2|a-u|) 1_{[a∧b, a∨b)}(u)`. -/
theorem remark_4_5_term_eq {a b u : ℝ} (ha : u ≠ a) (hb : u ≠ b) :
    (Icc (min a b) (max a b)).indicator (fun u => |u - a| + |u - b|) u =
      1 / 2 * ((Ico (min a b) (max a b)).indicator (fun u => 2 * |b - u|) u +
        (Ico (min a b) (max a b)).indicator (fun u => 2 * |a - u|) u) := by
  have hmax : u ≠ max a b := by rcases max_choice a b with h | h <;> rw [h] <;> assumption
  by_cases hu : u ∈ Ico (min a b) (max a b)
  · rw [indicator_of_mem (Ico_subset_Icc_self hu), indicator_of_mem hu, indicator_of_mem hu,
      abs_sub_comm b, abs_sub_comm a]
    ring
  · have hu' : u ∉ Icc (min a b) (max a b) := fun h => hu ⟨h.1, lt_of_le_of_ne h.2 hmax⟩
    rw [indicator_of_notMem hu', indicator_of_notMem hu, indicator_of_notMem hu]
    ring

/-- **Remark 4.5** (one-dimensional case, identity). For `d = 1`, up to the choice of interval
endpoints (i.e. for a.e. level `u`), `𝓛^{π_n}_ω(u) = ½ (λ^{n,+}_T(u) + λ^{n,-}_T(u))`, where
`λ^{n,+}_T` is the discrete local time of `ω` along `π_n` and `λ^{n,-}_T` that of the reversed
path along the reversed partition. (`ℝ` is identified with `ℝ^1` through the coordinate.) -/
theorem remark_4_5_identity (p : Partition T) (ω : ℝ → Rd 1) :
    (fun v => discreteOccupationDensity p ω v) =ᵐ[volume] fun v =>
      1 / 2 * (discreteLocalTime p (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v) +
        discreteLocalTime.reversed p (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) := by
  set x : ℝ → ℝ := fun t => Rd.coord 0 (ω t)
  have hfin : (Rd.coord 0 ⁻¹' (⋃ i : Fin p.m, {x (p.left i), x (p.right i)})).Finite :=
    (finite_iUnion fun i => (finite_singleton _).insert _).preimage Rd.coord_one_injective.injOn
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)] with v hv
  simp only [mem_preimage, mem_iUnion, mem_insert_iff, mem_singleton_iff, not_exists,
    not_or] at hv
  simp only [discreteOccupationDensity, discreteOccupationDensity.piece_one,
    discreteLocalTime.reversed_eq, discreteLocalTime,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => remark_4_5_term_eq (hv i).1 (hv i).2

/-- **Subgoal** (Remark 4.5, weak convergence is a.e.-invariant): if `f_n = f'_n` and `ℓ = ℓ'`
a.e., then `f_n ⇀ ℓ` in `L^r` implies `f'_n ⇀ ℓ'`. -/
theorem remark_4_5.weakLpTendsto_congr {d : ℕ} {r : ℝ≥0∞} {f f' : ℕ → Rd d → ℝ} {ℓ ℓ' : Rd d → ℝ}
    (hf : ∀ n, f n =ᵐ[volume] f' n) (hℓ : ℓ =ᵐ[volume] ℓ') (h : WeakLpTendsto r f ℓ) :
    WeakLpTendsto r f' ℓ' := by
  refine ⟨fun n => (h.1 n).ae_eq (hf n), h.2.1.ae_eq hℓ, fun g hg => ?_⟩
  have h1 : ∀ n, ∫ x, g x * f n x = ∫ x, g x * f' n x := fun n =>
    integral_congr_ae ((hf n).mono fun x hx => by simp [hx])
  have h2 : ∫ x, g x * ℓ x = ∫ x, g x * ℓ' x := integral_congr_ae (hℓ.mono fun x hx => by simp [hx])
  simp_rw [← h1, ← h2]
  exact h.2.2 g hg

/-- **Subgoal** (Remark 4.5, averaging): if `a_n ⇀ ℓ` and `b_n ⇀ ℓ` in `L^r`, `1 < r`, then
`½ (a_n + b_n) ⇀ ℓ`. -/
theorem remark_4_5.weakLpTendsto_half_add {d : ℕ} {r : ℝ≥0∞} (hr : 1 < r) {a b : ℕ → Rd d → ℝ}
    {ℓ : Rd d → ℝ} (ha : WeakLpTendsto r a ℓ) (hb : WeakLpTendsto r b ℓ) :
    WeakLpTendsto r (fun n x => 1 / 2 * (a n x + b n x)) ℓ := by
  refine ⟨fun n => ((ha.1 n).add (hb.1 n)).const_mul _, ha.2.1, fun g hg => ?_⟩
  have heq : ∀ n, ∫ x, g x * (1 / 2 * (a n x + b n x)) =
      1 / 2 * ((∫ x, g x * a n x) + ∫ x, g x * b n x) := fun n => by
    rw [← integral_add (remark_4_4.integrable_mul_conj hr (ha.1 n) hg)
      (remark_4_4.integrable_mul_conj hr (hb.1 n) hg), ← integral_const_mul]
    congr 1; funext x; ring
  simp_rw [heq]
  have := ((ha.2.2 g hg).add (hb.2.2 g hg)).const_mul (1 / 2 : ℝ)
  convert this using 2
  ring

/-- **Subgoal** (Remark 4.5, positivity of weak limits): a weak `L^r` limit, `1 < r`, of
nonnegative functions is a.e. nonnegative. -/
theorem remark_4_5.ae_nonneg_of_weakLpTendsto {d : ℕ} {r : ℝ≥0∞} (hr : 1 < r)
    {f : ℕ → Rd d → ℝ} {ℓ : Rd d → ℝ} (hf : ∀ n x, 0 ≤ f n x) (h : WeakLpTendsto r f ℓ) :
    0 ≤ᵐ[volume] ℓ := by
  obtain ⟨hne, -, -⟩ := remark_4_4.conjExponent_facts hr
  set ℓ' := h.2.1.aestronglyMeasurable.mk ℓ
  have hℓ' : ℓ =ᵐ[volume] ℓ' := h.2.1.aestronglyMeasurable.ae_eq_mk
  have hm : StronglyMeasurable ℓ' := h.2.1.aestronglyMeasurable.stronglyMeasurable_mk
  have hk : ∀ k : ℕ, volume ({x | ℓ' x < 0} ∩ Metric.ball (0 : Rd d) k) = 0 := by
    intro k
    set S := {x | ℓ' x < 0} ∩ Metric.ball (0 : Rd d) k
    have hS : MeasurableSet S := (hm.measurable measurableSet_Iio).inter Metric.isOpen_ball.measurableSet
    have hSf : volume S ≠ ∞ := (measure_mono inter_subset_right).trans_lt measure_ball_lt_top |>.ne
    have hg : MemLp (S.indicator fun _ => (1 : ℝ)) r.conjExponent := memLp_indicator_const _ hS.nullMeasurableSet 1 (Or.inr hSf)
    have hlim := h.2.2 _ hg
    have hge : 0 ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x * ℓ x :=
      ge_of_tendsto' hlim fun n => integral_nonneg fun x => by
        by_cases hx : x ∈ S <;> simp [hx, hf n x]
    have hI : ∫ x, S.indicator (fun _ => (1 : ℝ)) x * ℓ x = ∫ x in S, ℓ' x := by
      rw [← integral_indicator hS]
      refine integral_congr_ae (hℓ'.mono fun x hx => ?_)
      by_cases hx' : x ∈ S <;> simp [hx', hx]
    rw [hI] at hge
    have hint : IntegrableOn ℓ' S := by
      have := remark_4_4.integrable_mul_conj hr (h.2.1.ae_eq hℓ') hg
      refine (this.integrableOn (s := S)).congr_fun (fun x hx => by simp [hx]) hS
    have hneg : ∫ x in S, ℓ' x ≤ 0 := setIntegral_nonpos hS fun x hx => hx.1.le
    have h0 : ∫ x in S, (-ℓ' x) = 0 := by rw [integral_neg]; linarith
    have hpos := (setIntegral_eq_zero_iff_of_nonneg_ae (f := fun x => -ℓ' x)
      ((ae_restrict_mem hS).mono fun x hx => by simpa using hx.1.le) hint.neg).1 h0
    rw [EventuallyEq, ae_restrict_iff' hS] at hpos
    refine measure_eq_zero_iff_ae_notMem.2 (hpos.mono fun x hx hxS => ?_)
    have := hx hxS
    have h2 := hxS.1
    simp only [Pi.zero_apply, neg_eq_zero, mem_ofPred_eq] at this h2
    linarith
  have hU : volume {x | ℓ' x < 0} = 0 := by
    have : {x | ℓ' x < 0} = ⋃ k : ℕ, ({x | ℓ' x < 0} ∩ Metric.ball (0 : Rd d) k) := by
      ext x; simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      exact ⟨fun hx => ⟨_, hx, (exists_nat_gt ‖x‖).choose_spec⟩, fun ⟨_, hx, _⟩ => hx⟩
    rw [this]; exact measure_iUnion_null hk
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hU, hℓ'] with x hx hxe
  simp only [not_lt] at hx
  simpa [hxe] using hx

/-- **Subgoal** (Remark 4.5, positive part): a weak `L^r` limit `ℓ`, `1 < r`, of nonnegative
functions is also the weak limit as `ℓ⁺ = max ℓ 0`. -/
theorem remark_4_5.weakLpTendsto_posPart {d : ℕ} {r : ℝ≥0∞} (hr : 1 < r)
    {f : ℕ → Rd d → ℝ} {ℓ : Rd d → ℝ} (hf : ∀ n x, 0 ≤ f n x) (h : WeakLpTendsto r f ℓ) :
    WeakLpTendsto r f (fun x => max (ℓ x) 0) :=
  remark_4_5.weakLpTendsto_congr (fun _ => EventuallyEq.rfl)
    ((remark_4_5.ae_nonneg_of_weakLpTendsto hr hf h).mono fun _x hx => (max_eq_left hx).symm) h

/-- **Remark 4.5** (convergence and seminorm). For `d = 1`, if for some `r ∈ (1, ∞]` both
discrete local-time sequences converge to the same terminal local time,
`λ^{n,±}_T ⇀ ℓ_T` in `L^r(ℝ)`, then `𝓛^{π_n}_ω ⇀ ℓ_T` in `L^r(ℝ)` and
`‖h‖_{W^0_{ω,π}} = ∫ |h(u)| ℓ_T(u) du` for `h ∈ L^{r'}(ℝ)`. -/
theorem remark_4_5_seminorm (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd 1 → ℝ}
    (hplus : WeakLpTendsto r
      (fun n v => discreteLocalTime (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    (hminus : WeakLpTendsto r
      (fun n v => discreteLocalTime.reversed (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ) :
    WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ ∧
      ∀ (h : Rd 1 → Rd 1 →L[ℝ] Rd 1), MemLp h r.conjExponent →
        occupationSeminorm π ω h = ∫⁻ v, ‖h v‖ₑ * ENNReal.ofReal (ℓ v) := by
  have hweak : WeakLpTendsto r (fun n => discreteOccupationDensity (π n) ω) ℓ :=
    remark_4_5.weakLpTendsto_congr (fun n => (remark_4_5_identity (π n) ω).symm) EventuallyEq.rfl
      (remark_4_5.weakLpTendsto_half_add hr hplus hminus)
  refine ⟨hweak, fun h hh => ?_⟩
  have hL0 : ∀ n x, 0 ≤ discreteOccupationDensity (π n) ω x := fun n x =>
    Finset.sum_nonneg fun i _ => discreteOccupationDensity.piece_nonneg _ _ _
  rw [remark_4_4_seminorm hω hQV hosc hr (fun x => le_max_right (ℓ x) 0)
    (remark_4_5.weakLpTendsto_posPart hr hL0 hweak) hh]
  refine lintegral_congr fun v => ?_
  congr 1
  rcases le_total 0 (ℓ v) with h0 | h0
  · rw [max_eq_left h0]
  · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]

/-- **Remark 4.5** (inclusion). Under the hypotheses of `remark_4_5_seminorm`,
`{F ∈ W^{2,1}(ℝ) : F'' ∈ L^{r'}(ℝ)} ⊆ 𝓦^2_{ω,π}`; `F` is taken to be its continuous
representative (`W^{2,1}(ℝ) ⊂ C^1(ℝ)`), which is what makes the trace condition automatic. -/
theorem remark_4_5_subset (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {r : ℝ≥0∞} (hr : 1 < r) {ℓ : Rd 1 → ℝ}
    (hplus : WeakLpTendsto r
      (fun n v => discreteLocalTime (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    (hminus : WeakLpTendsto r
      (fun n v => discreteLocalTime.reversed (π n) (fun t => Rd.coord 0 (ω t)) (Rd.coord 0 v)) ℓ)
    {F : Rd 1 → ℝ} (hF : MemW 2 1 F) (hFc : Continuous F) {H : Rd 1 → (Rd 1 →L[ℝ] Rd 1)}
    (hH : IsWeakHessian F H) (hHr : MemLp H r.conjExponent) :
    F ∈ PathwiseSobolevSpace π ω := by
  have hL0 : ∀ n x, 0 ≤ discreteOccupationDensity (π n) ω x := fun n x =>
    Finset.sum_nonneg fun i _ => discreteOccupationDensity.piece_nonneg _ _ _
  exact remark_4_4 hω hQV hosc hr (fun x => le_max_right (ℓ x) 0)
    (remark_4_5.weakLpTendsto_posPart hr hL0
      (remark_4_5_seminorm hω hQV hosc hr hplus hminus).1) hF hFc hH hHr

/-- **Subgoal** (Remark 4.5 bounded case, `L^∞` norm by duality): if `∫_s |f| ≤ C |s|` for every
measurable `s` of finite measure, then `‖f‖_∞ ≤ C`. -/
theorem remark_4_5.eLpNorm_top_le_of_setIntegral_abs_le {d : ℕ} {f : Rd d → ℝ}
    (hf : MemLp f ⊤) {C : ℝ}
    (h : ∀ s, MeasurableSet s → volume s < ∞ → ∫ x in s, |f x| ≤ C * volume.real s) :
    eLpNorm f ⊤ volume ≤ ENNReal.ofReal C := by
  have hint : ∀ s, MeasurableSet s → volume s < ∞ → IntegrableOn (fun x => |f x|) s := by
    intro s _ hs
    have : Fact (volume s < ∞) := ⟨hs⟩
    exact (hf.restrict s).norm.integrable le_top
  have hae : 0 ≤ᵐ[volume] fun x => C - |f x| := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hst => ?_)
      (fun s hs hst => ?_)
    · exact (integrableOn_const hst.ne).sub (hint s hs hst)
    · rw [integral_sub (integrableOn_const hst.ne) (hint s hs hst), setIntegral_const,
        smul_eq_mul, sub_nonneg, mul_comm]
      exact h s hs hst
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound (hae.mono fun x hx => ?_)
  simp only [Pi.zero_apply, sub_nonneg] at hx
  simpa [Real.norm_eq_abs] using hx

/-- **Remark 4.5** (bounded local-time case). For `d = 1`, if `𝓛^{π_n}_ω →* ℓ_T` weakly-* in
`L^∞(ℝ)`, then `sup_n ‖𝓛^{π_n}_ω‖_{L^∞} < ∞` (Banach–Steinhaus) and `𝓦^2_{ω,π} = W^{2,1}(ℝ)`
(for continuous representatives). -/
theorem remark_4_5_bounded (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {ℓ : Rd 1 → ℝ}
    (hweak : WeakLpTendsto ⊤ (fun n => discreteOccupationDensity (π n) ω) ℓ) :
    (∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n, 1 ≤ n →
        eLpNorm (discreteOccupationDensity (π n) ω) ⊤ volume ≤ K) ∧
      ∀ F : Rd 1 → ℝ, Continuous F → (F ∈ PathwiseSobolevSpace π ω ↔ MemW 2 1 F) := by
  sorry

/-- **Remark 4.5** (comparison with Davis–Obłój–Siorpaes). For `d = 1`, if a local time
`(ℓ_t)_{t ∈ [0,T]}` exists in the sense of [DOS18] and the DOS change-of-variable formula
`F(ω(t)) - F(ω(0)) = ∫_0^t F'(ω(s)) d^π ω(s) + ½ ∫ ℓ_t(u) F''(u) du` applies to the same `F`,
with the same pathwise integral (eq. (16)), then
`[F'(ω), ω]_π(t) = ∫ ℓ_t(u) F''(u) du` for `t ∈ [0, T]`. -/
theorem remark_4_5_local_time (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {F : Rd 1 → ℝ} (hF : MemW 2 1 F)
    {H : Rd 1 → (Rd 1 →L[ℝ] Rd 1)} (hH : IsWeakHessian F H) (A : ApproximatingSequence π ω F H)
    (ℓ : ℝ → Rd 1 → ℝ)
    (hDOS : ∀ t ∈ Icc 0 T, F (ω t) - F (ω 0) = weakPathwiseIntegral A t +
      1 / 2 * ∫ v, ℓ t v * Rd.coord 0 (H v (Rd.basisVec 0))) :
    ∀ t ∈ Icc 0 T, weakCovariation A t = ∫ v, ℓ t v * Rd.coord 0 (H v (Rd.basisVec 0)) := by
  intro t ht
  have h51 := theorem_5_1 hω hQV hosc hF hH A t ht
  have hd := hDOS t ht
  linarith

end WeakPathwiseIto
