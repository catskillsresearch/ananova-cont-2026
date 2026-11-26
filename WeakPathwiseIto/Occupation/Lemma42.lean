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

open scoped Classical in
/-- **Subgoal** (Lemma 4.2 proof, `tendsto_riemannStieltjes` grid step a: discrete sums): for
points `r_i ∈ (0, T]` with weights `w_i ≥ 0` and the grid `s_k = kT/K`, if `g` varies by at
most `η` on `[0,T]` over distances `≤ T/K`, then
`|∑_i g(r_i) w_i - ∑_{k<K} g(s_{k+1}) (W(s_{k+1}) - W(s_k))| ≤ η ∑_i w_i`, where
`W(s) = ∑_{r_i ≤ s} w_i`. -/
theorem abs_sum_sub_grid_le {ι : Type*} [Fintype ι] {r w : ι → ℝ} (hr : ∀ i, r i ∈ Ioc 0 T)
    (hw : ∀ i, 0 ≤ w i) {K : ℕ} (hK : 0 < K) {g : ℝ → ℝ} {η : ℝ}
    (hη : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| ≤ T / K → |g x - g y| ≤ η) :
    |∑ i, g (r i) * w i - ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * T / K) *
        (∑ i ∈ Finset.univ.filter (fun i => r i ≤ (k + 1 : ℕ) * T / K), w i -
          ∑ i ∈ Finset.univ.filter (fun i => r i ≤ (k : ℕ) * T / K), w i)| ≤
      η * ∑ i, w i := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · simp
  have hT : 0 ≤ T := ((hr i0).1.trans_le (hr i0).2).le
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k : ℕ, s k = (k : ℝ) * T / K := ⟨_, fun _ => rfl⟩
  simp_rw [← hs]
  have hsmono : ∀ k, s k ≤ s (k + 1) := fun k => by
    rw [hs, hs]; push_cast
    exact div_le_div_of_nonneg_right (by nlinarith) hK'.le
  have hsK : s K = T := by rw [hs]; field_simp
  have hs0 : s 0 = 0 := by rw [hs]; simp
  have hstep : ∀ k, s (k + 1) - s k = T / K := fun k => by rw [hs, hs]; push_cast; ring
  have hsnn : ∀ k, 0 ≤ s k := fun k => by rw [hs]; positivity
  have hsle : ∀ k < K, s (k + 1) ≤ T := fun k hk => by
    rw [hs, div_le_iff₀ hK']
    have : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
    nlinarith
  set c : ℕ → ι → ℝ := fun k i =>
    (if r i ≤ s (k + 1) then 1 else 0) - (if r i ≤ s k then 1 else 0) with hc
  have hsum_c : ∀ i, ∑ k ∈ Finset.range K, c k i = 1 := fun i => by
    simp only [hc]
    rw [Finset.sum_range_sub (fun k => if r i ≤ s k then (1 : ℝ) else 0), hsK, hs0,
      if_pos (hr i).2, if_neg (not_le.2 (hr i).1)]
    norm_num
  have hW : ∀ k, ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s (k + 1)), w i -
      ∑ i ∈ Finset.univ.filter (fun i => r i ≤ s k), w i = ∑ i, c k i * w i := fun k => by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc]
    split_ifs <;> ring
  simp_rw [hW]
  have h1 : ∀ i, g (r i) * w i = ∑ k ∈ Finset.range K, c k i * g (r i) * w i := fun i => by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_c, one_mul]
  have key : ∑ i, g (r i) * w i - ∑ k ∈ Finset.range K, g (s (k + 1)) * ∑ i, c k i * w i =
      ∑ i, ∑ k ∈ Finset.range K, c k i * (g (r i) - g (s (k + 1))) * w i := by
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range K), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hterm : ∀ i, ∀ k ∈ Finset.range K,
      |c k i * (g (r i) - g (s (k + 1))) * w i| ≤ c k i * η * w i := by
    intro i k hk
    have hkK := Finset.mem_range.1 hk
    have hw0 := hw i
    by_cases h1 : r i ≤ s (k + 1) <;> by_cases h2 : r i ≤ s k
    · simp [hc, h1, h2]
    · have hcv : c k i = 1 := by simp [hc, h1, h2]
      rw [hcv, one_mul, one_mul, abs_mul, abs_of_nonneg hw0]
      refine mul_le_mul_of_nonneg_right (hη _ ⟨(hr i).1.le, (hr i).2⟩ _
        ⟨hsnn _, hsle k hkK⟩ ?_) hw0
      rw [abs_sub_comm, abs_of_nonneg (by linarith), ← hstep k]
      linarith [not_le.1 h2]
    · exact absurd (h2.trans (hsmono k)) h1
    · simp [hc, h1, h2]
  rw [key]
  calc |∑ i, ∑ k ∈ Finset.range K, c k i * (g (r i) - g (s (k + 1))) * w i|
      ≤ ∑ i, ∑ k ∈ Finset.range K, |c k i * (g (r i) - g (s (k + 1))) * w i| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ k ∈ Finset.range K, c k i * η * w i :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k hk => hterm i k hk
    _ = η * ∑ i, w i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_c]
        ring

/-- **Subgoal** (Lemma 4.2 proof, `tendsto_riemannStieltjes` grid step b: the Stieltjes
integral): with the grid `s_k = kT/K` and `g` continuous on `[0,T]` varying by at most `η`
over distances `≤ T/K`, `|∫_{[0,T]} g d tr[ω]_π - ∑_{k<K} g(s_{k+1}) (tr(s_{k+1}) - tr(s_k))|
≤ η (tr(T) - tr(0))`. -/
theorem abs_integral_sub_grid_le (hQV : HasQuadraticVariation π ω) {K : ℕ} (hK : 0 < K)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T)) {η : ℝ}
    (hη : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| ≤ T / K → |g x - g y| ≤ η) :
    |(∫ t in Icc 0 T, g t ∂hQV.traceMeasure) - ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * T / K) *
        (hQV.trace ((k + 1 : ℕ) * T / K) - hQV.trace ((k : ℕ) * T / K))| ≤
      η * (hQV.trace T - hQV.trace 0) := by
  have hT : 0 ≤ T := (π 0).nonneg
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k : ℕ, s k = (k : ℝ) * T / K := ⟨_, fun _ => rfl⟩
  simp_rw [← hs]
  have hsmono : ∀ k, s k ≤ s (k + 1) := fun k => by
    rw [hs, hs]; push_cast
    exact div_le_div_of_nonneg_right (by nlinarith) hK'.le
  have hsK : s K = T := by rw [hs]; field_simp
  have hs0 : s 0 = 0 := by rw [hs]; simp
  have hsnn : ∀ k, 0 ≤ s k := fun k => by rw [hs]; positivity
  have hsle : ∀ k < K, s (k + 1) ≤ T := fun k hk => by
    rw [hs, div_le_iff₀ hK']
    have : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
    nlinarith
  have hstep : ∀ k, s (k + 1) - s k = T / K := fun k => by rw [hs, hs]; push_cast; ring
  haveI : IsLocallyFiniteMeasure hQV.traceMeasure := by
    unfold HasQuadraticVariation.traceMeasure; infer_instance
  have hInt : IntegrableOn g (Icc 0 T) hQV.traceMeasure := hg.integrableOn_compact isCompact_Icc
  have hcell : ∀ k < K, Ioc (s k) (s (k + 1)) ⊆ Icc 0 T := fun k hk x hx =>
    ⟨(hsnn k).trans hx.1.le, hx.2.trans (hsle k hk)⟩
  have hfin : ∀ k < K, hQV.traceMeasure (Ioc (s k) (s (k + 1))) < ⊤ := fun k hk =>
    (measure_mono (hcell k hk)).trans_lt isCompact_Icc.measure_lt_top
  have h0 : hQV.traceMeasure {0} = 0 := (traceMeasure_Ioc hQV le_rfl le_rfl hT).2
  have hIcc : ∫ t in Icc 0 T, g t ∂hQV.traceMeasure = ∫ t in Ioc 0 T, g t ∂hQV.traceMeasure := by
    refine setIntegral_congr_set (ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) h0, ?_⟩)
    · simp only [mem_diff, mem_Icc, mem_Ioc, not_and] at hx
      exact Set.mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h => hx.2 h hx.1.2) hx.1.1)
    · rw [sdiff_eq_empty.2 Ioc_subset_Icc_self, measure_empty]
  have hsplit : ∫ t in Ioc 0 T, g t ∂hQV.traceMeasure =
      ∑ k ∈ Finset.range K, ∫ t in Ioc (s k) (s (k + 1)), g t ∂hQV.traceMeasure := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := hQV.traceMeasure)
      (a := s) (n := K) fun k hk =>
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (hsmono k)).2 (hInt.mono_set (hcell k hk))
    rw [hs0, hsK, intervalIntegral.integral_of_le hT] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_of_le (hsmono k)
  have hsum : ∀ k ∈ Finset.range K, g (s (k + 1)) * (hQV.trace (s (k + 1)) - hQV.trace (s k)) =
      ∫ t in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂hQV.traceMeasure := fun k hk => by
    rw [setIntegral_const, smul_eq_mul, mul_comm,
      (traceMeasure_Ioc hQV (hsnn k) (hsmono k) (hsle k (Finset.mem_range.1 hk))).1]
  rw [hIcc, hsplit, Finset.sum_congr rfl hsum, ← Finset.sum_sub_distrib]
  have hcellb : ∀ k ∈ Finset.range K, |(∫ t in Ioc (s k) (s (k + 1)), g t ∂hQV.traceMeasure) -
      ∫ t in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂hQV.traceMeasure| ≤
        η * (hQV.trace (s (k + 1)) - hQV.trace (s k)) := fun k hk => by
    have hk' := Finset.mem_range.1 hk
    rw [← integral_sub (hInt.mono_set (hcell k hk')) (integrableOn_const (hfin k hk').ne),
      ← (traceMeasure_Ioc hQV (hsnn k) (hsmono k) (hsle k hk')).1, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (hfin k hk') fun x hx => ?_
    rw [Real.norm_eq_abs]
    refine hη _ (hcell k hk' hx) _ ⟨hsnn _, hsle k hk'⟩ ?_
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2]), ← hstep k]
    linarith [hx.1]
  calc _ ≤ ∑ k ∈ Finset.range K, |(∫ t in Ioc (s k) (s (k + 1)), g t ∂hQV.traceMeasure) -
        ∫ t in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂hQV.traceMeasure| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, η * (hQV.trace (s (k + 1)) - hQV.trace (s k)) :=
        Finset.sum_le_sum hcellb
    _ = η * (hQV.trace T - hQV.trace 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => hQV.trace (s k)), hsK, hs0]

/-- **Subgoal** (Lemma 4.2 proof: Riemann–Stieltjes convergence): for `g` continuous on `[0, T]`,
`∑_i g(t_{i+1}) |ω(t_{i+1}) - ω(t_i)|² → ∫_{[0,T]} g d tr[ω]_π` (weak convergence of the
discrete quadratic-variation measures, from pointwise convergence of their distribution
functions to the continuous `tr[ω]_π`). -/
theorem tendsto_riemannStieltjes (hQV : HasQuadraticVariation π ω) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) :
    Tendsto (fun n => ∑ i, g ((π n).right i) * ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)
      atTop (𝓝 (∫ t in Icc 0 T, g t ∂hQV.traceMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hT : 0 ≤ T := (π 0).nonneg
  obtain ⟨B, hB, hB1, hB2⟩ : ∃ B : ℝ, 0 < B ∧ hQV.trace T + 1 ≤ B ∧
      hQV.trace T - hQV.trace 0 ≤ B :=
    ⟨|hQV.trace T| + 1 + |hQV.trace T - hQV.trace 0|, by positivity,
      by linarith [le_abs_self (hQV.trace T), abs_nonneg (hQV.trace T - hQV.trace 0)],
      by linarith [le_abs_self (hQV.trace T - hQV.trace 0), abs_nonneg (hQV.trace T)]⟩
  obtain ⟨η, hη, hηB⟩ : ∃ η : ℝ, 0 < η ∧ η * B = ε / 4 :=
    ⟨ε / 4 / B, by positivity, by field_simp⟩
  obtain ⟨δ, hδ, hgδ⟩ :=
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (T / δ)
  have hKr : (0 : ℝ) < K := (div_nonneg hT hδ.le).trans_lt hK
  have hK0 : 0 < K := by exact_mod_cast hKr
  have hTK : T / K < δ := by
    rw [div_lt_iff₀ hKr]
    have := (div_lt_iff₀ hδ).1 hK
    linarith
  have hη' : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| ≤ T / K → |g x - g y| ≤ η :=
    fun x hx y hy hxy => by
      have := hgδ x hx y hy (by rw [Real.dist_eq]; exact hxy.trans_lt hTK)
      rw [Real.dist_eq] at this
      exact this.le
  have hmem : ∀ j : ℕ, j ≤ K → (j : ℝ) * T / K ∈ Icc 0 T := fun j hj => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hKr]
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith
  have hgridlim := tendsto_finset_sum (Finset.range K) fun k hk =>
    ((tendsto_discreteTrace hQV (hmem (k + 1) (Finset.mem_range.1 hk))).sub
      (tendsto_discreteTrace hQV (hmem k (Finset.mem_range.1 hk).le))).const_mul
        (g ((k + 1 : ℕ) * T / K))
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hgridlim (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 ((tendsto_sum_sq hQV).eventually
    (gt_mem_nhds (show hQV.trace T < hQV.trace T + 1 by linarith)))
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := abs_sum_sub_grid_le (r := (π n).right)
    (w := fun i => ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)
    (fun i => ⟨((π n).t_mem i.castSucc).1.trans_lt ((π n).left_lt_right i),
      ((π n).t_mem i.succ).2⟩) (fun i => by positivity) hK0 hη'
  have e2 := abs_integral_sub_grid_le hQV hK0 hg hη'
  have e3 := hN1 n (le_of_max_le_left hn)
  rw [Real.dist_eq] at e3
  have e4 := hN2 n (le_of_max_le_right hn)
  have hS0 : 0 ≤ ∑ i, ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have h5 : η * ∑ i, ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 ≤ ε / 4 := by
    rw [← hηB]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
  have h6 : η * (hQV.trace T - hQV.trace 0) ≤ ε / 4 := by
    rw [← hηB]; exact mul_le_mul_of_nonneg_left hB2 hη.le
  rw [Real.dist_eq]
  rw [abs_sub_comm] at e2
  have t1 := abs_sub_le (∑ i, g ((π n).right i) * ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)
    (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * T / K) *
      (∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ (k + 1 : ℕ) * T / K),
        ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 -
       ∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ (k : ℕ) * T / K),
        ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2))
    (∫ t in Icc 0 T, g t ∂hQV.traceMeasure)
  have t2 := abs_sub_le (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * T / K) *
      (∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ (k + 1 : ℕ) * T / K),
        ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2 -
       ∑ i ∈ Finset.univ.filter (fun i => (π n).right i ≤ (k : ℕ) * T / K),
        ‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2))
    (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * T / K) *
      (hQV.trace ((k + 1 : ℕ) * T / K) - hQV.trace ((k : ℕ) * T / K)))
    (∫ t in Icc 0 T, g t ∂hQV.traceMeasure)
  linarith

/-- **Subgoal** (Lemma 4.2 proof, first display): if `|φ(x) - φ(y)| ≤ ε` whenever
`|x - y| ≤ osc(ω, π_n)`, then
`|∫ φ 𝓛^{π_n}_ω - ∑_i φ(ω(t_i)) |ω(t_{i+1}) - ω(t_i)|²| ≤ ε ∑_i |ω(t_{i+1}) - ω(t_i)|²`. -/
theorem abs_integral_sub_le (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hmod : ∀ x y, ‖x - y‖ ≤ pathOscillation ω p → |φ x - φ y| ≤ ε) :
    |(∫ x, φ x * discreteOccupationDensity p ω x) -
        ∑ i, φ (ω (p.left i)) * ‖ω (p.right i) - ω (p.left i)‖ ^ 2| ≤
      ε * ∑ i, ‖ω (p.right i) - ω (p.left i)‖ ^ 2 := by
  set A : Fin p.m → Rd d := fun i => ω (p.left i) with hA
  set B : Fin p.m → Rd d := fun i => ω (p.right i) with hB
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hball : ∀ i x, x ∈ incrementBall (A i) (B i) → ‖x - A i‖ ≤ ‖B i - A i‖ := by
    intro i x hx
    rw [incrementBall, Metric.mem_closedBall] at hx
    have h1 := dist_triangle x (midpoint ℝ (A i) (B i)) (A i)
    rw [dist_midpoint_left (𝕜 := ℝ)] at h1
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (B i)]
    have h2 : ‖(2 : ℝ)‖⁻¹ * dist (A i) (B i) = dist (A i) (B i) / 2 := by
      rw [Real.norm_two]; ring
    linarith
  have hP : ∀ i x, |(φ x - φ (A i)) * discreteOccupationDensity.piece (A i) (B i) x| ≤
      ε * discreteOccupationDensity.piece (A i) (B i) x := by
    intro i x
    have hP0 := discreteOccupationDensity.piece_nonneg (A i) (B i) x
    rcases eq_or_ne (discreteOccupationDensity.piece (A i) (B i) x) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero, abs_zero]
    have hx : x ∈ incrementBall (A i) (B i) := by
      by_contra hx
      apply h0
      unfold discreteOccupationDensity.piece
      split_ifs
      · rfl
      · exact Set.indicator_of_notMem hx _
    rw [abs_mul, abs_of_nonneg hP0]
    exact mul_le_mul_of_nonneg_right
      (hmod x (A i) ((hball i x hx).trans (norm_increment_le hω p i))) hP0
  have hint : ∀ i, Integrable (fun x => φ x * discreteOccupationDensity.piece (A i) (B i) x) :=
    fun i => (discreteOccupationDensity.integrable_piece _ _).bdd_mul hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have e1 : (∫ x, φ x * discreteOccupationDensity p ω x) =
      ∑ i, ∫ x, φ x * discreteOccupationDensity.piece (A i) (B i) x := by
    unfold discreteOccupationDensity
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum _ fun i _ => hint i
  have e2 : ∀ i, φ (A i) * ‖B i - A i‖ ^ 2 =
      ∫ x, φ (A i) * discreteOccupationDensity.piece (A i) (B i) x := fun i => by
    rw [integral_const_mul, discreteOccupationDensity.integral_piece]
  have e3 : ∀ i, (∫ x, φ x * discreteOccupationDensity.piece (A i) (B i) x) -
      ∫ x, φ (A i) * discreteOccupationDensity.piece (A i) (B i) x =
      ∫ x, (φ x - φ (A i)) * discreteOccupationDensity.piece (A i) (B i) x := fun i => by
    rw [← integral_sub (hint i) ((discreteOccupationDensity.integrable_piece _ _).const_mul _)]
    congr 1
    funext x
    ring
  have hbound : ∀ i, |∫ x, (φ x - φ (A i)) * discreteOccupationDensity.piece (A i) (B i) x| ≤
      ε * ‖B i - A i‖ ^ 2 := fun i => by
    rw [← Real.norm_eq_abs, ← discreteOccupationDensity.integral_piece, ← integral_const_mul]
    exact norm_integral_le_of_norm_le
      ((discreteOccupationDensity.integrable_piece _ _).const_mul ε)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hP i x)
  show |(∫ x, φ x * discreteOccupationDensity p ω x) - ∑ i, φ (A i) * ‖B i - A i‖ ^ 2| ≤
    ε * ∑ i, ‖B i - A i‖ ^ 2
  rw [e1, Finset.sum_congr rfl fun i _ => e2 i, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => e3 i, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hbound i)

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
