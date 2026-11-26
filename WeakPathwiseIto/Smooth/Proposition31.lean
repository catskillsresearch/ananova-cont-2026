/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Smooth.PathwiseCovariation
public import WeakPathwiseIto.Occupation.Lemma42

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace proposition_3_1

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T}

/-- **Subgoal** (Proposition 3.1 proof: Stieltjes measure of an interval): for `0 ≤ a ≤ b ≤ T`,
`d[x]_π((a, b]) = [x]_π(b) - [x]_π(a)`. -/
theorem stieltjesMeasure_Ioc {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    h.stieltjesMeasure.real (Ioc a b) = h.qv b - h.qv a := by
  have hT : 0 ≤ T := (π 0).nonneg
  have hc : Continuous h.qvExt := by
    unfold HasScalarQuadraticVariation.qvExt
    exact h.continuousOn.comp_continuous
      (by fun_prop : Continuous fun t : ℝ => max 0 (min t T))
      (fun t => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩)
  set F := h.qvExt_monotone.stieltjesFunction with hFdef
  have hF : ∀ y, F y = h.qvExt y := fun y => by
    rw [hFdef, Monotone.stieltjesFunction_eq]
    exact (h.qvExt_monotone.continuousWithinAt_Ioi_iff_rightLim_eq).1 hc.continuousWithinAt
  have hclamp : ∀ s ∈ Icc 0 T, h.qvExt s = h.qv s := fun s hs => by
    unfold HasScalarQuadraticVariation.qvExt
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hmeas : h.stieltjesMeasure = F.measure := rfl
  rw [Measure.real_def, hmeas, StieltjesFunction.measure_Ioc, hF, hF,
    ENNReal.toReal_ofReal (sub_nonneg.2 (h.qvExt_monotone hab)),
    hclamp b ⟨ha.trans hab, hb⟩, hclamp a ⟨ha, hab.trans hb⟩]

/-- **Subgoal** (Proposition 3.1 proof, convergence of `I_1^n`, grid step): with the grid
`s_k = k t / K` and `g` continuous on `[0,T]` varying by at most `η` over distances `≤ t/K` in
`[0,t]`, `|∫_0^t g d[x]_π - ∑_{k<K} g(s_{k+1}) ([x](s_{k+1}) - [x](s_k))| ≤ η ([x](t) - [x](0))`. -/
theorem abs_integral_sub_grid_le {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {t : ℝ}
    (ht : t ∈ Icc 0 T) {K : ℕ} (hK : 0 < K) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T)) {η : ℝ}
    (hη : ∀ y ∈ Icc 0 t, ∀ z ∈ Icc 0 t, |y - z| ≤ t / K → |g y - g z| ≤ η) :
    |h.integral g t - ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
        (h.qv ((k + 1 : ℕ) * t / K) - h.qv ((k : ℕ) * t / K))| ≤ η * (h.qv t - h.qv 0) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k : ℕ, s k = (k : ℝ) * t / K := ⟨_, fun _ => rfl⟩
  simp_rw [← hs]
  have hsmono : ∀ k, s k ≤ s (k + 1) := fun k => by
    rw [hs, hs]; push_cast
    exact div_le_div_of_nonneg_right (by nlinarith [ht.1]) hK'.le
  have hsK : s K = t := by rw [hs]; field_simp
  have hs0 : s 0 = 0 := by rw [hs]; simp
  have hsnn : ∀ k, 0 ≤ s k := fun k => by rw [hs]; have := ht.1; positivity
  have hsle : ∀ k < K, s (k + 1) ≤ t := fun k hk => by
    rw [hs, div_le_iff₀ hK']
    have : ((k + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hk
    nlinarith [ht.1]
  have hstep : ∀ k, s (k + 1) - s k = t / K := fun k => by rw [hs, hs]; push_cast; ring
  haveI : IsLocallyFiniteMeasure h.stieltjesMeasure := by
    unfold HasScalarQuadraticVariation.stieltjesMeasure; infer_instance
  have hInt : IntegrableOn g (Icc 0 T) h.stieltjesMeasure := hg.integrableOn_compact isCompact_Icc
  have hcell : ∀ k < K, Ioc (s k) (s (k + 1)) ⊆ Icc 0 t := fun k hk y hy =>
    ⟨(hsnn k).trans hy.1.le, hy.2.trans (hsle k hk)⟩
  have hcellT : ∀ k < K, Ioc (s k) (s (k + 1)) ⊆ Icc 0 T := fun k hk =>
    (hcell k hk).trans (Icc_subset_Icc le_rfl ht.2)
  have hfin : ∀ k < K, h.stieltjesMeasure (Ioc (s k) (s (k + 1))) < ⊤ := fun k hk =>
    (measure_mono (hcellT k hk)).trans_lt isCompact_Icc.measure_lt_top
  have hsplit : h.integral g t =
      ∑ k ∈ Finset.range K, ∫ u in Ioc (s k) (s (k + 1)), g u ∂h.stieltjesMeasure := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := h.stieltjesMeasure)
      (a := s) (n := K) fun k hk =>
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (hsmono k)).2 (hInt.mono_set (hcellT k hk))
    rw [hs0, hsK, intervalIntegral.integral_of_le ht.1] at this
    rw [HasScalarQuadraticVariation.integral, ← this]
    exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_of_le (hsmono k)
  have hIoc : ∀ k < K, h.stieltjesMeasure.real (Ioc (s k) (s (k + 1))) = h.qv (s (k + 1)) - h.qv (s k) :=
    fun k hk => stieltjesMeasure_Ioc h (hsnn k) (hsmono k) ((hsle k hk).trans ht.2)
  have hsum : ∀ k ∈ Finset.range K, g (s (k + 1)) * (h.qv (s (k + 1)) - h.qv (s k)) =
      ∫ u in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂h.stieltjesMeasure := fun k hk => by
    rw [setIntegral_const, smul_eq_mul, mul_comm, hIoc k (Finset.mem_range.1 hk)]
  rw [hsplit, Finset.sum_congr rfl hsum, ← Finset.sum_sub_distrib]
  have hcellb : ∀ k ∈ Finset.range K, |(∫ u in Ioc (s k) (s (k + 1)), g u ∂h.stieltjesMeasure) -
      ∫ u in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂h.stieltjesMeasure| ≤
        η * (h.qv (s (k + 1)) - h.qv (s k)) := fun k hk => by
    have hk' := Finset.mem_range.1 hk
    rw [← integral_sub (hInt.mono_set (hcellT k hk')) (integrableOn_const (hfin k hk').ne),
      ← hIoc k hk', ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (hfin k hk') fun y hy => ?_
    rw [Real.norm_eq_abs]
    refine hη _ (hcell k hk' hy) _ ⟨hsnn _, hsle k hk'⟩ ?_
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.2]), ← hstep k]
    linarith [hy.1]
  calc _ ≤ ∑ k ∈ Finset.range K, |(∫ u in Ioc (s k) (s (k + 1)), g u ∂h.stieltjesMeasure) -
        ∫ u in Ioc (s k) (s (k + 1)), g (s (k + 1)) ∂h.stieltjesMeasure| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, η * (h.qv (s (k + 1)) - h.qv (s k)) :=
        Finset.sum_le_sum hcellb
    _ = η * (h.qv t - h.qv 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => h.qv (s k)), hsK, hs0]

/-- **Subgoal** (Proposition 3.1 proof, convergence of `I_1^n`, [CF10]): for `g` continuous on
`[0,T]` and `t ∈ [0,T]`, `∑_{t_{k+1} ≤ t} g(t_{k+1}) (x(t_{k+1}) - x(t_k))² → ∫_0^t g d[x]_π`
(weak convergence of the discrete quadratic-variation measures). -/
theorem tendsto_riemannStieltjes {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      g ((π n).right k) * (x ((π n).right k) - x ((π n).left k)) ^ 2)
      atTop (𝓝 (h.integral g t)) := by
  have hT : 0 ≤ T := (π 0).nonneg
  have hpos : ∀ n (k : Fin (π n).m), 0 < (π n).right k := fun n k =>
    ((π n).t_mem k.castSucc).1.trans_lt ((π n).left_lt_right k)
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0
    have : ∀ n, (∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ 0),
        g ((π n).right k) * (x ((π n).right k) - x ((π n).left k)) ^ 2) = 0 := fun n => by
      rw [Finset.filter_false_of_mem fun k _ => not_le.2 (hpos n k), Finset.sum_empty]
    simp only [this, HasScalarQuadraticVariation.integral, Ioc_self, Measure.restrict_empty,
      integral_zero_measure]
    exact tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB, hB1, hB2⟩ : ∃ B : ℝ, 0 < B ∧ h.qv t + 1 ≤ B ∧ h.qv t - h.qv 0 ≤ B :=
    ⟨|h.qv t| + 1 + |h.qv t - h.qv 0|, by positivity,
      by linarith [le_abs_self (h.qv t), abs_nonneg (h.qv t - h.qv 0)],
      by linarith [le_abs_self (h.qv t - h.qv 0), abs_nonneg (h.qv t)]⟩
  obtain ⟨η, hη, hηB⟩ : ∃ η : ℝ, 0 < η ∧ η * B = ε / 4 :=
    ⟨ε / 4 / B, by positivity, by field_simp⟩
  obtain ⟨δ, hδ, hgδ⟩ :=
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (t / δ)
  have hKr : (0 : ℝ) < K := (div_nonneg ht.1 hδ.le).trans_lt hK
  have hK0 : 0 < K := by exact_mod_cast hKr
  have htK : t / K < δ := by
    rw [div_lt_iff₀ hKr]
    have := (div_lt_iff₀ hδ).1 hK
    linarith
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hη' : ∀ y ∈ Icc 0 t, ∀ z ∈ Icc 0 t, |y - z| ≤ t / K → |g y - g z| ≤ η :=
    fun y hy z hz hyz => by
      have := hgδ y (hsub hy) z (hsub hz) (by rw [Real.dist_eq]; exact hyz.trans_lt htK)
      rw [Real.dist_eq] at this
      exact this.le
  have hmem : ∀ j : ℕ, j ≤ K → (j : ℝ) * t / K ∈ Icc 0 t := fun j hj => by
    refine ⟨by have := ht.1; positivity, ?_⟩
    rw [div_le_iff₀ hKr]
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith [ht.1]
  have hgridlim := tendsto_finset_sum (Finset.range K) fun k hk =>
    ((h.tendsto _ (hsub (hmem (k + 1) (Finset.mem_range.1 hk)))).sub
      (h.tendsto _ (hsub (hmem k (Finset.mem_range.1 hk).le)))).const_mul
        (g ((k + 1 : ℕ) * t / K))
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hgridlim (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 ((h.tendsto t ht).eventually
    (gt_mem_nhds (show h.qv t < h.qv t + 1 by linarith)))
  refine ⟨max N1 N2, fun n hn => ?_⟩
  set r : Fin (π n).m → ℝ := fun k => min ((π n).right k) t with hr
  set w : Fin (π n).m → ℝ := fun k =>
    if (π n).right k ≤ t then (x ((π n).right k) - x ((π n).left k)) ^ 2 else 0 with hw
  have hinner : ∀ s ≤ t, ∑ k ∈ Finset.univ.filter (fun k => r k ≤ s), w k =
      discreteQuadraticVariation (π n) x s := fun s hs => by
    unfold discreteQuadraticVariation
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : (π n).right k ≤ t
    · simp only [hr, hw, min_eq_left h1, if_pos h1]
    · have h2 : ¬ (π n).right k ≤ s := fun h' => h1 (h'.trans hs)
      simp only [hr, hw, if_neg h1, if_neg h2, ite_self]
  have hA : ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      g ((π n).right k) * (x ((π n).right k) - x ((π n).left k)) ^ 2 = ∑ k, g (r k) * w k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : (π n).right k ≤ t
    · simp only [hr, hw, min_eq_left h1, if_pos h1]
    · simp only [hw, if_neg h1, mul_zero]
  have hSw : ∑ k, w k = discreteQuadraticVariation (π n) x t := by
    rw [← hinner t le_rfl, Finset.filter_true_of_mem fun k _ => min_le_right _ _]
  have e1 := lemma_4_2.abs_sum_sub_grid_le (T := t) (r := r) (w := w)
    (fun k => ⟨lt_min (hpos n k) htpos, min_le_right _ _⟩)
    (fun k => by simp only [hw]; split_ifs <;> positivity) hK0 hη'
  have hgrid : ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
      (∑ i ∈ Finset.univ.filter (fun i => r i ≤ (k + 1 : ℕ) * t / K), w i -
        ∑ i ∈ Finset.univ.filter (fun i => r i ≤ (k : ℕ) * t / K), w i) =
      ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
        (discreteQuadraticVariation (π n) x ((k + 1 : ℕ) * t / K) -
          discreteQuadraticVariation (π n) x ((k : ℕ) * t / K)) :=
    Finset.sum_congr rfl fun k hk => by
      rw [hinner _ (hmem (k + 1) (Finset.mem_range.1 hk)).2,
        hinner _ (hmem k (Finset.mem_range.1 hk).le).2]
  rw [← hA, hSw, hgrid] at e1
  have e2 := abs_integral_sub_grid_le h ht hK0 hg hη'
  have e3 := hN1 n (le_of_max_le_left hn)
  rw [Real.dist_eq] at e3
  have e4 := hN2 n (le_of_max_le_right hn)
  have hS0 : 0 ≤ discreteQuadraticVariation (π n) x t :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h5 : η * discreteQuadraticVariation (π n) x t ≤ ε / 4 := by
    rw [← hηB]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
  have h6 : η * (h.qv t - h.qv 0) ≤ ε / 4 := by
    rw [← hηB]; exact mul_le_mul_of_nonneg_left hB2 hη.le
  rw [Real.dist_eq]
  rw [abs_sub_comm] at e2
  have t1 := abs_sub_le (∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      g ((π n).right k) * (x ((π n).right k) - x ((π n).left k)) ^ 2)
    (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
      (discreteQuadraticVariation (π n) x ((k + 1 : ℕ) * t / K) -
        discreteQuadraticVariation (π n) x ((k : ℕ) * t / K)))
    (h.integral g t)
  have t2 := abs_sub_le (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
      (discreteQuadraticVariation (π n) x ((k + 1 : ℕ) * t / K) -
        discreteQuadraticVariation (π n) x ((k : ℕ) * t / K)))
    (∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
      (h.qv ((k + 1 : ℕ) * t / K) - h.qv ((k : ℕ) * t / K)))
    (h.integral g t)
  linarith

/-- **Subgoal** (Proposition 3.1 proof, (6)): for `s ∈ [t_k, t_{k+1}]`,
`|ω(s) - ω(t_k)| ≤ osc(ω, π_n)`. -/
theorem norm_sub_left_le {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T)
    (i : Fin p.m) {s : ℝ} (hs : s ∈ Icc (p.left i) (p.right i)) :
    ‖ω s - ω (p.left i)‖ ≤ pathOscillation ω p := by
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
  unfold pathOscillation
  refine le_ciSup_of_le hbdd1 i (le_ciSup_of_le (hbdd2 i) s ?_)
  exact le_ciSup (f := fun _ : s ∈ Icc (p.left i) (p.right i) =>
    ‖ω s - ω (p.left i)‖) (Set.finite_range _).bddAbove hs

/-- **Subgoal** (Proposition 3.1 proof, Newton–Leibniz remainder `r_k^n`): if
`|∇f(z) - ∇f(y)| ≤ ε` on the segment `[x, y]`, then `|f(y) - f(x) - ∇f(y)(y - x)| ≤ ε |y - x|`. -/
theorem norm_taylor_le {f : Rd d → Rd d} (hf : Differentiable ℝ f) {x y : Rd d} {ε : ℝ}
    (hε : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ ε) :
    ‖f y - f x - fderiv ℝ f y (y - x)‖ ≤ ε * ‖y - x‖ := by
  set A := fderiv ℝ f y with hA
  have hd : ∀ z, HasFDerivAt (fun z => f z - A z) (fderiv ℝ f z - A) z := fun z =>
    (hf z).hasFDerivAt.sub A.hasFDerivAt
  have key := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (f := fun z => f z - A z) (C := ε) (fun z _ => (hd z).differentiableAt)
    (fun z hz => by rw [(hd z).fderiv]; exact hε z hz) (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)
  have e : f y - A y - (f x - A x) = f y - f x - A (y - x) := by rw [map_sub]; abel
  simpa only [e] using key

/-- **Subgoal** (Proposition 3.1 proof: splitting the discrete covariation): the stopped sum
equals the sum over complete intervals `t_{k+1} ≤ t` plus the straddling interval
`t_k < t < t_{k+1}`. -/
theorem riemannSum_eq (p : Partition T) (f : Rd d → Rd d) (ω : ℝ → Rd d) (t : ℝ) :
    pathwiseCovariation.riemannSum p f ω t =
      ∑ k ∈ Finset.univ.filter (fun k => p.right k ≤ t),
        ⟪f (ω (p.right k)) - f (ω (p.left k)), ω (p.right k) - ω (p.left k)⟫ +
      ∑ k ∈ Finset.univ.filter (fun k => p.left k < t ∧ t < p.right k),
        ⟪f (ω t) - f (ω (p.left k)), ω t - ω (p.left k)⟫ := by
  unfold pathwiseCovariation.riemannSum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlr := p.left_lt_right k
  by_cases h1 : p.right k ≤ t
  · have h2 : ¬ (p.left k < t ∧ t < p.right k) := fun h => absurd h1 (not_le.2 h.2)
    rw [if_pos h1, if_neg h2, min_eq_left h1, min_eq_left (hlr.le.trans h1), add_zero]
  · by_cases h3 : p.left k < t
    · have h2 : p.left k < t ∧ t < p.right k := ⟨h3, not_le.1 h1⟩
      rw [if_neg h1, if_pos h2, min_eq_right (not_le.1 h1).le, min_eq_left h3.le, zero_add]
    · have h2 : ¬ (p.left k < t ∧ t < p.right k) := fun h => h3 h.1
      rw [if_neg h1, if_neg h2, min_eq_right (not_le.1 h1).le, min_eq_right (not_lt.1 h3)]
      simp

/-- **Subgoal** (Proposition 3.1 proof, `⟨∇f, δω ᵗδω⟩` by polarization):
`⟨A v, v⟩ = ∑_{i,j} A_{ij} ((v_i + v_j)² - v_i² - v_j²) / 2`. -/
theorem inner_apply_eq (A : Rd d →L[ℝ] Rd d) (v : Rd d) :
    ⟪A v, v⟫ = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) *
      ((Rd.coord i v + Rd.coord j v) ^ 2 - Rd.coord i v ^ 2 - Rd.coord j v ^ 2) / 2 := by
  have hc : ∀ (i : Fin d) (u : Rd d), Rd.coord i u = u i := fun i u => by
    simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]
  have hexp : ∀ u : Rd d, u = ∑ j, Rd.coord j u • Rd.basisVec j := fun u => by
    ext i
    simp [hc, Rd.basisVec, Pi.single_apply]
  have key : ∀ u w : Rd d, ⟪A u, w⟫ = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) *
      (Rd.coord j u * Rd.coord i w) := fun u w => by
    conv_lhs => rw [hexp u, hexp w]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Rd.coord]
    ring
  rw [key v v]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Subgoal** (Proposition 3.1 proof: `I_1^n(t) → ∫_0^t ⟨∇f(ω(u)), d[ω]_π(u)⟩`). -/
theorem tendsto_main {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
        ω ((π n).right k) - ω ((π n).left k)⟫) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
  have hDf : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by norm_num)
  have hGc : ∀ i j : Fin d,
      ContinuousOn (fun u => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) (Icc 0 T) :=
    fun i j => by
      have h1 : Continuous fun A : Rd d →L[ℝ] Rd d => Rd.coord i (A (Rd.basisVec j)) := by
        unfold Rd.coord; fun_prop
      exact h1.comp_continuousOn (hDf.comp_continuousOn hω)
  have hcsub : ∀ (i : Fin d) (a b : Rd d), Rd.coord i (a - b) = Rd.coord i a - Rd.coord i b :=
    fun i a b => by simp [Rd.coord, inner_sub_left]
  have hlim : Tendsto (fun n => ∑ i, ∑ j,
      ((∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
          Rd.coord i (fderiv ℝ f (ω ((π n).right k)) (Rd.basisVec j)) *
            ((fun s => Rd.coord i (ω s) + Rd.coord j (ω s)) ((π n).right k) -
              (fun s => Rd.coord i (ω s) + Rd.coord j (ω s)) ((π n).left k)) ^ 2) -
        (∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
          Rd.coord i (fderiv ℝ f (ω ((π n).right k)) (Rd.basisVec j)) *
            ((fun s => Rd.coord i (ω s)) ((π n).right k) -
              (fun s => Rd.coord i (ω s)) ((π n).left k)) ^ 2) -
        (∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
          Rd.coord i (fderiv ℝ f (ω ((π n).right k)) (Rd.basisVec j)) *
            ((fun s => Rd.coord j (ω s)) ((π n).right k) -
              (fun s => Rd.coord j (ω s)) ((π n).left k)) ^ 2)) / 2) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
    unfold HasQuadraticVariation.matrixIntegral
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      (((tendsto_riemannStieltjes (hQV.pair i j) (hGc i j) ht).sub
        (tendsto_riemannStieltjes (hQV.coord i) (hGc i j) ht)).sub
        (tendsto_riemannStieltjes (hQV.coord j) (hGc i j) ht)).div_const 2
  refine hlim.congr fun n => ?_
  have e : ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
        ω ((π n).right k) - ω ((π n).left k)⟫ =
      ∑ i, ∑ j, ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
        Rd.coord i (fderiv ℝ f (ω ((π n).right k)) (Rd.basisVec j)) *
          ((Rd.coord i (ω ((π n).right k) - ω ((π n).left k)) +
              Rd.coord j (ω ((π n).right k) - ω ((π n).left k))) ^ 2 -
            Rd.coord i (ω ((π n).right k) - ω ((π n).left k)) ^ 2 -
            Rd.coord j (ω ((π n).right k) - ω ((π n).left k)) ^ 2) / 2 := by
    rw [Finset.sum_congr rfl fun k _ => inner_apply_eq _ _]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
  rw [e]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hcsub]
  ring

/-- **Subgoal** (Proposition 3.1 proof: `I_2^n(t) → 0`, `|δω · r| ≤ ρ_{∇f}(osc) |δω|²`). -/
theorem tendsto_remainder {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d}
    (hf : ContDiffBounded 1 f) (t : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      (⟪f (ω ((π n).right k)) - f (ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
        ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
          ω ((π n).right k) - ω ((π n).left k)⟫)) atTop (𝓝 0) := by
  have hDf : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by norm_num)
  have hfd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hω).isBounded.exists_norm_le
  have hωC : ∀ s ∈ Icc 0 T, ‖ω s‖ ≤ C := fun s hs => hC _ (mem_image_of_mem ω hs)
  have hu := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : Rd d) (C + 1)).uniformContinuousOn_of_continuous hDf.continuousOn)
  set M : ℝ := |hQV.trace T| + 1 with hM
  have hM0 : 0 < M := by positivity
  have hevS : ∀ᶠ n in atTop, ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 ≤ M :=
    ((lemma_4_2.tendsto_sum_sq hQV).eventually (gt_mem_nhds
      (show hQV.trace T < M by rw [hM]; linarith [le_abs_self (hQV.trace T)]))).mono
        fun n h => h.le
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδD⟩ := hu (ε / (2 * M)) (by positivity)
  filter_upwards [hevS, hosc.eventually (gt_mem_nhds (lt_min hδ one_pos))] with n hn hon
  rw [Real.dist_eq, sub_zero]
  have hterm : ∀ k : Fin (π n).m,
      |⟪f (ω ((π n).right k)) - f (ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
        ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
          ω ((π n).right k) - ω ((π n).left k)⟫| ≤
        ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 := fun k => by
    have hΔ := lemma_4_2.norm_increment_le hω (π n) k
    have hΔ' : ‖ω ((π n).right k) - ω ((π n).left k)‖ < min δ 1 := hΔ.trans_lt hon
    have hr : ‖ω ((π n).right k)‖ ≤ C := hωC _ ((π n).t_mem _)
    have hrB : ω ((π n).right k) ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have hseg : ∀ z ∈ segment ℝ (ω ((π n).left k)) (ω ((π n).right k)),
        ‖fderiv ℝ f z - fderiv ℝ f (ω ((π n).right k))‖ ≤ ε / (2 * M) := fun z hz => by
      have hz' : z ∈ Metric.closedBall (ω ((π n).right k)) ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
        (convex_closedBall _ _).segment_subset
          (by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])
          (Metric.mem_closedBall_self (norm_nonneg _)) hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz'
      have hzB : z ∈ Metric.closedBall (0 : Rd d) (C + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖z‖ = ‖(z - ω ((π n).right k)) + ω ((π n).right k)‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - ω ((π n).right k)‖ + ‖ω ((π n).right k)‖ := norm_add_le _ _
          _ ≤ C + 1 := by linarith [min_le_right δ 1]
      have := hδD z hzB _ hrB (by rw [dist_eq_norm]; linarith [min_le_left δ 1])
      rw [dist_eq_norm] at this
      exact this.le
    have htay := norm_taylor_le hfd hseg
    rw [← inner_sub_left]
    calc _ ≤ ‖f (ω ((π n).right k)) - f (ω ((π n).left k)) - fderiv ℝ f (ω ((π n).right k))
          (ω ((π n).right k) - ω ((π n).left k))‖ * ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖) *
            ‖ω ((π n).right k) - ω ((π n).left k)‖ :=
          mul_le_mul_of_nonneg_right htay (norm_nonneg _)
      _ = _ := by ring
  calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
        |⟪f (ω ((π n).right k)) - f (ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
          ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
            ω ((π n).right k) - ω ((π n).left k)⟫| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
        ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hterm k
    _ ≤ ∑ k, ε / (2 * M) * ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => by positivity
    _ = ε / (2 * M) * ∑ k, ‖ω ((π n).right k) - ω ((π n).left k)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ε / (2 * M) * M := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- **Subgoal** (Proposition 3.1 proof: the straddling interval `t_k < t < t_{k+1}` contributes
at most `sup |∇f| · osc(ω, π_n)² → 0`). -/
theorem tendsto_boundary {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
      ⟪f (ω t) - f (ω ((π n).left k)), ω t - ω ((π n).left k)⟫) atTop (𝓝 0) := by
  have hfd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  obtain ⟨L, hL⟩ := hf.2 1 le_rfl
  have hL' : ∀ y, ‖fderiv ℝ f y‖ ≤ max L 0 := fun y => by
    rw [← norm_iteratedFDeriv_one]; exact (hL y).trans (le_max_left _ _)
  have hcard : ∀ n, (Finset.univ.filter
      (fun k => (π n).left k < t ∧ t < (π n).right k)).card ≤ 1 := fun n => by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have key : ∀ a b : Fin (π n).m, a < b → (π n).right a ≤ (π n).left b := fun a b hab =>
      (π n).strictMono.monotone (by rw [Fin.le_def]; simp; omega)
    rcases lt_trichotomy a b with h | h | h
    · exact absurd ((key a b h).trans_lt hb.1) (not_lt.2 ha.2.le)
    · exact h
    · exact absurd ((key b a h).trans_lt ha.1) (not_lt.2 hb.2.le)
  refine squeeze_zero_norm (a := fun n => max L 0 * pathOscillation ω (π n) ^ 2) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    have hterm : ∀ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
        |⟪f (ω t) - f (ω ((π n).left k)), ω t - ω ((π n).left k)⟫| ≤
          max L 0 * pathOscillation ω (π n) ^ 2 := fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hs := norm_sub_left_le hω (π n) k ⟨hk.1.le, hk.2.le⟩
      have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hfd y)
        (fun y _ => hL' y) (mem_univ (ω ((π n).left k))) (mem_univ (ω t))
      calc _ ≤ ‖f (ω t) - f (ω ((π n).left k))‖ * ‖ω t - ω ((π n).left k)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (max L 0 * ‖ω t - ω ((π n).left k)‖) * ‖ω t - ω ((π n).left k)‖ :=
            mul_le_mul_of_nonneg_right hmv (norm_nonneg _)
        _ = max L 0 * ‖ω t - ω ((π n).left k)‖ ^ 2 := by ring
        _ ≤ max L 0 * pathOscillation ω (π n) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) (le_max_right _ _)
    have hnn : 0 ≤ max L 0 * pathOscillation ω (π n) ^ 2 :=
      mul_nonneg (le_max_right _ _) (sq_nonneg _)
    calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
          |⟪f (ω t) - f (ω ((π n).left k)), ω t - ω ((π n).left k)⟫| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k)).card •
            (max L 0 * pathOscillation ω (π n) ^ 2) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 1 • (max L 0 * pathOscillation ω (π n) ^ 2) := nsmul_le_nsmul_left hnn (hcard n)
      _ = _ := one_nsmul _
  · have := (hosc.pow 2).const_mul (max L 0)
    simpa using this

end proposition_3_1

/-- **Proposition 3.1.** Let `ω ∈ C^0([0,T], ℝ^d) ∩ Q^π` satisfy (6). For `f ∈ C^1_b(ℝ^d, ℝ^d)`
the limit `[f(ω), ω]_π(t)` exists and equals `∫_0^t ⟨∇f(ω(u)), d[ω]_π(u)⟩`. -/
theorem proposition_3_1 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f) :
    ∀ t ∈ Icc 0 T, Tendsto (fun n => pathwiseCovariation.riemannSum (π n) f ω t) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
  intro t ht
  have h := ((proposition_3_1.tendsto_remainder hω hQV hosc hf t).add
    (proposition_3_1.tendsto_main hω hQV hf ht)).add (proposition_3_1.tendsto_boundary hω hosc hf ht)
  rw [zero_add, add_zero] at h
  refine h.congr fun n => ?_
  rw [proposition_3_1.riemannSum_eq]
  simp only [Finset.sum_sub_distrib]
  ring

end WeakPathwiseIto
