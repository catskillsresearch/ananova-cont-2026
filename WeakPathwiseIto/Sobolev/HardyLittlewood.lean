/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.

Provenance: the covering lemmas `measure_biUnion_le_lintegral_aux` and
`measure_biUnion_le_lintegral` below are adapted from the Carleson project
(https://github.com/fpvandoorn/carleson, file `Carleson/ToMathlib/HardyLittlewood.lean`,
commit f7487cc9da4d1e73f009dc0280cd5b958f3e2c78, Apache-2.0, F. van Doorn et al. and
contributors). Adaptation: specialised to Lebesgue measure on `ℝ^d` with doubling constant
`2^d` (`measure_ball_two_le`) in place of Carleson's `IsDoubling`, and the auxiliary
`def tr` inlined. An unchanged copy of the source file is in `vendor/carleson/`. The `L^p`
bound is proved by truncation and the layer-cake formula instead of Carleson's real
interpolation theorem, which would pull in about 14.6k further lines.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric Vitali
open scoped ENNReal NNReal

namespace WeakPathwiseIto

namespace hardyLittlewood

variable {d : ℕ}

/-- **Subgoal** (Hardy–Littlewood, `M_1 f` is Borel: `x ↦ c ν(B(x, r))` is lower semicontinuous for a
measure `ν`, since `B(x, r - δ) ⊆ B(x', r)` for `x'` near `x` and `ν(B(x, r - δ)) → ν(B(x, r))`). -/
theorem lowerSemicontinuous_mul_measure_ball (ν : Measure (Rd d)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    LowerSemicontinuous fun x => c * ν (Metric.ball x r) := by
  intro x y hy
  set s : ℕ → Set (Rd d) := fun n => Metric.ball x (r - r / ((n : ℝ) + 2)) with hs
  have hmono : Monotone s := by
    intro m n hmn
    refine Metric.ball_subset_ball ?_
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have : r / ((n : ℝ) + 2) ≤ r / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le hm (by linarith [show (m : ℝ) ≤ n from by exact_mod_cast hmn])
    linarith
  have hU : (⋃ n, s n) = Metric.ball x r := by
    ext z
    simp only [mem_iUnion, hs, Metric.mem_ball]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < r / ((n : ℝ) + 2) := by positivity
      linarith
    · intro hz
      have hpos : 0 < r - dist z x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist z x))
      refine ⟨n, ?_⟩
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have : r / ((n : ℝ) + 2) < r - dist z x := by
        rw [div_lt_iff₀ h2]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
  have ht : Tendsto (fun n => c * ν (s n)) atTop (𝓝 (c * ν (Metric.ball x r))) := by
    rw [← hU]
    exact ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop hmono) (Or.inr hc)
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hy)).exists
  have hδ : 0 < r / ((n : ℝ) + 2) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with x' hx'
  refine lt_of_lt_of_le hn (mul_le_mul_right (measure_mono fun z hz => ?_) c)
  simp only [hs, Metric.mem_ball] at hz hx' ⊢
  linarith [dist_triangle z x x', dist_comm x x']

/-- **Subgoal** (Hardy–Littlewood, `M_1 f` is Borel: a supremum of lower semicontinuous ball averages). -/
theorem measurable_localMaximalFunction (f : Rd d → ℝ) :
    Measurable (localMaximalFunction 1 f) := by
  unfold localMaximalFunction
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_iSup fun r =>
    lowerSemicontinuous_iSup fun hr => lowerSemicontinuous_iSup fun _ => ?_)
  have h : ∀ x, laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ) =
      (volume (Metric.ball (0 : Rd d) r))⁻¹ *
        (volume.withDensity fun y => ‖f y‖ₑ) (Metric.ball x r) := by
    intro x
    rw [laverage_eq, withDensity_apply _ Metric.isOpen_ball.measurableSet,
      Measure.restrict_apply_univ, Measure.addHaar_ball_center, ENNReal.div_eq_inv_mul]
  simp_rw [h]
  exact lowerSemicontinuous_mul_measure_ball _ hr _ (ENNReal.inv_ne_top.2 (Metric.measure_ball_pos volume _ hr).ne')


/-- **Subgoal** (Hardy–Littlewood, Lebesgue measure is doubling: `|B(x, 2r)| ≤ 2^d |B(x, r)|`). -/
theorem measure_ball_two_le (x : Rd d) (r : ℝ) :
    volume (Metric.ball x (2 * r)) ≤ 2 ^ d * volume (Metric.ball x r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 (by linarith)]; simp
  rw [Measure.addHaar_ball_of_pos _ _ (by linarith), Measure.addHaar_ball_of_pos _ _ hr,
    finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (by positivity), ← mul_assoc,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **Subgoal** (Hardy–Littlewood, Vitali covering for balls of bounded radius; adapted from
Carleson `measure_biUnion_le_lintegral_aux`). -/
theorem measure_biUnion_le_lintegral_aux {ι : Type*} {𝓑 : Set ι} {c : ι → Rd d} {r : ι → ℝ}
    (l : ℝ≥0∞) (u : Rd d → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * volume (Metric.ball (c i) (r i)) ≤
      ∫⁻ x in Metric.ball (c i) (r i), u x) :
    l * volume (⋃ i ∈ 𝓑, Metric.ball (c i) (r i)) ≤ (2 ^ d) ^ 2 * ∫⁻ x, u x := by
  let 𝓑' := { a ∈ 𝓑 | 0 < r a }
  obtain ⟨B, hB𝓑, hB, h2B⟩ := exists_disjoint_subfamily_covering_enlargement_ball
    𝓑' c r R (fun a ha => hR a ha.1) (2 ^ 2) (by norm_num)
  have : Countable B := hB.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a ha => nonempty_ball.mpr (hB𝓑 ha).right)
  have disj := fun i j hij ↦
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * volume (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * volume (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
      refine mul_right_mono (measure_mono fun x hx ↦ ?_)
      simp only [mem_iUnion] at hx
      rcases hx with ⟨i, i𝓑, hi⟩
      have i𝓑' : i ∈ 𝓑' := .intro i𝓑 (nonempty_ball.mp (nonempty_of_mem hi))
      obtain ⟨b, bB, hb⟩ := h2B i i𝓑'
      exact mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, volume (ball (c i) (2 ^ 2 * r i)) :=
      mul_right_mono <| measure_biUnion_le volume this fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, (2 ^ d) ^ 2 * volume (ball (c i) (r i)) := by
      refine mul_right_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
      rw [sq, sq, mul_assoc, mul_assoc]
      apply (measure_ball_two_le (c i) (2 * r i)).trans
      gcongr; exact measure_ball_two_le (c i) (r i)
    _ = (2 ^ d) ^ 2 * ∑' i : B, l * volume (ball (c i) (r i)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ (2 ^ d) ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x := by
      gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _)).left
    _ = (2 ^ d) ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x := by
      congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ (2 ^ d) ^ 2 * ∫⁻ x, u x := by
      gcongr; exact Measure.restrict_le_self

/-- **Subgoal** (Hardy–Littlewood, Vitali covering for arbitrary balls; adapted from Carleson
`measure_biUnion_le_lintegral`). -/
theorem measure_biUnion_le_lintegral {ι : Type*} (𝓑 : Set ι) {c : ι → Rd d} {r : ι → ℝ}
    (l : ℝ≥0∞) (u : Rd d → ℝ≥0∞)
    (h2u : ∀ i ∈ 𝓑, l * volume (Metric.ball (c i) (r i)) ≤
      ∫⁻ x in Metric.ball (c i) (r i), u x) :
    l * volume (⋃ i ∈ 𝓑, Metric.ball (c i) (r i)) ≤ (2 ^ d) ^ 2 * ∫⁻ x, u x := by
  set tr : ℕ → Set ι := fun k => {i | i ∈ 𝓑 ∧ r i ≤ k} with htr
  have tr_mono : Monotone tr := by
    intro i j hij
    rintro k ⟨hi₁, hi₂⟩
    exact ⟨hi₁, hi₂.trans (Nat.cast_le.mpr hij)⟩
  have tr_union : 𝓑 = ⋃ k, tr k := by
    apply eq_of_subset_of_subset
    · intro i hi
      rcases exists_nat_ge (r i) with ⟨k, hk⟩
      exact mem_iUnion.mpr ⟨k, hi, hk⟩
    · intro i hi
      exact (mem_iUnion.mp hi).elim (fun _ p => p.left)
  have : volume (⋃ i ∈ 𝓑, ball (c i) (r i)) = ⨆ k, volume (⋃ i ∈ tr k, ball (c i) (r i)) := by
    conv_lhs => rw [tr_union, biUnion_iUnion]
    have : Monotone (⋃ x ∈ tr ·, ball (c x) (r x)) :=
      fun i j hij ↦ biUnion_mono (tr_mono hij) (fun _ _ ↦ by rfl)
    rw [this.measure_iUnion]
  rw [this, ENNReal.mul_iSup]
  exact iSup_le fun R ↦
    measure_biUnion_le_lintegral_aux l u R (fun i hi ↦ hi.2) (fun i hi ↦ h2u i hi.1)

/-- **Subgoal** (Hardy–Littlewood, `t < M_1 f(x)` is witnessed by a ball `B(x, r)`, `r < 1`). -/
theorem exists_ball_of_lt {f : Rd d → ℝ} {x : Rd d} {t : ℝ≥0∞}
    (h : t < localMaximalFunction 1 f x) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      t * volume (Metric.ball x r) ≤ ∫⁻ y in Metric.ball x r, ‖f y‖ₑ := by
  unfold localMaximalFunction at h
  simp only [lt_iSup_iff] at h
  obtain ⟨r, hr, hr1, ht⟩ := h
  refine ⟨r, hr, ENNReal.ofReal_lt_one.1 hr1, ?_⟩
  rw [laverage_eq, Measure.restrict_apply_univ] at ht
  have hV0 : volume (Metric.ball x r) ≠ 0 := (Metric.measure_ball_pos _ _ hr).ne'
  have hVt : volume (Metric.ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hV0) (Or.inl hVt) |>.1 ht).le

/-- **Subgoal** (Hardy–Littlewood, weak type `(1, 1)`: `t |{M_1 f > t}| ≤ 4^d ‖f‖_1`). -/
theorem mul_measure_lt_le (f : Rd d → ℝ) (t : ℝ≥0∞) :
    t * volume {x | t < localMaximalFunction 1 f x} ≤ (2 ^ d) ^ 2 * ∫⁻ y, ‖f y‖ₑ := by
  set 𝓑 : Set (Rd d × ℝ) := {i | t * volume (Metric.ball i.1 i.2) ≤
    ∫⁻ y in Metric.ball i.1 i.2, ‖f y‖ₑ}
  have hsub : {x | t < localMaximalFunction 1 f x} ⊆ ⋃ i ∈ 𝓑, Metric.ball i.1 i.2 := by
    intro x hx
    obtain ⟨r, hr, -, hle⟩ := exists_ball_of_lt hx
    exact mem_iUnion₂.2 ⟨(x, r), hle, Metric.mem_ball_self hr⟩
  calc t * volume {x | t < localMaximalFunction 1 f x}
      ≤ t * volume (⋃ i ∈ 𝓑, Metric.ball i.1 i.2) := by gcongr
    _ ≤ (2 ^ d) ^ 2 * ∫⁻ y, ‖f y‖ₑ :=
      measure_biUnion_le_lintegral (c := Prod.fst) (r := Prod.snd) 𝓑 t _ fun i hi => hi

/-- **Subgoal** (Hardy–Littlewood, sublinearity: `|f| ≤ |g| + |h|` gives
`M_1 f ≤ M_1 g + M_1 h`). -/
theorem le_add {f g h : Rd d → ℝ} (hg : Measurable g)
    (hfgh : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ + ‖h y‖ₑ) (x : Rd d) :
    localMaximalFunction 1 f x ≤ localMaximalFunction 1 g x + localMaximalFunction 1 h x := by
  have hmem : ∀ (φ : Rd d → ℝ) (r : ℝ), 0 < r → ENNReal.ofReal r < 1 →
      laverage (volume.restrict (Metric.ball x r)) (fun y => ‖φ y‖ₑ) ≤
        localMaximalFunction 1 φ x := fun φ r hr hr1 => by
    unfold localMaximalFunction
    apply le_iSup_of_le r; apply le_iSup_of_le hr; apply le_iSup_of_le hr1; exact le_rfl
  conv_lhs => unfold localMaximalFunction
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hr1 => ?_
  calc laverage (volume.restrict (Metric.ball x r)) (fun y => ‖f y‖ₑ)
      ≤ laverage (volume.restrict (Metric.ball x r)) (fun y => ‖g y‖ₑ + ‖h y‖ₑ) :=
        laverage_mono_ae (ae_of_all _ hfgh)
    _ = laverage (volume.restrict (Metric.ball x r)) (fun y => ‖g y‖ₑ) +
          laverage (volume.restrict (Metric.ball x r)) (fun y => ‖h y‖ₑ) := by
        simp only [laverage_eq]
        rw [lintegral_add_left hg.enorm, ENNReal.add_div]
    _ ≤ _ := add_le_add (hmem g r hr hr1) (hmem h r hr hr1)

/-- **Subgoal** (Hardy–Littlewood, `|g| ≤ c` gives `M_1 g ≤ c`). -/
theorem le_of_enorm_le {g : Rd d → ℝ} {c : ℝ≥0∞} (hg : ∀ y, ‖g y‖ₑ ≤ c) (x : Rd d) :
    localMaximalFunction 1 g x ≤ c := by
  unfold localMaximalFunction
  refine iSup_le fun r => iSup_le fun _ => iSup_le fun _ => ?_
  refine (laverage_mono_ae (ae_of_all _ hg)).trans ?_
  rw [laverage_eq, lintegral_const]
  rw [mul_div_assoc]
  exact mul_le_of_le_one_right' ENNReal.div_self_le_one

/-- **Subgoal** (Hardy–Littlewood, truncated weak bound:
`t |{M_1 f > t}| ≤ 2 · 4^d ∫_{2|f| > t} |f|`). -/
theorem mul_measure_lt_le_truncate {f : Rd d → ℝ} (hf : Measurable f) (t : ℝ) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < localMaximalFunction 1 f x} ≤
      2 * (2 ^ d) ^ 2 * ∫⁻ y in {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ}, ‖f y‖ₑ := by
  set S : Set (Rd d) := {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ} with hS_def
  have hS : MeasurableSet S := measurableSet_lt measurable_const (hf.enorm.const_mul _)
  set a : ℝ≥0∞ := ENNReal.ofReal t / 2 with ha_def
  have h2a : 2 * a = ENNReal.ofReal t := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have haa : a + a = ENNReal.ofReal t := ENNReal.add_halves _
  have hg : Measurable (S.indicator f) := hf.indicator hS
  have hsplit : ∀ y, ‖f y‖ₑ ≤ ‖S.indicator f y‖ₑ + ‖Sᶜ.indicator f y‖ₑ := fun y => by
    by_cases hy : y ∈ S
    · simp [hy]
    · simp [hy]
  have hh : ∀ y, ‖Sᶜ.indicator f y‖ₑ ≤ a := fun y => by
    by_cases hy : y ∈ S
    · simp [hy]
    · rw [indicator_of_mem (show y ∈ Sᶜ from hy)]
      simp only [hS_def, mem_ofPred_eq, not_lt] at hy
      rw [ha_def, ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
        mul_comm]
      exact hy
  have hsub : {x | ENNReal.ofReal t < localMaximalFunction 1 f x} ⊆
      {x | a < localMaximalFunction 1 (S.indicator f) x} := fun x hx => by
    simp only [mem_ofPred_eq] at hx ⊢
    by_contra hle
    push Not at hle
    have := (le_add hg hsplit x).trans (add_le_add hle (le_of_enorm_le hh x))
    rw [haa] at this
    exact absurd hx (not_lt.2 this)
  calc ENNReal.ofReal t * volume {x | ENNReal.ofReal t < localMaximalFunction 1 f x}
      ≤ 2 * (a * volume {x | a < localMaximalFunction 1 (S.indicator f) x}) := by
        rw [← mul_assoc, h2a]; gcongr
    _ ≤ 2 * ((2 ^ d) ^ 2 * ∫⁻ y, ‖S.indicator f y‖ₑ) := by
        exact mul_right_mono (mul_measure_lt_le _ a)
    _ = 2 * (2 ^ d) ^ 2 * ∫⁻ y in S, ‖f y‖ₑ := by
        rw [← mul_assoc]
        congr 1
        simp_rw [enorm_indicator_eq_indicator_enorm]
        exact lintegral_indicator hS _

/-- **Subgoal** (Hardy–Littlewood, `∫_0^a q t^{q-1} dt = a^q` in `ℝ≥0∞`). -/
theorem lintegral_Ioi_indicator_rpow {q : ℝ} (hq : 0 < q) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (t ^ (q - 1))) t = a ^ q / ENNReal.ofReal q := by
  have hfin : ∀ b : ℝ, 0 ≤ b → ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal b}.indicator
      (fun t => ENNReal.ofReal (t ^ (q - 1))) t = ENNReal.ofReal b ^ q / ENNReal.ofReal q := by
    intro b hb
    have hS : MeasurableSet {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal b} :=
      measurableSet_lt ENNReal.measurable_ofReal measurable_const
    rw [lintegral_indicator hS, Measure.restrict_restrict hS]
    have hset : {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal b} ∩ Ioi 0 = Ioo 0 b := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo, ENNReal.ofReal_lt_ofReal_iff']
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1.trans h2⟩, h1⟩
    have hint : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Ioo 0 b) :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) (by linarith : (-1 : ℝ) < q - 1)).1).mono_set Ioo_subset_Ioc_self
    rw [hset, ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => Real.rpow_nonneg ht.1.le _),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < q - 1)), sub_add_cancel,
      Real.zero_rpow hq.ne', sub_zero, ENNReal.ofReal_div_of_pos hq,
      ENNReal.ofReal_rpow_of_nonneg hb hq.le]
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [ENNReal.top_rpow_of_pos hq, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    have hle : ∀ n : ℕ, ((n : ℝ≥0∞)) ^ q / ENNReal.ofReal q ≤
        ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < ⊤}.indicator
          (fun t => ENNReal.ofReal (t ^ (q - 1))) t := fun n => by
      rw [← ENNReal.ofReal_natCast, ← hfin n (Nat.cast_nonneg n)]
      refine lintegral_mono fun t => indicator_le_indicator_of_subset
        (fun t _ => ENNReal.ofReal_lt_top) (fun _ => bot_le) t
    have ht : Tendsto (fun n : ℕ => ((n : ℝ≥0∞)) ^ q / ENNReal.ofReal q) atTop (𝓝 ⊤) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞)) ^ q) atTop (𝓝 ⊤) := by
        have := ((ENNReal.continuous_rpow_const (y := q)).tendsto ⊤).comp
          ENNReal.tendsto_nat_nhds_top
        rwa [ENNReal.top_rpow_of_pos hq] at this
      have := ENNReal.Tendsto.div_const h1 (Or.inr (ENNReal.ofReal_pos.2 hq).ne')
      rwa [ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at this
    exact top_unique (le_of_tendsto' ht hle)
  · rw [← ENNReal.ofReal_toReal ha]
    exact hfin _ ENNReal.toReal_nonneg

/-- **Subgoal** (Hardy–Littlewood, layer-cake formula for `ℝ≥0∞`-valued functions). -/
theorem lintegral_rpow_eq_lintegral_meas_lt {g : Rd d → ℝ≥0∞} (hg : Measurable g) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ x, g x ^ p = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt' : ∀ x, g x ^ p = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
      {t : ℝ | ENNReal.ofReal t < g x}.indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t :=
    fun x => by rw [lintegral_Ioi_indicator_rpow hp, ENNReal.mul_div_cancel hp0 hpt]
  simp_rw [hpt']
  rw [lintegral_const_mul' _ _ hpt]
  congr 1
  have hF : Measurable (Function.uncurry fun (x : Rd d) (t : ℝ) =>
      {t : ℝ | ENNReal.ofReal t < g x}.indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t) := by
    have hS : MeasurableSet {z : Rd d × ℝ | ENNReal.ofReal z.2 < g z.1} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hg.comp measurable_fst)
    exact ((measurable_snd.pow_const (p - 1)).ennreal_ofReal).indicator hS
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun t => ?_
  have hSt : MeasurableSet {x | ENNReal.ofReal t < g x} := measurableSet_lt measurable_const hg
  rw [mul_comm, ← lintegral_indicator_const hSt]
  rfl

/-- **Subgoal** (Hardy–Littlewood, Tonelli for the truncated bound:
`∫_0^∞ t^{p-2} ∫_{2|f| > t} |f| dt = 2^{p-1}/(p-1) ‖f‖_p^p`). -/
theorem lintegral_truncate_eq {f : Rd d → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ y in {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ}, ‖f y‖ₑ =
      2 ^ (p - 1) / ENNReal.ofReal (p - 1) * ∫⁻ y, ‖f y‖ₑ ^ p := by
  have hS : MeasurableSet {z : ℝ × Rd d | ENNReal.ofReal z.1 < 2 * ‖f z.2‖ₑ} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
      ((hf.comp measurable_snd).enorm.const_mul _)
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (p - 2)) *
      ∫⁻ y in {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ}, ‖f y‖ₑ =
      ∫⁻ y, {z : ℝ × Rd d | ENNReal.ofReal z.1 < 2 * ‖f z.2‖ₑ}.indicator
        (fun z => ENNReal.ofReal (z.1 ^ (p - 2)) * ‖f z.2‖ₑ) (t, y) := fun t => by
    have hSt : MeasurableSet {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ} :=
      measurableSet_lt measurable_const (hf.enorm.const_mul _)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hSt]
    refine lintegral_congr fun y => ?_
    by_cases hy : ENNReal.ofReal t < 2 * ‖f y‖ₑ
    · simp [indicator_of_mem, hy]
    · simp [indicator_of_notMem, hy]
  simp_rw [h1]
  have hF : Measurable (Function.uncurry fun (t : ℝ) (y : Rd d) =>
      {z : ℝ × Rd d | ENNReal.ofReal z.1 < 2 * ‖f z.2‖ₑ}.indicator
        (fun z => ENNReal.ofReal (z.1 ^ (p - 2)) * ‖f z.2‖ₑ) (t, y)) :=
    (((measurable_fst.pow_const (p - 2)).ennreal_ofReal).mul
      (hf.comp measurable_snd).enorm).indicator hS
  rw [lintegral_lintegral_swap hF.aemeasurable, ← lintegral_const_mul' _ _
    (ENNReal.div_ne_top (by simp) (ENNReal.ofReal_pos.2 (by linarith)).ne')]
  refine lintegral_congr fun y => ?_
  have h2 : ∀ t : ℝ, {z : ℝ × Rd d | ENNReal.ofReal z.1 < 2 * ‖f z.2‖ₑ}.indicator
      (fun z => ENNReal.ofReal (z.1 ^ (p - 2)) * ‖f z.2‖ₑ) (t, y) =
      {t : ℝ | ENNReal.ofReal t < 2 * ‖f y‖ₑ}.indicator
        (fun t => ENNReal.ofReal (t ^ (p - 1 - 1))) t * ‖f y‖ₑ := fun t => by
    rw [show p - 1 - 1 = p - 2 by ring]
    by_cases ht : ENNReal.ofReal t < 2 * ‖f y‖ₑ
    · simp [indicator_of_mem, ht]
    · simp [indicator_of_notMem, ht]
  simp_rw [h2]
  rw [lintegral_mul_const' _ _ enorm_ne_top, lintegral_Ioi_indicator_rpow (by linarith),
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
  have h3 : ‖f y‖ₑ ^ p = ‖f y‖ₑ ^ (p - 1) * ‖f y‖ₑ := by
    conv_lhs => rw [show p = (p - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  rw [h3, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Subgoal** (Hardy–Littlewood, strong type `(p, p)`, `p > 1`, for measurable `f`). -/
theorem lintegral_rpow_le {f : Rd d → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, localMaximalFunction 1 f x ^ p ≤
      ENNReal.ofReal p * (2 * (2 ^ d) ^ 2) * (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
        ∫⁻ y, ‖f y‖ₑ ^ p := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, `M_1 f` depends only on the a.e. class of `f`). -/
theorem congr_ae {f g : Rd d → ℝ} (h : f =ᵐ[volume] g) :
    localMaximalFunction 1 f = localMaximalFunction 1 g := by
  sorry

end hardyLittlewood

end WeakPathwiseIto
