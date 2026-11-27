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
  sorry

/-- **Subgoal** (Hardy–Littlewood, `t < M_1 f(x)` is witnessed by a ball `B(x, r)`, `r < 1`). -/
theorem exists_ball_of_lt {f : Rd d → ℝ} {x : Rd d} {t : ℝ≥0∞}
    (h : t < localMaximalFunction 1 f x) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      t * volume (Metric.ball x r) ≤ ∫⁻ y in Metric.ball x r, ‖f y‖ₑ := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, weak type `(1, 1)`: `t |{M_1 f > t}| ≤ 4^d ‖f‖_1`). -/
theorem mul_measure_lt_le (f : Rd d → ℝ) (t : ℝ≥0∞) :
    t * volume {x | t < localMaximalFunction 1 f x} ≤ (2 ^ d) ^ 2 * ∫⁻ y, ‖f y‖ₑ := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, sublinearity: `|f| ≤ |g| + |h|` gives
`M_1 f ≤ M_1 g + M_1 h`). -/
theorem le_add {f g h : Rd d → ℝ} (hg : Measurable g)
    (hfgh : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ + ‖h y‖ₑ) (x : Rd d) :
    localMaximalFunction 1 f x ≤ localMaximalFunction 1 g x + localMaximalFunction 1 h x := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, `|g| ≤ c` gives `M_1 g ≤ c`). -/
theorem le_of_enorm_le {g : Rd d → ℝ} {c : ℝ≥0∞} (hg : ∀ y, ‖g y‖ₑ ≤ c) (x : Rd d) :
    localMaximalFunction 1 g x ≤ c := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, truncated weak bound:
`t |{M_1 f > t}| ≤ 2 · 4^d ∫_{2|f| > t} |f|`). -/
theorem mul_measure_lt_le_truncate {f : Rd d → ℝ} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < localMaximalFunction 1 f x} ≤
      2 * (2 ^ d) ^ 2 * ∫⁻ y in {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ}, ‖f y‖ₑ := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, `∫_0^a q t^{q-1} dt = a^q` in `ℝ≥0∞`). -/
theorem lintegral_Ioi_indicator_rpow {q : ℝ} (hq : 0 < q) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (t ^ (q - 1))) t = a ^ q / ENNReal.ofReal q := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, layer-cake formula for `ℝ≥0∞`-valued functions). -/
theorem lintegral_rpow_eq_lintegral_meas_lt {g : Rd d → ℝ≥0∞} (hg : Measurable g) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ x, g x ^ p = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)) := by
  sorry

/-- **Subgoal** (Hardy–Littlewood, Tonelli for the truncated bound:
`∫_0^∞ t^{p-2} ∫_{2|f| > t} |f| dt = 2^{p-1}/(p-1) ‖f‖_p^p`). -/
theorem lintegral_truncate_eq {f : Rd d → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ y in {y | ENNReal.ofReal t < 2 * ‖f y‖ₑ}, ‖f y‖ₑ =
      2 ^ (p - 1) / ENNReal.ofReal (p - 1) * ∫⁻ y, ‖f y‖ₑ ^ p := by
  sorry

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
