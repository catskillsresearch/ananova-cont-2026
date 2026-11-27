/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.IsCubeOrBall
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace lemma_2_2

variable {d : ℕ}

/-- **Subgoal** (Lemma 2.2 proof, maximal function on a closed ball): for `0 < ρ` with
`ρ ≤ R`, `∫_{B̄(a,ρ)} |f| ≤ |B(a,ρ)| M_R f(a)`. -/
theorem lintegral_closedBall_le (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ} (hρ : 0 < ρ) {R : ℝ≥0∞}
    (hρR : ENNReal.ofReal ρ ≤ R) :
    ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ ≤ volume (Metric.ball a ρ) * localMaximalFunction R f a := by
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
  have hlt : ENNReal.ofReal (ρ - 1 / ((n : ℝ) + 1)) < R :=
    ((ENNReal.ofReal_lt_ofReal_iff hρ).2 (by linarith)).trans_le hρR
  have hM : laverage (volume.restrict (Metric.ball a (ρ - 1 / ((n : ℝ) + 1)))) (fun y => ‖f y‖ₑ) ≤
      localMaximalFunction R f a := by
    unfold localMaximalFunction
    exact le_iSup_of_le (ρ - 1 / ((n : ℝ) + 1)) (le_iSup_of_le hr (le_iSup_of_le hlt le_rfl))
  rw [← measure_mul_laverage, Measure.restrict_apply_univ]
  exact mul_le_mul' (measure_mono (Metric.ball_subset_ball (by linarith))) hM

/-- **Subgoal** (Lemma 2.2 proof, `Q ⊂ B̄(x, diam Q)`): for `d ≥ 1`, a cube or ball has finite
positive diameter and lies in the closed ball of radius `diam Q` about each of its points. -/
theorem subset_closedBall (hd : 0 < d) {Q : Set (Rd d)} (hQ : IsCubeOrBall Q) {x : Rd d}
    (hx : x ∈ Q) : Metric.ediam Q ≠ ⊤ ∧ 0 < (Metric.ediam Q).toReal ∧
      Q ⊆ Metric.closedBall x (Metric.ediam Q).toReal := by
  obtain ⟨c, r, hr, hQ'⟩ := hQ
  have hcoord : ∀ (v : Rd d) (i : Fin d), Rd.coord i v = v i := fun v i => by
    rw [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]; simp
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- every point of `Q` is within `r d` of `c`
  have hcube : ∀ v : Rd d, (∀ i, |Rd.coord i v| ≤ r) → ‖v‖ ≤ r * d := by
    intro v hv
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ i, ‖v i‖ ^ 2 ≤ (r * d) ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, ← hcoord]
            exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
        _ = d * r ^ 2 := by simp
        _ ≤ (r * d) ^ 2 := by nlinarith [sq_nonneg r]
    calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((r * d) ^ 2) := Real.sqrt_le_sqrt hs
      _ = r * d := Real.sqrt_sq (by positivity)
  have hsub : Q ⊆ Metric.closedBall c (r * d) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases hQ' with rfl | rfl | rfl | rfl
    · exact (le_of_lt (by simpa [dist_eq_norm] using hy)).trans (by nlinarith)
    · exact (by simpa [dist_eq_norm] using hy : ‖y - c‖ ≤ r).trans (by nlinarith)
    · exact hcube _ fun i => (hy i).le
    · exact hcube _ hy
  have hne : Metric.ediam Q ≠ ⊤ :=
    Metric.isBounded_iff_ediam_ne_top.1 (Metric.isBounded_closedBall.subset hsub)
  -- two distinct points of `Q`
  set e : Rd d := Rd.basisVec ⟨0, hd⟩
  have he : ‖e‖ = 1 := by simp [e, Rd.basisVec]
  have hec : ∀ i, |Rd.coord i ((r / 2) • e)| ≤ r / 2 := by
    intro i
    rw [hcoord, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by positivity : 0 < r / 2)]
    have : |e i| ≤ 1 := by
      rw [← hcoord, Rd.coord]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [he, one_mul]; simp [Rd.basisVec]
    nlinarith [abs_nonneg (e i)]
  have hc : c ∈ Q := by
    rcases hQ' with rfl | rfl | rfl | rfl
    · exact Metric.mem_ball_self hr
    · exact Metric.mem_closedBall_self hr.le
    · intro i; simp [Rd.coord, hr]
    · intro i; simp [Rd.coord, hr.le]
  have hp : c + (r / 2) • e ∈ Q := by
    have hn : ‖(r / 2) • e‖ = r / 2 := by rw [norm_smul, he, Real.norm_of_nonneg (by positivity), mul_one]
    rcases hQ' with rfl | rfl | rfl | rfl
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hn]; linarith
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hn]; linarith
    · intro i; rw [add_sub_cancel_left]; linarith [hec i]
    · intro i; rw [add_sub_cancel_left]; linarith [hec i]
  have hpos : 0 < Metric.ediam Q := by
    refine lt_of_lt_of_le ?_ (Metric.edist_le_ediam_of_mem hc hp)
    rw [edist_pos]
    intro h
    have : ‖(r / 2) • e‖ = 0 := by
      rw [show (r / 2) • e = (c + (r / 2) • e) - c by abel, ← h, sub_self, norm_zero]
    rw [norm_smul, he] at this
    have : r / 2 = 0 := by simpa [abs_of_pos hr] using this
    linarith
  refine ⟨hne, ENNReal.toReal_pos hpos.ne' hne, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_edist]
  exact ENNReal.toReal_mono hne (Metric.edist_le_ediam_of_mem hy hx)

/-- **Subgoal** (Lemma 2.2 proof, `α < d`, one dyadic shell): on
`{ρ/2^{k+1} < |y - x| ≤ ρ/2^k}`, `∫ |f| |x - y|^{α-d} ≤ 2^{d-α} ρ^α 2^{-kα} |B(0,1)| M_ρ f(x)`. -/
theorem lintegral_shell_le {α : ℝ} (hα : 0 < α) (hαd : α < d) (f : Rd d → ℝ) (x : Rd d)
    {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∫⁻ y in {y | ρ / 2 ^ (k + 1) < dist y x ∧ dist y x ≤ ρ / 2 ^ k},
        ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k) *
        volume (Metric.ball (0 : Rd d) 1) * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set a := ρ / 2 ^ (k + 1) with ha_def
  set b := ρ / 2 ^ k with hb_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hbρ : b ≤ ρ := div_le_self hρ.le (one_le_pow₀ (by norm_num))
  have hs : 0 ≤ (d : ℝ) - α := by linarith
  have hS : {y | a < dist y x ∧ dist y x ≤ b} = Metric.closedBall x b \ Metric.closedBall x a := by
    ext y; simp [Metric.mem_closedBall, and_comm]
  rw [hS]
  set K : ℝ≥0∞ := (ENNReal.ofReal a ^ ((d : ℝ) - α))⁻¹ with hK
  have hpt : ∀ y ∈ Metric.closedBall x b \ Metric.closedBall x a,
      ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤ ‖f y‖ₑ * K := by
    intro y hy
    have hay : a < dist x y := by
      have := hy.2; rw [Metric.mem_closedBall, not_le, dist_comm] at this; exact this
    rw [div_eq_mul_inv, hK]
    gcongr
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hay.le
  have hvol : volume (Metric.ball x b) = ENNReal.ofReal (b ^ d) * volume (Metric.ball (0 : Rd d) 1) := by
    rw [Measure.addHaar_ball volume x hb.le, finrank_euclideanSpace_fin]
  have hreal : ((a ^ ((d : ℝ) - α))⁻¹ * b ^ d) =
      (2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k := by
    have h2 : (0:ℝ) < 2 := two_pos
    rw [ha_def, hb_def, ← Real.rpow_natCast (ρ / 2 ^ k), Real.rpow_def_of_pos ha,
      Real.rpow_def_of_pos hb, Real.rpow_def_of_pos h2, Real.rpow_def_of_pos hρ,
      Real.rpow_def_of_pos h2, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, Real.log_div hρ.ne' (by positivity), Real.log_div hρ.ne' (by positivity),
      Real.log_pow, Real.log_pow]
    congr 1
    push_cast
    ring
  have hKe : K * ENNReal.ofReal (b ^ d) =
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k) := by
    rw [hK, ENNReal.ofReal_rpow_of_pos ha, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hreal]
  calc ∫⁻ y in Metric.closedBall x b \ Metric.closedBall x a, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α)
      ≤ ∫⁻ y in Metric.closedBall x b \ Metric.closedBall x a, ‖f y‖ₑ * K :=
        setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_closedBall) hpt
    _ = (∫⁻ y in Metric.closedBall x b \ Metric.closedBall x a, ‖f y‖ₑ) * K :=
        lintegral_mul_const' _ _ (by
          rw [hK]
          exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ha) ENNReal.ofReal_ne_top).ne')
    _ ≤ (∫⁻ y in Metric.closedBall x b, ‖f y‖ₑ) * K := by
        gcongr
        exact sdiff_subset
    _ ≤ (volume (Metric.ball x b) * localMaximalFunction (ENNReal.ofReal ρ) f x) * K := by
        gcongr
        exact lintegral_closedBall_le f x hb (ENNReal.ofReal_le_ofReal hbρ)
    _ = _ := by
        rw [hvol, ← hKe]
        ring

/-- **Subgoal** (Lemma 2.2 proof, `α < d`): summing the dyadic shells,
`∫_{B̄(x,ρ)} |f| |x - y|^{α-d} ≤ C ρ^α M_ρ f(x)`. -/
theorem lintegral_closedBall_kernel_le_of_lt {α : ℝ} (hα : 0 < α) (hαd : α < d) :
    ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (x : Rd d) {ρ : ℝ}, 0 < ρ →
      ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
        C * ENNReal.ofReal ρ ^ α * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := hα.trans hαd
    exact_mod_cast this
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set V := volume (Metric.ball (0 : Rd d) 1) with hV
  set r : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-α)) with hr
  have hr1 : r < 1 := ENNReal.ofReal_lt_one.2
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hα))
  set C' : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α)) * V * (1 - r)⁻¹ with hC'
  have hC'top : C' ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    measure_ball_lt_top.ne) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne')
  refine ⟨C'.toNNReal, fun f x ρ hρ => ?_⟩
  rw [ENNReal.coe_toNNReal hC'top]
  set S : ℕ → Set (Rd d) := fun k => {y | ρ / 2 ^ (k + 1) < dist y x ∧ dist y x ≤ ρ / 2 ^ k}
    with hSdef
  have hcover : Metric.closedBall x ρ ⊆ {x} ∪ ⋃ k, S k := by
    intro y hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    right
    have hpos : 0 < dist y x := dist_pos.2 hyx
    have hyr : dist y x ≤ ρ := hy
    have hex : ∃ k : ℕ, ρ / 2 ^ (k + 1) < dist y x := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ρ / dist y x) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hpos] at hn
      rw [div_lt_iff₀ (by positivity), pow_succ]
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith
    classical
    refine mem_iUnion.2 ⟨Nat.find hex, show _ ∧ _ from ⟨Nat.find_spec hex, ?_⟩⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos'
    · rw [h0, pow_zero, div_one]; exact hyr
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos').symm⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      rw [hj]; exact not_lt.1 this
  have h0 : volume ({x} : Set (Rd d)) = 0 := measure_singleton x
  set A : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α)) * ENNReal.ofReal (ρ ^ α) * V *
    localMaximalFunction (ENNReal.ofReal ρ) f x with hA
  have hterm : ∀ k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k) *
      V * localMaximalFunction (ENNReal.ofReal ρ) f x = A * r ^ k := fun k => by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), hA, hr]
    ring
  calc _ ≤ ∫⁻ y in {x} ∪ ⋃ k, S k, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ y in {x}, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α)) +
          ∫⁻ y in ⋃ k, S k, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) :=
        lintegral_union_le _ _ _
    _ = ∫⁻ y in ⋃ k, S k, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) := by
        rw [setLIntegral_measure_zero _ _ h0, zero_add]
    _ ≤ ∑' k, ∫⁻ y in S k, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k, ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) - α) * ρ ^ α * ((2 : ℝ) ^ (-α)) ^ k) *
          V * localMaximalFunction (ENNReal.ofReal ρ) f x :=
        ENNReal.tsum_le_tsum fun k => lintegral_shell_le hα hαd f x hρ k
    _ = ∑' k, A * r ^ k := tsum_congr hterm
    _ = A * (1 - r)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = _ := by
        rw [hA, hC', ENNReal.ofReal_rpow_of_pos hρ]
        ring

/-- **Subgoal** (Lemma 2.2 proof, `d ≤ α`): the kernel is at most `ρ^{α-d}` on `B̄(x,ρ)`, so
`∫_{B̄(x,ρ)} |f| |x - y|^{α-d} ≤ |B(0,1)| ρ^α M_ρ f(x)`. -/
theorem lintegral_closedBall_kernel_le_of_ge {α : ℝ} (hα : 0 < α) (hαd : (d : ℝ) ≤ α) :
    ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (x : Rd d) {ρ : ℝ}, 0 < ρ →
      ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
        C * ENNReal.ofReal ρ ^ α * localMaximalFunction (ENNReal.ofReal ρ) f x := by
  set V := volume (Metric.ball (0 : Rd d) 1) with hV
  refine ⟨V.toNNReal, fun f x ρ hρ => ?_⟩
  rw [ENNReal.coe_toNNReal measure_ball_lt_top.ne]
  have hs : (d : ℝ) - α ≤ 0 := by linarith
  set K : ℝ≥0∞ := (ENNReal.ofReal ρ ^ ((d : ℝ) - α))⁻¹ with hK
  have hpt : ∀ y ∈ Metric.closedBall x ρ,
      ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤ ‖f y‖ₑ * K := by
    intro y hy
    rw [div_eq_mul_inv, hK]
    have hle : edist x y ≤ ENNReal.ofReal ρ := by
      rw [edist_dist, dist_comm]
      exact ENNReal.ofReal_le_ofReal (Metric.mem_closedBall.1 hy)
    have hinv : (edist x y ^ ((d : ℝ) - α))⁻¹ ≤ (ENNReal.ofReal ρ ^ ((d : ℝ) - α))⁻¹ := by
      have he : (d : ℝ) - α = -(α - d) := by ring
      have ht' : 0 ≤ α - d := by linarith
      rw [he, ENNReal.rpow_neg, ENNReal.rpow_neg, inv_inv, inv_inv]
      exact ENNReal.rpow_le_rpow hle ht'
    exact mul_le_mul' le_rfl hinv
  have hvol : volume (Metric.ball x ρ) = ENNReal.ofReal (ρ ^ d) * V := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have h1 : ∀ (z : Rd 0) (r : ℝ), 0 < r → Metric.ball z r = univ := fun z r hr =>
        eq_univ_of_forall fun w => by
          rw [Metric.mem_ball, Subsingleton.elim w z, dist_self]; exact hr
      rw [hV, h1 x ρ hρ, h1 0 1 one_pos, pow_zero, ENNReal.ofReal_one, one_mul]
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      rw [Measure.addHaar_ball volume x hρ.le, finrank_euclideanSpace_fin]
  have hreal : (ρ ^ ((d : ℝ) - α))⁻¹ * ρ ^ d = ρ ^ α := by
    rw [← Real.rpow_natCast ρ d, Real.rpow_def_of_pos hρ, Real.rpow_def_of_pos hρ,
      Real.rpow_def_of_pos hρ, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hKe : K * ENNReal.ofReal (ρ ^ d) = ENNReal.ofReal ρ ^ α := by
    rw [hK, ENNReal.ofReal_rpow_of_pos hρ, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hreal, ENNReal.ofReal_rpow_of_pos hρ]
  calc ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α)
      ≤ ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ * K :=
        setLIntegral_mono' measurableSet_closedBall hpt
    _ = (∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ) * K :=
        lintegral_mul_const' _ _ (by
          rw [hK]
          exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hρ) ENNReal.ofReal_ne_top).ne')
    _ ≤ (volume (Metric.ball x ρ) * localMaximalFunction (ENNReal.ofReal ρ) f x) * K := by
        gcongr
        exact lintegral_closedBall_le f x hρ le_rfl
    _ = _ := by
        rw [hvol, ← hKe]
        ring

end lemma_2_2

/-- **Lemma 2.2** ([BH93, Lemma 3]). For `α > 0` there is `C_{α,d}` such that for every cube or ball `Q`, every
`f ∈ L^1(Q)` and every `x ∈ Q`,
`∫_Q |f(y)| / |x - y|^{d-α} dy ≤ C_{α,d} (diam Q)^α M_{diam Q} f(x)`. -/
theorem lemma_2_2 (d : ℕ) {α : ℝ} (hα : 0 < α) : ∃ C : ℝ≥0, 0 < C ∧
    ∀ (Q : Set (Rd d)) (f : Rd d → ℝ), IsCubeOrBall Q → IntegrableOn f Q →
      ∀ x ∈ Q,
        ∫⁻ y in Q, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
          C * Metric.ediam Q ^ α *
            localMaximalFunction (Metric.ediam Q) f x := by
  obtain ⟨C0, hC0⟩ : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (x : Rd d) {ρ : ℝ}, 0 < ρ →
      ∫⁻ y in Metric.closedBall x ρ, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) ≤
        C * ENNReal.ofReal ρ ^ α * localMaximalFunction (ENNReal.ofReal ρ) f x := by
    by_cases h : α < d
    · exact lemma_2_2.lintegral_closedBall_kernel_le_of_lt hα h
    · exact lemma_2_2.lintegral_closedBall_kernel_le_of_ge hα (le_of_not_gt h)
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun Q f hQ _ x hx => ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : ∀ y : Rd 0, ‖f y‖ₑ / edist x y ^ (((0 : ℕ) : ℝ) - α) = 0 := fun y => by
      rw [Subsingleton.elim y x, edist_self, Nat.cast_zero, zero_sub,
        ENNReal.zero_rpow_of_neg (neg_neg_of_pos hα), ENNReal.div_top]
    simp only [hz, lintegral_zero]
    exact zero_le
  obtain ⟨hfin, -, hsub⟩ := lemma_2_2.subset_closedBall hd hQ hx
  have hρ : ENNReal.ofReal (Metric.ediam Q).toReal = Metric.ediam Q := ENNReal.ofReal_toReal hfin
  have hpos : 0 < (Metric.ediam Q).toReal := (lemma_2_2.subset_closedBall hd hQ hx).2.1
  calc ∫⁻ y in Q, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α)
      ≤ ∫⁻ y in Metric.closedBall x (Metric.ediam Q).toReal, ‖f y‖ₑ / edist x y ^ ((d : ℝ) - α) :=
        lintegral_mono_set hsub
    _ ≤ C0 * ENNReal.ofReal (Metric.ediam Q).toReal ^ α *
          localMaximalFunction (ENNReal.ofReal (Metric.ediam Q).toReal) f x := hC0 f x hpos
    _ = C0 * Metric.ediam Q ^ α * localMaximalFunction (Metric.ediam Q) f x := by rw [hρ]
    _ ≤ _ := by
        gcongr
        exact le_max_left _ _

end WeakPathwiseIto
