/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.OccupationSeminorm
public import WeakPathwiseIto.Appendix.PotentialProfile
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Bessel.WienerLawExists
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Main.Theorem52Steps

/-! # Path-side steps of the proof of Theorem 5.2 (Appendix C)

The first partition interval is treated separately (`J_{m,n}(x₀)`), since the finite-valued
representative `g_m = (M_1 u_m)·1_{N_m^c}` need not dominate `M_1 u_m` at `B(0) = x₀`; the
modified (10)/(11) then give `‖u_m‖_{W⁰_{B,π}} ≤ C_{p,B} limsup_n ‖h_m‖^{1/p}_{n,1,B}` with a
constant independent of `m`. Also: the standard mollifier sequence, measurability and a.e.
finiteness of `M_1`, and the Brownian path facts `B(0) = x₀` and continuity. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Appendix C, `i = 0` increment: the kernel centred at `a = x₀` is kept explicit,
`∫ |f| 𝓛^{n,0} ≤ C (∫_{B̄(a,|b-a|)} |f| |z - a|^{2-d} dz + M_1 f(b) |b - a|²)`). -/
theorem lintegral_piece_le_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a b : Rd d),
    AEStronglyMeasurable f → ‖b - a‖ ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      C * ((∫⁻ x in Metric.closedBall a ‖b - a‖, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
        localMaximalFunction 1 f b * ENNReal.ofReal (‖b - a‖ ^ 2)) := by
  have hK : ∃ K : ℝ≥0, ∀ (f : Rd d → ℝ) (a : Rd d) {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
      ∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) ≤
        K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f a := by
    rcases le_or_gt d 2 with h | h
    · exact occupationSeminorm.eq_10.lintegral_kernel_le_of_le_two h
    · exact occupationSeminorm.eq_10.lintegral_kernel_le_of_three_le (by omega)
  obtain ⟨K, hK⟩ := hK
  refine ⟨(occupationConstant d).toNNReal * (1 + K), fun f a b hf hab => ?_⟩
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
    simp only [discreteOccupationDensity.piece, h, ite_false]
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
          ((∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
            K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f b) := by
        gcongr
        exact hK f b hρ hab
    _ ≤ ENNReal.ofReal (occupationConstant d) * ((1 + K) *
          ((∫⁻ x in Metric.closedBall a ρ, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ)))) +
            localMaximalFunction 1 f b * ENNReal.ofReal (ρ ^ 2))) := by
        gcongr
        rw [mul_add]
        refine add_le_add ?_ ?_
        · exact le_mul_of_one_le_left zero_le le_self_add
        · calc ↑K * ENNReal.ofReal (ρ ^ 2) * localMaximalFunction 1 f b
              = ↑K * (localMaximalFunction 1 f b * ENNReal.ofReal (ρ ^ 2)) := by ring
            _ ≤ _ := mul_le_mul' le_add_self le_rfl
    _ = _ := by
        rw [ENNReal.coe_mul, show (((occupationConstant d).toNNReal : ℝ≥0) : ℝ≥0∞) =
          ENNReal.ofReal (occupationConstant d) from rfl]
        push_cast
        ring

/-- **Subgoal** (Appendix C, (10) with the first increment kept explicit): if `g ≥ M_1 f` at the
path's partition points `ω(t_j)`, `j ≥ 1`, then
`∫ |f| 𝓛^π_ω ≤ C (J + ∑_i (g(ω(t_{i+1})) + g(ω(t_i))) |Δω_i|²)`, `J` the kernel integral at `ω(0)`
over the ball of radius `osc(ω, π)`. -/
theorem lintegral_le_maximal_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (π : Partition T) (ω : ℝ → Rd d)
    (f : Rd d → ℝ) (g : Rd d → ℝ≥0∞), ContinuousOn ω (Icc 0 T) → LocallyIntegrable f →
    pathOscillation ω π ≤ 1 →
    (∀ j : Fin (π.m + 1), j ≠ 0 → localMaximalFunction 1 f (ω (π.t j)) ≤ g (ω (π.t j))) →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x) ≤
      C * ((∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω π),
          ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ)))) +
        ∑ i : Fin π.m, (g (ω (π.right i)) + g (ω (π.left i))) *
          ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2)) := by
  obtain ⟨C₁, hC₁⟩ := occupationSeminorm.eq_10.lintegral_piece_le d
  obtain ⟨C₂, hC₂⟩ := lintegral_piece_le_first d
  refine ⟨C₁ + C₂, fun π ω f g hω hf hosc hg => ?_⟩
  have hc : 0 ≤ occupationConstant d := by unfold occupationConstant; positivity
  have hnn : ∀ (a b x : Rd d), 0 ≤ discreteOccupationDensity.piece a b x :=
    discreteOccupationDensity.piece_nonneg
  have hmeas : ∀ (a b : Rd d), Measurable (discreteOccupationDensity.piece a b) := by
    intro a b
    unfold discreteOccupationDensity.piece
    split_ifs
    · exact measurable_const
    · exact Measurable.indicator (by fun_prop) measurableSet_closedBall
  have hfm : AEStronglyMeasurable f := hf.aestronglyMeasurable
  set J := ∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω π),
    ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ))) with hJ
  set X : Fin π.m → ℝ≥0∞ := fun i => (g (ω (π.right i)) + g (ω (π.left i))) *
    ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2) with hX
  have hright : ∀ i : Fin π.m, localMaximalFunction 1 f (ω (π.right i)) ≤ g (ω (π.right i)) :=
    fun i => hg i.succ (Fin.succ_ne_zero i)
  have hterm : ∀ i : Fin π.m, ∫⁻ x, ‖f x‖ₑ *
      ENNReal.ofReal (discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x) ≤
        (if (i : ℕ) = 0 then (C₂ : ℝ≥0∞) * J else 0) + ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * X i := by
    intro i
    have hinc := (occupationSeminorm.eq_10.norm_increment_le hω π i).trans hosc
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ↓reduceIte]
      have hl : π.left i = 0 := by
        have : i.castSucc = 0 := Fin.ext (by simp [hi])
        simp [Partition.left, this, π.t_zero]
      have hJi : ∫⁻ x in Metric.closedBall (ω (π.left i)) ‖ω (π.right i) - ω (π.left i)‖,
          ‖f x‖ₑ * ENNReal.ofReal (‖x - ω (π.left i)‖ ^ (2 - (d : ℝ))) ≤ J := by
        rw [hJ, hl]
        refine lintegral_mono_set (Metric.closedBall_subset_closedBall ?_)
        have := occupationSeminorm.eq_10.norm_increment_le hω π i
        rwa [hl] at this
      calc _ ≤ (C₂ : ℝ≥0∞) * ((∫⁻ x in Metric.closedBall (ω (π.left i)) ‖ω (π.right i) - ω (π.left i)‖,
            ‖f x‖ₑ * ENNReal.ofReal (‖x - ω (π.left i)‖ ^ (2 - (d : ℝ)))) +
            localMaximalFunction 1 f (ω (π.right i)) *
              ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2)) := hC₂ f _ _ hfm hinc
        _ ≤ (C₂ : ℝ≥0∞) * (J + X i) := by
            gcongr
            simp only [hX]
            gcongr
            exact (hright i).trans le_self_add
        _ ≤ _ := by
            rw [mul_add]
            gcongr
            exact le_add_self
    · simp only [hi, ↓reduceIte, zero_add]
      have hleft : localMaximalFunction 1 f (ω (π.left i)) ≤ g (ω (π.left i)) :=
        hg i.castSucc (fun h => hi (by simpa using congrArg Fin.val h))
      calc _ ≤ (C₁ : ℝ≥0∞) * (localMaximalFunction 1 f (ω (π.right i)) +
            localMaximalFunction 1 f (ω (π.left i))) *
              ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2) := hC₁ f _ _ hfm hinc
        _ ≤ (C₁ : ℝ≥0∞) * X i := by
            rw [mul_assoc]
            simp only [hX]
            gcongr
            exact hright i
        _ ≤ _ := by
            gcongr
            exact le_self_add
  have hite : ∑ i : Fin π.m, (if (i : ℕ) = 0 then (C₂ : ℝ≥0∞) * J else 0) ≤ (C₂ : ℝ≥0∞) * J := by
    rw [← Finset.sum_filter]
    calc _ = (Finset.univ.filter fun i : Fin π.m => (i : ℕ) = 0).card • ((C₂ : ℝ≥0∞) * J) :=
          Finset.sum_const _
      _ ≤ 1 • ((C₂ : ℝ≥0∞) * J) := by
          gcongr
          refine Finset.card_le_one.2 fun a ha b hb => ?_
          simp only [Finset.mem_filter] at ha hb
          exact Fin.ext (ha.2.trans hb.2.symm)
      _ = _ := one_smul _ _
  calc ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x)
      = ∫⁻ x, ∑ i : Fin π.m, ‖f x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x) := by
        congr 1; funext x
        rw [discreteOccupationDensity, ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn _ _ x),
          Finset.mul_sum]
    _ = ∑ i : Fin π.m, ∫⁻ x, ‖f x‖ₑ *
          ENNReal.ofReal (discreteOccupationDensity.piece (ω (π.left i)) (ω (π.right i)) x) :=
        lintegral_finsetSum' _ (fun i _ =>
          hfm.enorm.mul (ENNReal.measurable_ofReal.comp (hmeas _ _)).aemeasurable)
    _ ≤ ∑ i : Fin π.m, ((if (i : ℕ) = 0 then (C₂ : ℝ≥0∞) * J else 0) +
          ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * X i) := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i : Fin π.m, (if (i : ℕ) = 0 then (C₂ : ℝ≥0∞) * J else 0) +
          ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * ∑ i, X i := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (C₂ : ℝ≥0∞) * J + ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * ∑ i, X i := by gcongr
    _ ≤ ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * J + ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * ∑ i, X i := by
        gcongr
        exact le_add_self
    _ = _ := by rw [← mul_add]

/-- **Subgoal** (Appendix C, `‖z - x₀‖^{2-d} ≤ ν(‖z - x₀‖)` on small balls). -/
theorem rpow_le_potentialProfile {r : ℝ} (hr1 : r ≤ 1) :
    r ^ (2 - (d : ℝ)) ≤ potentialProfile d r := by
  unfold potentialProfile
  split_ifs with h1 h2
  · subst h1; norm_num; exact hr1
  · subst h2
    norm_num
  · exact le_rfl

/-- **Subgoal** (Appendix C, `J_{m,n}(x₀) → 0`): if `∫ |f(z)| ν(|z - x₀|) dz < ∞` and the radii
shrink to `0`, the kernel integrals over `B̄(x₀, ρ_n)` tend to `0`. -/
theorem tendsto_lintegral_closedBall_kernel {f : Rd d → ℝ}
    {x₀ : Rd d} (hf : ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) < ⊤)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ (ρ n),
      ‖f x‖ₑ * ENNReal.ofReal (‖x - x₀‖ ^ (2 - (d : ℝ)))) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h0 : ∀ x : Rd 0, ‖f x‖ₑ * ENNReal.ofReal (‖x - x₀‖ ^ (2 - ((0 : ℕ) : ℝ))) = 0 := by
      intro x
      rw [Subsingleton.elim x x₀, sub_self, norm_zero]
      norm_num
    simp_rw [h0, lintegral_zero]
    exact tendsto_const_nhds
  -- `d ≥ 1`: dominate by the `ν`-weighted integrand on shrinking balls
  have hvol : Tendsto (fun n => volume (Metric.closedBall x₀ (max (ρ n) 0))) atTop (𝓝 0) := by
    have hm : Tendsto (fun n => max (ρ n) 0) atTop (𝓝 0) := by
      simpa using hρ.max (tendsto_const_nhds (x := (0 : ℝ)))
    have hc : Tendsto (fun n => ENNReal.ofReal (max (ρ n) 0 ^ d)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow d).tendsto 0 |>.comp hm)
      rw [zero_pow hd.ne', ENNReal.ofReal_zero] at this
      exact this
    have := ENNReal.Tendsto.mul_const hc (Or.inr (measure_ball_lt_top (μ := volume)
      (x := (0 : Rd d)) (r := 1)).ne)
    rw [zero_mul] at this
    refine this.congr fun n => ?_
    rw [Measure.addHaar_closedBall _ _ (le_max_right _ _), finrank_euclideanSpace_fin]
  have hlim := tendsto_setLIntegral_zero hf.ne (μ := volume) hvol
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hρ.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  calc ∫⁻ x in Metric.closedBall x₀ (ρ n), ‖f x‖ₑ * ENNReal.ofReal (‖x - x₀‖ ^ (2 - (d : ℝ)))
      ≤ ∫⁻ x in Metric.closedBall x₀ (ρ n), ‖f x‖ₑ * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => ?_)
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        gcongr
        exact rpow_le_potentialProfile (hx.trans hn)
    _ ≤ _ := lintegral_mono_set (Metric.closedBall_subset_closedBall (le_max_left _ _))

/-- **Subgoal** (Appendix C, (11) with the first increment kept explicit: Hölder and
`sup_n ‖ρ_{n,ω}‖_{L^q} < ∞`). The constant depends only on `(π, ω, p)`, not on `f` or `g`. -/
theorem le_limsup_discreteSeminorm_first {p q : ℝ} (hpq : p.HolderConjugate q)
    (π : ℕ → Partition T) (ω : ℝ → Rd d) (hω : ContinuousOn ω (Icc 0 T))
    (hosc : pathOscillation.Vanishes ω π)
    (hρ : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) ω) (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : Rd d → ℝ) (g : Rd d → ℝ≥0∞), LocallyIntegrable f →
      (∀ n, ∀ j : Fin ((π n).m + 1), j ≠ 0 →
        localMaximalFunction 1 f (ω ((π n).t j)) ≤ g (ω ((π n).t j))) →
      Tendsto (fun n => ∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω (π n)),
          ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ)))) atTop (𝓝 0) →
      occupationSeminorm π ω f ≤ C * limsup (fun n => discreteSeminorm (π n) p g ω) atTop := by
  obtain ⟨C10, hC10⟩ := lintegral_le_maximal_first (T := T) d
  obtain ⟨K, hKtop, hK⟩ := hρ
  have hp1 : 1 < p := hpq.lt
  have hq : 0 < q := hpq.symm.pos
  have h2 : (2 : ℝ≥0∞) ^ ((p - 1) / p) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (div_nonneg (by linarith) (by linarith)) ENNReal.ofNat_ne_top
  have hCt : (C10 : ℝ≥0∞) * 2 ^ ((p - 1) / p) * K < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top h2) hKtop
  refine ⟨(C10 : ℝ≥0∞) * 2 ^ ((p - 1) / p) * K, hCt, fun f g hf hg hJ => ?_⟩
  have hev : ∀ᶠ n in atTop, pathOscillation ω (π n) ≤ 1 := hosc.eventually (Iic_mem_nhds one_pos)
  set J := fun n => ∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω (π n)),
    ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ))) with hJdef
  unfold occupationSeminorm
  calc limsup (fun n => ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity (π n) ω x)) atTop
      ≤ limsup (fun n => (C10 : ℝ≥0∞) * J n +
          (C10 : ℝ≥0∞) * 2 ^ ((p - 1) / p) * K * discreteSeminorm (π n) p g ω) atTop := by
        refine limsup_le_limsup (hev.mono fun n hn => ?_)
        calc _ ≤ (C10 : ℝ≥0∞) * (J n + ∑ i : Fin (π n).m, (g (ω ((π n).right i)) +
              g (ω ((π n).left i))) *
                ENNReal.ofReal (‖ω ((π n).right i) - ω ((π n).left i)‖ ^ 2)) :=
              hC10 (π n) ω f g hω hf hn (hg n)
          _ ≤ (C10 : ℝ≥0∞) * (J n + (2 ^ ((p - 1) / p) * discreteSeminorm (π n) p g ω) * K) := by
              gcongr
              exact (occupationSeminorm.eq_11.sum_le_holder hpq (π n) ω _).trans
                (mul_le_mul' (occupationSeminorm.eq_11.sum_rpow_le hp1.le _ _ _)
                  ((occupationSeminorm.eq_11.sum_rpow_le_eLpNorm hq _ _).trans (hK n)))
          _ = _ := by ring
    _ = _ := by
        have hJ' : Tendsto (fun n => (C10 : ℝ≥0∞) * J n) atTop (𝓝 0) := by
          simpa using ENNReal.Tendsto.const_mul hJ (Or.inr ENNReal.coe_ne_top)
        exact (ENNReal.limsup_add_of_left_tendsto_zero hJ' _).trans
          (ENNReal.limsup_const_mul_of_ne_top hCt.ne)

/-- **Subgoal** (Appendix C, `‖g‖_{n,p,B} = ‖g^p‖^{1/p}_{n,1,B}` for `g ≥ 0`). -/
theorem discreteSeminorm_enorm_rpow {p : ℝ} (hp : 0 < p) (π : Partition T) {g : Rd d → ℝ}
    (hg : 0 ≤ g) (ω : ℝ → Rd d) :
    discreteSeminorm π p (fun x => ‖g x‖ₑ) ω =
      discreteSeminorm π 1 (fun x => ‖g x ^ p‖ₑ) ω ^ (1 / p) := by
  have he : ∀ x, ‖g x ^ p‖ₑ = ‖g x‖ₑ ^ p := by
    intro x
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hg x) p), Real.enorm_eq_ofReal (hg x),
      ENNReal.ofReal_rpow_of_nonneg (hg x) hp.le]
  simp only [discreteSeminorm, he, ENNReal.rpow_one, div_one]

/-- **Subgoal** (Appendix C, `M_1 f` is Borel: `x ↦ c ν(B(x, r))` is lower semicontinuous for a
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

/-- **Subgoal** (Appendix C, `M_1 f` is Borel: a supremum of lower semicontinuous ball averages). -/
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

/-- **Subgoal** (Appendix C, `N_m = {M_1 u_m = ∞}` is Lebesgue-null: `M_1 u_m ∈ L^p`). -/
theorem ae_localMaximalFunction_lt_top {p : ℝ} (hp : 1 < p) {f : Rd d → ℝ}
    (hf : MemLp f (ENNReal.ofReal p)) : ∀ᵐ x, localMaximalFunction 1 f x < ⊤ := by
  obtain ⟨C, hC⟩ := eLpNorm_maximal_le (d := d) hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hm := measurable_localMaximalFunction (d := d) f
  have hlt : eLpNorm (localMaximalFunction 1 f) (ENNReal.ofReal p) volume < ⊤ :=
    (hC f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.eLpNorm_lt_top)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith)] at hlt
  have hint : ∫⁻ x, ‖localMaximalFunction 1 f x‖ₑ ^ p ≠ ⊤ :=
    ((ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0 : ℝ) < 1 / p)).1 hlt).ne
  filter_upwards [ae_lt_top' (hm.enorm.pow_const p).aemeasurable hint] with x hx
  rw [enorm_eq_self] at hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (by linarith)).1 hx

/-- **Subgoal** (Appendix C, `‖h_m‖_{L^1} = ‖g_m‖^p_{L^p} → 0`). -/
theorem tendsto_eLpNorm_rpow_one {p : ℝ} (hp : 0 < p) {g : ℕ → Rd d → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hgm : ∀ m, Measurable (g m))
    (hlim : Tendsto (fun m => eLpNorm (g m) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun x => g m x ^ p) 1 volume) atTop (𝓝 0) := by
  have heq : ∀ m, eLpNorm (fun x => g m x ^ p) 1 volume =
      eLpNorm (g m) (ENNReal.ofReal p) volume ^ p := by
    intro m
    have h0 : ENNReal.ofReal p ≠ 0 := by rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hg m x) p), Real.enorm_eq_ofReal (hg m x),
      ENNReal.ofReal_rpow_of_nonneg (hg m x) hp.le]
    · exact (hgm m).aestronglyMeasurable
    · exact ((hgm m).pow_const p).aestronglyMeasurable
  simp_rw [heq]
  have := (ENNReal.continuous_rpow_const (y := p)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos hp] at this
  exact this.comp hlim

/-- **Subgoal** (Appendix C, standard mollifier `η_m(x) = m^d η(m x)`). -/
theorem exists_mollifier (d : ℕ) : ∃ ψ : ℕ → Rd d → ℝ,
    (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
    (∀ n x, 0 ≤ ψ n x) ∧ (∀ n, ∫ x, ψ n x = 1) ∧
    (∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) ∧
    ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d := by
  let φ : ContDiffBump (0 : Rd d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  set η : Rd d → ℝ := φ.normed volume with hη
  have hsupp : ∀ n : ℕ, ∀ x : Rd d, η (((n : ℝ) + 1) • x) ≠ 0 → ‖x‖ < 1 / ((n : ℝ) + 1) := by
    intro n x hx
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : ((n : ℝ) + 1) • x ∈ Metric.ball (0 : Rd d) 1 := by
      rw [← φ.support_normed_eq (μ := volume)]; exact hx
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hn] at this
    rw [lt_div_iff₀ hn]; linarith
  refine ⟨fun n x => ((n : ℝ) + 1) ^ d * η (((n : ℝ) + 1) • x), fun n => ?_, fun n => ?_,
    fun n x => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact contDiff_const.mul (φ.contDiff_normed.comp (contDiff_const_smul _))
  · refine HasCompactSupport.intro' (isCompact_closedBall (0 : Rd d) (1 / ((n : ℝ) + 1)))
      Metric.isClosed_closedBall fun x hx => ?_
    by_contra h
    have h2 : η (((n : ℝ) + 1) • x) ≠ 0 := fun h0 => h (by simp only [h0, mul_zero])
    exact hx (Metric.mem_closedBall.2 (by rw [dist_zero_right]; exact (hsupp n x h2).le))
  · exact mul_nonneg (by positivity) (φ.nonneg_normed _)
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin,
      φ.integral_normed, smul_eq_mul, mul_one, abs_inv, abs_of_pos (pow_pos hn d),
      mul_inv_cancel₀ (pow_pos hn d).ne']
  · intro x hx
    have h2 : η (((n : ℝ) + 1) • x) ≠ 0 := fun h0 => hx (by simp only [h0, mul_zero])
    rw [Metric.mem_ball, dist_zero_right]; exact hsupp n x h2
  · refine ⟨1 / volume.real (Metric.closedBall (0 : Rd d) φ.rIn), fun n x => ?_⟩
    calc ((n : ℝ) + 1) ^ d * η (((n : ℝ) + 1) • x)
        ≤ ((n : ℝ) + 1) ^ d * (1 / volume.real (Metric.closedBall (0 : Rd d) φ.rIn)) :=
          mul_le_mul_of_nonneg_left (φ.normed_le_div_measure_closedBall_rIn (μ := volume) _)
            (pow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) d)
      _ = _ := mul_comm _ _

/-- **Subgoal** (Appendix C, `u_m ∈ L^1` for Lemma B.1): for `G ∈ C²_b ∩ W^{2,1}` and `F ∈ W^{2,1}`
with weak Hessian `H`, `‖∇²G - H‖` is integrable. -/
theorem integrable_norm_hessian_sub {F G : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (hG : ContDiffBounded 2 G)
    (hG1 : MemW 2 1 G) : Integrable fun x => ‖smoothHessian G x - H x‖ := by
  sorry

/-- **Subgoal** (Appendix C, `B(0) = x₀`, `ℙ_{x₀}`-almost surely). -/
theorem ae_path_zero (hT : 0 ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), CanonicalWienerSpace.path ω 0 = x₀ := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, -, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x₀
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hmeas : MeasurableSet {ω : CanonicalWienerSpace d T | CanonicalWienerSpace.path ω 0 = x₀} := by
    have : {ω : CanonicalWienerSpace d T | CanonicalWienerSpace.path ω 0 = x₀} =
        (fun ω : CanonicalWienerSpace d T => ω ⟨0, h0⟩) ⁻¹' {x₀} := by
      ext ω
      simp [CanonicalWienerSpace.path, CanonicalWienerSpace.B, h0]
    rw [this]
    exact (continuous_eval_const (⟨0, h0⟩ : Icc (0:ℝ) T)).measurable (measurableSet_singleton x₀)
  have hae : AEMeasurable (fun ω' => CanonicalWienerSpace.ofCoords (T := T) x₀
      (fun i t => W i t ω') fun i => hW i ω') Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun s => ?_
    simp only [CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  rw [hP, ae_map_iff hae hmeas]
  have hz : ∀ᵐ ω' ∂Q, ∀ i, W i 0 ω' = 0 :=
    ae_all_iff.2 fun i => (hB i).toIsPreBrownianReal.eval_zero_ae_eq_zero
  filter_upwards [hz] with ω' hω'
  simp [CanonicalWienerSpace.path, CanonicalWienerSpace.B, CanonicalWienerSpace.ofCoords, h0, hω']

/-- **Subgoal** (Appendix C, Brownian paths are continuous on `[0, T]`). -/
theorem continuousOn_path (ω : CanonicalWienerSpace d T) :
    ContinuousOn (CanonicalWienerSpace.path ω) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Icc 0 T).domRestrict (CanonicalWienerSpace.path ω) = ω := by
    funext t
    simp [Set.domRestrict, CanonicalWienerSpace.path, CanonicalWienerSpace.B, t.2]
  rw [h]
  exact ω.continuous

end theorem_5_2

end WeakPathwiseIto
