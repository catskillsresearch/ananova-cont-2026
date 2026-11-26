/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Occupation.NormalizedQuadraticDensity
public import WeakPathwiseIto.Appendix.GaussianMoment
public import WeakPathwiseIto.Bessel.WienerLawExists

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

namespace lemma_A_1

open ProbabilityTheory

/-- **Subgoal** (Lemma A.1 proof, step 1: `‖ρ_{n,B}‖^q_{L^q} = ∑_i |Z_i^n|^{2q} Δ_i^n`):
for a fixed path, `∫_0^T |ρ_n(t)|^q dt = ∑_i (|ω(t_{i+1}) - ω(t_i)|² / Δ_i)^q Δ_i`. -/
theorem integral_rpow_eq_sum (π : Partition T) (ω : ℝ → Rd d) {q : ℝ} (hq : 0 < q) :
    ∫ t in Icc 0 T, |normalizedQuadraticDensity π ω t| ^ q =
      ∑ i : Fin π.m, (‖ω (π.right i) - ω (π.left i)‖ ^ 2 / (π.right i - π.left i)) ^ q *
        (π.right i - π.left i) := by
  set c : Fin π.m → ℝ := fun i => ‖ω (π.right i) - ω (π.left i)‖ ^ 2 / (π.right i - π.left i)
    with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (sq_nonneg _) (by linarith [π.left_lt_right i])
  have hdisj : ∀ i j : Fin π.m, i ≠ j → ∀ t, t ∈ Ico (π.left i) (π.right i) →
      t ∉ Ico (π.left j) (π.right j) := by
    have key : ∀ i j : Fin π.m, i < j → π.right i ≤ π.left j := fun i j hij =>
      π.strictMono.monotone (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; omega)
    intro i j hij t hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [key i j h, hi.2, hj.1]
    · linarith [key j i h, hi.1, hj.2]
  have hpt : ∀ t, |normalizedQuadraticDensity π ω t| ^ q =
      ∑ i, (Ico (π.left i) (π.right i)).indicator (fun _ => c i ^ q) t := by
    intro t
    by_cases h : ∃ i, t ∈ Ico (π.left i) (π.right i)
    · obtain ⟨i0, hi0⟩ := h
      unfold normalizedQuadraticDensity
      rw [Finset.sum_eq_single i0 (fun j _ hj => indicator_of_notMem (hdisj i0 j hj.symm t hi0) _)
          (by simp),
        Finset.sum_eq_single i0 (fun j _ hj => indicator_of_notMem (hdisj i0 j hj.symm t hi0) _)
          (by simp),
        indicator_of_mem hi0, indicator_of_mem hi0, abs_of_nonneg (hc0 i0)]
    · push_neg at h
      simp [normalizedQuadraticDensity, indicator_of_notMem (h _), Real.zero_rpow hq.ne']
  have hsub : ∀ i, Ico (π.left i) (π.right i) ⊆ Icc 0 T := fun i s hs =>
    ⟨(π.t_mem _).1.trans hs.1, hs.2.le.trans (π.t_mem _).2⟩
  simp_rw [hpt]
  rw [integral_finset_sum _ fun i _ => (integrable_const _).indicator measurableSet_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.2 (hsub i), setIntegral_const, measureReal_def, Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith [π.left_lt_right i]), smul_eq_mul, mul_comm]

/-- **Subgoal** (Lemma A.1 proof, step 2a: coordinates of `B`): on `[0, T]` the canonical
process of `ofCoords x W` is `x + ∑_i W^i(t) e_i`. -/
theorem B_ofCoords (x : Rd d) (W : Fin d → ℝ≥0 → ℝ) (hW : ∀ i, Continuous (W i)) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    CanonicalWienerSpace.B (T := T) t (CanonicalWienerSpace.ofCoords x W hW) =
      x + ∑ i, W i t.toNNReal • Rd.basisVec i := by
  simp [CanonicalWienerSpace.B, ht, CanonicalWienerSpace.ofCoords]

/-- **Subgoal** (Lemma A.1 proof, step 2b: from coordinates to `N(0, I_d)`): independent
standard normal coordinates `Y^1, …, Y^d` give `∑_i Y^i e_i ∼ N(0, I_d)`. -/
theorem hasLaw_sum_smul_basisVec {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : Fin d → Ω → ℝ} (hind : iIndepFun Y Q)
    (hlaw : ∀ i, HasLaw (Y i) (gaussianReal 0 1) Q) :
    HasLaw (fun ω => ∑ i, Y i ω • Rd.basisVec i) (stdGaussian (Rd d)) Q := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 2c: `Z_i^n ∼ N(0, I_d)`): for `0 ≤ s < t ≤ T`,
`(t - s)^{-1/2} (B(t) - B(s)) ∼ N(0, I_d)` under `ℙ_x`. -/
theorem hasLaw_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    HasLaw (fun ω => (t - s) ^ (-(1 / 2 : ℝ)) •
        (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω))
      (stdGaussian (Rd d)) (CanonicalWienerSpace.P (T := T) x) := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 2d: the `Z_i^n` are independent): the increments of `B`
over the cells of a partition are independent under `ℙ_x`. -/
theorem iIndepFun_increments (x : Rd d) (π : Partition T) :
    iIndepFun (fun (i : Fin π.m) (ω : CanonicalWienerSpace d T) =>
        CanonicalWienerSpace.path ω (π.right i) - CanonicalWienerSpace.path ω (π.left i))
      (CanonicalWienerSpace.P (T := T) x) := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 3: square integrability): `‖ρ_{n,B}‖^q_{L^q}` is in
`L²(ℙ_x)`. -/
theorem memLp_two (x : Rd d) (π : Partition T) {q : ℝ} (hq : 1 < q) :
    MemLp (fun ω => ∫ t in Icc 0 T,
        |normalizedQuadraticDensity π (CanonicalWienerSpace.path ω) t| ^ q) 2
      (CanonicalWienerSpace.P (T := T) x) := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 3: mean): `𝔼_x ‖ρ_{n,B}‖^q_{L^q} = c_{q,d} T`. -/
theorem integral_eq (x : Rd d) (π : Partition T) {q : ℝ} (hq : 1 < q) :
    ∫ ω, (∫ t in Icc 0 T,
        |normalizedQuadraticDensity π (CanonicalWienerSpace.path ω) t| ^ q)
      ∂(CanonicalWienerSpace.P (T := T) x) = gaussianMoment d q * T := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 3: variance): with `b_{q,d} := Var |Z|^{2q}`,
`Var_x ‖ρ_{n,B}‖^q_{L^q} = b_{q,d} ∑_i (Δ_i^n)² ≤ b_{q,d} T |π_n|`. -/
theorem variance_le (x : Rd d) {q : ℝ} (hq : 1 < q) : ∃ b : ℝ, ∀ π : Partition T,
    variance (fun ω => ∫ t in Icc 0 T,
        |normalizedQuadraticDensity π (CanonicalWienerSpace.path ω) t| ^ q)
      (CanonicalWienerSpace.P (T := T) x) ≤ b * T * π.mesh := by
  sorry

/-- **Subgoal** (Lemma A.1 proof, step 4: Chebyshev + Borel–Cantelli): if `𝔼 X_n = c` and
`Var X_n ≤ a_n` with `∑ a_n < ∞`, then `X_n → c` almost surely. -/
theorem tendsto_ae_of_summable_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {c : ℝ} {a : ℕ → ℝ} (hX : ∀ n, MemLp (X n) 2 μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = c) (hvar : ∀ n, variance (X n) μ ≤ a n) (ha : Summable a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 c) := by
  have ha0 : ∀ n, 0 ≤ a n := fun n => (variance_nonneg _ _).trans (hvar n)
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ω ∉ {ω | (1 / ((k : ℝ) + 1)) ≤ |X n ω - c|} := by
    intro k
    set ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by positivity
    refine ae_eventually_notMem (ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (a n / ε ^ 2)) ?_
      (ENNReal.tsum_le_tsum fun n => ?_))
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (ha0 n) (sq_nonneg _))
        (ha.div_const _)]
      exact ENNReal.ofReal_ne_top
    · have := meas_ge_le_variance_div_sq (hX n) hε
      rw [hmean n] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hvar n) (sq_nonneg _)))
  filter_upwards [ae_all_iff.2 hk] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := (hω k).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [mem_setOf_eq, not_le] at this
  rw [Real.dist_eq]
  linarith

end lemma_A_1

/-- **Lemma A.1.** If `∑_{n ≥ 1} |π_n| < ∞` and `q > 1`, then
`‖ρ_{n,B}‖^q_{L^q([0,T])} → c_{q,d} T`, `ℙ_x`-almost surely. -/
theorem lemma_A_1 {π : ℕ → Partition T}
    (hπ : Summable fun n => (π (n + 1)).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x), Tendsto
      (fun n => ∫ t in Icc 0 T, |normalizedQuadraticDensity (π n) (CanonicalWienerSpace.path ω) t| ^ q)
      atTop (𝓝 (gaussianMoment d q * T)) := by
  have := CanonicalWienerSpace.isProbabilityMeasure_P (T := T) x
  obtain ⟨b, hb⟩ := lemma_A_1.variance_le x hq
  have hsum : Summable fun n => b * T * (π n).mesh :=
    ((summable_nat_add_iff (f := fun n => (π n).mesh) 1).1 hπ).mul_left (b * T)
  exact lemma_A_1.tendsto_ae_of_summable_variance (fun n => lemma_A_1.memLp_two x (π n) hq)
    (fun n => lemma_A_1.integral_eq x (π n) hq) (fun n => hb (π n)) hsum

/-- **Lemma A.1** (consequence): `sup_n ‖ρ_{n,B}‖_{L^q([0,T])} < ∞`, `ℙ_x`-almost surely. -/
theorem lemma_A_1_bounded {π : ℕ → Partition T}
    (hπ : Summable fun n => (π (n + 1)).mesh) {q : ℝ} (hq : 1 < q) (x : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) (CanonicalWienerSpace.path ω))
        (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K := by
  filter_upwards [lemma_A_1 hπ hq x] with ω hω
  obtain ⟨B, hB⟩ := hω.bddAbove_range
  refine ⟨ENNReal.ofReal (max B 0 ^ q⁻¹), ENNReal.ofReal_lt_top, fun n => ?_⟩
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [(normalizedQuadraticDensity.memLp (π n) _ _).eLpNorm_eq_integral_rpow_norm hq0
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) ?_
    (by have : 0 < q := by linarith
        positivity))
  simp only [Real.norm_eq_abs]
  exact (hB ⟨n, rfl⟩).trans (le_max_left _ _)

end WeakPathwiseIto
