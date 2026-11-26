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
  have h1 := hind.hasLaw_pi hlaw
  have h2 : HasLaw (fun v : Fin d → ℝ => ∑ i, v i • Rd.basisVec i) (stdGaussian (Rd d))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    refine ⟨(continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul continuous_const).measurable.aemeasurable, ?_⟩
    rw [stdGaussian_eq_map_pi_orthonormalBasis (EuclideanSpace.basisFun (Fin d) ℝ)]
    congr 1
    funext v
    simp [Rd.basisVec, EuclideanSpace.basisFun_apply]
  exact h2.comp h1

/-- **Subgoal** (Lemma A.1 proof, step 2c: `Z_i^n ∼ N(0, I_d)`): for `0 ≤ s < t ≤ T`,
`(t - s)^{-1/2} (B(t) - B(s)) ∼ N(0, I_d)` under `ℙ_x`. -/
theorem hasLaw_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    HasLaw (fun ω => (t - s) ^ (-(1 / 2 : ℝ)) •
        (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω))
      (stdGaussian (Rd d)) (CanonicalWienerSpace.P (T := T) x) := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x
  set g : Ω' → CanonicalWienerSpace d T := fun ω' =>
    CanonicalWienerSpace.ofCoords x (fun i t => W i t ω') fun i => hW i ω' with hgdef
  have hg : AEMeasurable g Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [hgdef, CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  have htI : t ∈ Icc 0 T := ⟨hs.trans hst.le, ht⟩
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  set c : ℝ := (t - s) ^ (-(1 / 2 : ℝ)) with hc
  have hBm : ∀ r ∈ Icc 0 T, Measurable (CanonicalWienerSpace.B (d := d) (T := T) r) := by
    intro r hr
    have : CanonicalWienerSpace.B (d := d) (T := T) r = fun ω => ω ⟨r, hr⟩ := by
      funext ω; simp [CanonicalWienerSpace.B, hr]
    rw [this]
    exact ContinuousMap.measurable_eval _
  have hF : Measurable fun ω : CanonicalWienerSpace d T =>
      c • (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) :=
    ((hBm t htI).sub (hBm s hsI)).const_smul c
  set Y : Fin d → Ω' → ℝ := fun i ω' => c * (W i t.toNNReal ω' - W i s.toNNReal ω') with hY
  have hcomp : (fun ω => c • (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)) ∘ g =
      fun ω' => ∑ i, Y i ω' • Rd.basisVec i := by
    funext ω'
    simp only [Function.comp, hgdef]
    rw [B_ofCoords _ _ _ htI, B_ofCoords _ _ _ hsI, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, smul_smul]
  have hYind : iIndepFun Y Q :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => c * (f t.toNNReal - f s.toNNReal))
      fun _ => measurable_const.mul ((measurable_pi_apply _).sub (measurable_pi_apply _))
  have hYlaw : ∀ i, HasLaw (Y i) (gaussianReal 0 1) Q := by
    intro i
    have h := gaussianReal_const_mul ((hB i).toIsPreBrownianReal.hasLaw_sub t.toNNReal s.toNNReal) c
    have hv : (NNReal.mk (c ^ 2) (sq_nonneg _)) * nndist (t.toNNReal : ℝ) (s.toNNReal : ℝ) = 1 := by
      ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nndist, Real.dist_eq,
        Real.coe_toNNReal _ htI.1, Real.coe_toNNReal _ hs, NNReal.coe_one]
      rw [abs_of_pos (by linarith), hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
      rw [Real.rpow_neg_one]
      field_simp [show t - s ≠ 0 by linarith]
    rw [mul_zero] at h
    convert h using 2
    exact hv.symm
  have hlaw := hasLaw_sum_smul_basisVec hYind hYlaw
  rw [hP]
  refine ⟨hF.aemeasurable, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hg, hcomp]
  exact hlaw.map_eq

/-- **Subgoal** (Lemma A.1 proof, step 2d-i: jointly Gaussian): for independent real Brownian
motions `W^1, …, W^d` and times `t_0 ≤ ⋯ ≤ t_m`, all coordinate increments
`W^i(t_{k+1}) - W^i(t_k)` are jointly Gaussian. -/
theorem hasGaussianLaw_coordIncrements {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Fin d → ℝ≥0 → Ω' → ℝ} (hB : ∀ i, IsBrownianReal (W i) Q)
    (hind : iIndepFun (fun i ω' t => W i t ω') Q) {m : ℕ} (t : Fin (m + 1) → ℝ≥0) :
    HasGaussianLaw (fun ω' (k : Fin m) (i : Fin d) =>
      W i (t k.succ) ω' - W i (t k.castSucc) ω') Q := by
  have hi : ∀ i, HasGaussianLaw (fun ω' (k : Fin m) =>
      W i (t k.succ) ω' - W i (t k.castSucc) ω') Q := fun i =>
    (hB i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_increments
  have hind' : iIndepFun (fun i ω' (k : Fin m) =>
      W i (t k.succ) ω' - W i (t k.castSucc) ω') Q :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) (k : Fin m) => f (t k.succ) - f (t k.castSucc))
      fun _ => by fun_prop
  have hJ := hind'.hasGaussianLaw hi
  let L : (Fin d → Fin m → ℝ) →L[ℝ] (Fin m → Fin d → ℝ) :=
    ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin m → ℝ) i)
  exact hJ.map L

/-- **Subgoal** (Lemma A.1 proof, step 2d-ii: uncorrelated): increments over different cells are
uncorrelated (same coordinate: independent increments; different coordinates: independence). -/
theorem covariance_coordIncrements_eq_zero {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Fin d → ℝ≥0 → Ω' → ℝ} (hB : ∀ i, IsBrownianReal (W i) Q)
    (hind : iIndepFun (fun i ω' t => W i t ω') Q) {m : ℕ} {t : Fin (m + 1) → ℝ≥0}
    (ht : Monotone t) {k l : Fin m} (hkl : k ≠ l) (i j : Fin d) :
    cov[fun ω' => W i (t k.succ) ω' - W i (t k.castSucc) ω',
      fun ω' => W j (t l.succ) ω' - W j (t l.castSucc) ω'; Q] = 0 := by
  have hmem : ∀ (i : Fin d) (a b : ℝ≥0), MemLp (fun ω' => W i a ω' - W i b ω') 2 Q :=
    fun i a b => ((hB i).toIsPreBrownianReal.hasLaw_sub a b).hasGaussianLaw.memLp_two
  by_cases hij : i = j
  · subst hij
    exact (((hB i).toIsPreBrownianReal.hasIndepIncrements m t ht).indepFun hkl).covariance_eq_zero
      (hmem _ _ _) (hmem _ _ _)
  · have h := (hind.indepFun hij).comp
      (φ := fun f : ℝ≥0 → ℝ => f (t k.succ) - f (t k.castSucc))
      (ψ := fun f : ℝ≥0 → ℝ => f (t l.succ) - f (t l.castSucc))
      (by fun_prop) (by fun_prop)
    exact h.covariance_eq_zero (hmem _ _ _) (hmem _ _ _)

/-- **Subgoal** (Lemma A.1 proof, step 2d-iii: transport to `ℙ_x = Q ∘ g⁻¹`): independence of
`f_i ∘ g` under `Q` gives independence of `f_i` under the image measure. -/
theorem iIndepFun_map_of_comp {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {g : Ω' → Ω} (hg : AEMeasurable g Q) {f : ∀ i, Ω → β i}
    (hf : ∀ i, Measurable (f i)) (h : iIndepFun (fun i => f i ∘ g) Q) :
    iIndepFun f (Q.map g) := by
  have : IsProbabilityMeasure (Q.map g) := (Measure.isProbabilityMeasure_map_iff hg).2 inferInstance
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hf i).aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (measurable_pi_iff.2 fun i => hf i).aemeasurable hg]
  simp_rw [AEMeasurable.map_map_of_aemeasurable (hf _).aemeasurable hg]
  exact h.map_fun_eq_pi_map fun i => (hf i).comp_aemeasurable hg

/-- **Subgoal** (Lemma A.1 proof, step 2d: the `Z_i^n` are independent): the increments of `B`
over the cells of a partition are independent under `ℙ_x`. -/
theorem iIndepFun_increments (x : Rd d) (π : Partition T) :
    iIndepFun (fun (i : Fin π.m) (ω : CanonicalWienerSpace d T) =>
        CanonicalWienerSpace.path ω (π.right i) - CanonicalWienerSpace.path ω (π.left i))
      (CanonicalWienerSpace.P (T := T) x) := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x
  set g : Ω' → CanonicalWienerSpace d T := fun ω' =>
    CanonicalWienerSpace.ofCoords x (fun i t => W i t ω') fun i => hW i ω' with hgdef
  have hg : AEMeasurable g Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [hgdef, CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  have hBm : ∀ r ∈ Icc 0 T, Measurable (CanonicalWienerSpace.B (d := d) (T := T) r) := by
    intro r hr
    have : CanonicalWienerSpace.B (d := d) (T := T) r = fun ω => ω ⟨r, hr⟩ := by
      funext ω; simp [CanonicalWienerSpace.B, hr]
    rw [this]
    exact ContinuousMap.measurable_eval _
  set t' : Fin (π.m + 1) → ℝ≥0 := fun k => (π.t k).toNNReal with ht'def
  have ht' : Monotone t' := fun a b hab => Real.toNNReal_le_toNNReal (π.strictMono.monotone hab)
  have hX := (hasGaussianLaw_coordIncrements hB hind t').iIndepFun_of_covariance_eval
    fun k l hkl i j => covariance_coordIncrements_eq_zero hB hind ht' hkl i j
  have hY := hX.comp (fun _ (v : Fin d → ℝ) => ∑ i, v i • Rd.basisVec i) fun _ => by fun_prop
  rw [hP]
  refine iIndepFun_map_of_comp hg (fun k => ?_) ?_
  · exact (hBm _ (π.t_mem _)).sub (hBm _ (π.t_mem _))
  · convert hY using 1
    funext k ω'
    simp only [Function.comp, hgdef, CanonicalWienerSpace.path]
    rw [B_ofCoords (t := π.right k) _ _ _ (π.t_mem k.succ),
      B_ofCoords (t := π.left k) _ _ _ (π.t_mem k.castSucc),
      add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    rfl

/-- **Subgoal** (Lemma A.1 proof, step 3: Gaussian moments are finite): for `p ≥ 0`,
`z ↦ |z|^p` is in every `L^r(N(0, I_d))`, `r < ∞`. -/
theorem memLp_norm_rpow_stdGaussian {p : ℝ} (hp : 0 ≤ p) {r : ℝ≥0∞} (hr : r ≠ ∞) :
    MemLp (fun z : Rd d => ‖z‖ ^ p) r (stdGaussian (Rd d)) := by
  rcases hp.eq_or_lt with rfl | hp0
  · simp only [Real.rpow_zero]
    exact memLp_const 1
  have hq0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have h := (IsGaussian.memLp_id (stdGaussian (Rd d)) (ENNReal.ofReal p * r)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr)).norm_rpow_div (ENNReal.ofReal p)
  rw [ENNReal.toReal_ofReal hp, mul_comm, ENNReal.mul_div_cancel_right hq0 ENNReal.ofReal_ne_top] at h
  exact h

/-- **Subgoal** (Lemma A.1 proof, step 1 in terms of `Z_i^n`): along `ℙ_x`-paths,
`‖ρ_{n,B}‖^q_{L^q} = ∑_i |Z_i^n|^{2q} Δ_i^n` with `Z_i^n = (Δ_i^n)^{-1/2}(B(t_{i+1}) - B(t_i))`. -/
theorem integral_rpow_eq_sum_norm (π : Partition T) {q : ℝ} (hq : 0 < q)
    (ω : CanonicalWienerSpace d T) :
    ∫ t in Icc 0 T, |normalizedQuadraticDensity π (CanonicalWienerSpace.path ω) t| ^ q =
      ∑ i : Fin π.m, ‖(π.right i - π.left i) ^ (-(1 / 2 : ℝ)) •
          (CanonicalWienerSpace.B (π.right i) ω - CanonicalWienerSpace.B (π.left i) ω)‖ ^ (2 * q) *
        (π.right i - π.left i) := by
  rw [integral_rpow_eq_sum π (CanonicalWienerSpace.path ω) hq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set Δ := π.right i - π.left i with hΔ
  have hΔ0 : 0 < Δ := sub_pos.2 (π.left_lt_right i)
  set v := CanonicalWienerSpace.B (π.right i) ω - CanonicalWienerSpace.B (π.left i) ω with hv
  change (‖v‖ ^ 2 / Δ) ^ q = _
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hΔ0.le _),
    Real.mul_rpow (Real.rpow_nonneg hΔ0.le _) (norm_nonneg _), ← Real.rpow_mul hΔ0.le,
    Real.rpow_mul (norm_nonneg _), Real.div_rpow (sq_nonneg _) hΔ0.le, Real.rpow_two,
    show -(1 / 2 : ℝ) * (2 * q) = -q by ring, Real.rpow_neg hΔ0.le, div_eq_inv_mul]

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
  simp only [not_le] at this
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
