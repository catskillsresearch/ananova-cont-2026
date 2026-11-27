/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.WienerLawExists
public import WeakPathwiseIto.Main.IsItoIntegral

/-! # Steps of the proof of Proposition 5.3

Route A (approved): a direct `d`-dimensional elementary Itô calculus for the canonical process
`B` under `ℙ_x` and its natural filtration.

* **P53.A** (this file, first part): `B` under `ℙ_x` has increments independent of the past
  `𝓕_s = σ(B(v) : v ≤ s)`, with covariance `(t - s) I`; hence the elementary isometry inputs
  `E⟨ξ, B_t - B_s⟩² = (t - s) E|ξ|²` and the vanishing of cross terms.
* **P53.B**: elementary isometry and localisation (stubs below); limit in probability.
* **P53.C**: `∇F_m(B) → G(B)` in `L²(ds)` in probability, off a polar set.
* **P53.D**: Riemann sums along `π` converge in probability to the Itô integral.
* **P53.E**: assembly (`proposition_5_3`). -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace proposition_5_3

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (P53.A, helper): a two-member family indexed by `Bool` is mutually independent
as soon as its two members are independent. -/
theorem iIndepFun_bool {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : Type*} [MeasurableSpace β] {f : Bool → Ω → β} (h : IndepFun (f false) (f true) μ) :
    iIndepFun f μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have key : ∀ S : Finset Bool, S = ∅ ∨ S = {false} ∨ S = {true} ∨ S = {false, true} := by
    decide
  have hS := key S
  rcases hS with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp only [Finset.mem_insert, Finset.mem_singleton, iInter_iInter_eq_or_left,
      iInter_iInter_eq_left, Finset.prod_insert (by decide : false ∉ ({true} : Finset Bool)),
      Finset.prod_singleton]
    exact h.measure_inter_preimage_eq_mul _ _ (hs false (by simp)) (hs true (by simp))

/-- **Subgoal** (P53.A, independent Brownian coordinates: the joint past is independent of the
joint future increments). For independent real Brownian motions `W^1, …, W^d` and `s ≥ 0`, the
past `(W^i_v)_{i, v ≤ s}` is independent of the shifted increments `(W^i_{s+u} - W^i_s)_{i, u}`. -/
theorem indepFun_coords_past_shift {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Fin d → ℝ≥0 → Ω' → ℝ}
    (hB : ∀ i, IsBrownianReal (W i) Q)
    (hind : iIndepFun (fun i ω' t => W i t ω') Q) (s : ℝ≥0) :
    IndepFun (fun ω' (i : Fin d) (v : Iic s) => W i v ω')
      (fun ω' (i : Fin d) (u : ℝ≥0) => W i (s + u) ω' - W i s ω') Q := by
  have hae : ∀ i, AEMeasurable (fun ω' t => W i t ω') Q := fun i => (hB i).aemeasurable
  set Y : Fin d → Ω' → ℝ≥0 → ℝ := fun i => (hae i).mk _ with hYdef
  have hY : ∀ i, Measurable (Y i) := fun i => (hae i).measurable_mk
  have hYe : ∀ i, (fun ω' t => W i t ω') =ᵐ[Q] Y i := fun i => (hae i).ae_eq_mk
  set pastF : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w v => w (min v s) with hpastF
  set shiftF : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w u => w (s + u) - w s with hshiftF
  have hpm : Measurable pastF := by rw [hpastF]; fun_prop
  have hsm : Measurable shiftF := by rw [hshiftF]; fun_prop
  set piece : Bool → (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun b => cond b shiftF pastF with hpiece
  have hpiecem : ∀ b, Measurable (piece b) := fun b => by cases b <;> simpa [hpiece]
  set X : Fin d → Bool → Ω' → ℝ≥0 → ℝ := fun i b ω => piece b (Y i ω) with hX
  have mX : ∀ i b, Measurable (X i b) := fun i b => (hpiecem b).comp (hY i)
  have h1 : iIndepFun (fun i ω => (X i · ω)) Q := by
    have h0 : iIndepFun Y Q := hind.congr hYe
    exact h0.comp (fun _ w b => piece b w) fun _ => measurable_pi_iff.2 hpiecem
  have h2 : ∀ i, iIndepFun (X i) Q := by
    intro i
    refine iIndepFun_bool ?_
    have hsh := (hB i).toIsPreBrownianReal.indepFun_shift s
    have hc := hsh.symm.comp
      (φ := fun (g : Iic s → ℝ) (v : ℝ≥0) => g ⟨min v s, mem_Iic.2 (min_le_right _ _)⟩)
      (ψ := id) (measurable_pi_iff.2 fun _ => measurable_pi_apply _) measurable_id
    refine hc.congr ?_ ?_
    · filter_upwards [hYe i] with ω hω
      funext v
      simp [X, piece, pastF, ← hω]
    · filter_upwards [hYe i] with ω hω
      funext u
      simp [X, piece, shiftF, ← hω]
  have hU := iIndepFun_uncurry' mX h1 h2
  have hdisj : Disjoint ((Finset.univ : Finset (Fin d)) ×ˢ ({false} : Finset Bool))
      ((Finset.univ : Finset (Fin d)) ×ˢ ({true} : Finset Bool)) := by
    rw [Finset.disjoint_left]; rintro ⟨i, b⟩ h1 h2; simp at h1 h2; simp [h1] at h2
  have hF := hU.indepFun_finset _ _ hdisj (fun p => mX p.1 p.2)
  have hc := hF.comp
    (φ := fun (f : ((Finset.univ : Finset (Fin d)) ×ˢ ({false} : Finset Bool) :
        Finset (Fin d × Bool)) → ℝ≥0 → ℝ)
      (i : Fin d) (v : Iic s) => f ⟨(i, false), by simp⟩ v)
    (ψ := fun (f : ((Finset.univ : Finset (Fin d)) ×ˢ ({true} : Finset Bool) :
        Finset (Fin d × Bool)) → ℝ≥0 → ℝ)
      (i : Fin d) (u : ℝ≥0) => f ⟨(i, true), by simp⟩ u) (by fun_prop) (by fun_prop)
  have hall : ∀ᵐ ω ∂Q, ∀ i, (fun t => W i t ω) = Y i ω := ae_all_iff.2 hYe
  refine hc.congr ?_ ?_
  · filter_upwards [hall] with ω hω
    funext i v
    simp only [Function.comp_apply, X, piece, Bool.cond_false, pastF, ← hω i,
      min_eq_left (mem_Iic.1 v.2)]
  · filter_upwards [hall] with ω hω
    funext i u
    simp only [Function.comp_apply, X, piece, Bool.cond_true, shiftF, ← hω i]

/-- **Subgoal** (P53.A, helper): independence transfers to an image measure: if `f ∘ G` and
`g ∘ G` are independent under `Q`, then `f` and `g` are independent under `Q.map G`. -/
theorem indepFun_map_of_comp {Ω Ω' β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace β'] {Q : Measure Ω'} {G : Ω' → Ω} (hG : AEMeasurable G Q)
    {f : Ω → β} {g : Ω → β'} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun (f ∘ G) (g ∘ G) Q) : IndepFun f g (Q.map G) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro A C hA hC
  rw [Measure.map_apply_of_aemeasurable hG ((hf hA).inter (hg hC)),
    Measure.map_apply_of_aemeasurable hG (hf hA), Measure.map_apply_of_aemeasurable hG (hg hC)]
  exact h A C hA hC

/-- **Subgoal** (P53.A, helper): the canonical coordinate `B(t)` is measurable on `Ω`. -/
theorem measurable_B (t : ℝ) : Measurable (CanonicalWienerSpace.B (d := d) (T := T) t) := by
  unfold CanonicalWienerSpace.B
  by_cases h : t ∈ Icc 0 T
  · simp only [h, dite_true]; exact ContinuousMap.measurable_eval _
  · simp only [h, dite_false]; exact measurable_const

/-- **Subgoal** (P53.A, canonical space): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, the past path
`(B(v))_{v ≤ s}` is independent of the increment `B(t) - B(s)`. -/
theorem indepFun_past_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IndepFun (fun (ω : CanonicalWienerSpace d T) (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s}) => ω v)
      (fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
      (CanonicalWienerSpace.P (T := T) x) := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x
  set G : Ω' → CanonicalWienerSpace d T :=
    fun ω' => CanonicalWienerSpace.ofCoords x (fun i t => W i t ω') fun i => hW i ω' with hGdef
  have hG : AEMeasurable G Q := by
    refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [G, CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  rw [hP]
  refine indepFun_map_of_comp hG
    (measurable_pi_iff.2 fun v => ContinuousMap.measurable_eval _)
    ((measurable_B t).sub (measurable_B s)) ?_
  have hA := indepFun_coords_past_shift hB hind s.toNNReal
  set s' := s.toNNReal
  set t' := t.toNNReal
  have hss : s' ≤ t' := Real.toNNReal_le_toNNReal hst
  have hc := hA.comp
    (φ := fun (f : Fin d → Iic s' → ℝ) (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s}) =>
      x + ∑ i, f i ⟨((v : Icc (0 : ℝ) T) : ℝ).toNNReal,
        mem_Iic.2 (Real.toNNReal_le_toNNReal v.2)⟩ • Rd.basisVec i)
    (ψ := fun (f : Fin d → ℝ≥0 → ℝ) => ∑ i, f i (t' - s') • Rd.basisVec i)
    (by fun_prop) (by fun_prop)
  refine hc.congr (Eventually.of_forall fun ω' => ?_) (Eventually.of_forall fun ω' => ?_)
  · funext v
    simp [G, CanonicalWienerSpace.ofCoords]
  · have htI : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
    have hsI : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
    simp only [Function.comp_apply, CanonicalWienerSpace.B, htI, hsI, dite_true, G,
      CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk, add_tsub_cancel_of_le hss]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    simp_rw [sub_smul]
    rfl

/-- **Subgoal** (P53.A): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, `B(t) - B(s)` is independent of the
natural `σ`-algebra `𝓕_s`. -/
theorem indep_naturalSigma_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) :
    Indep (IsItoIntegral.naturalSigma d T s)
      (MeasurableSpace.comap (fun ω : CanonicalWienerSpace d T =>
        CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) inferInstance)
      (CanonicalWienerSpace.P (T := T) x) :=
  (IndepFun_iff_Indep _ _ _).1 (indepFun_past_increment x hs hst ht)

/-- **Subgoal** (P53.A, helper): a concrete representation of `ℙ_x` as the image `Q.map G` of
independent real Brownian motions `W^i`, under which `B(t) - B(s) = ∑_i (W^i_t - W^i_s) e_i`. -/
theorem exists_rep_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (W : Fin d → ℝ≥0 → Ω' → ℝ)
      (G : Ω' → CanonicalWienerSpace d T), IsProbabilityMeasure Q ∧
      (∀ i, IsBrownianReal (W i) Q) ∧ iIndepFun (fun i ω' t => W i t ω') Q ∧
      AEMeasurable G Q ∧ CanonicalWienerSpace.P (T := T) x = Q.map G ∧
      ∀ ω', CanonicalWienerSpace.B t (G ω') - CanonicalWienerSpace.B s (G ω') =
        ∑ i, (W i t.toNNReal ω' - W i s.toNNReal ω') • Rd.basisVec i := by
  obtain ⟨Ω', _, Q, W, hW, hQ, hB, hind, hP⟩ := CanonicalWienerSpace.isLaw_P (T := T) x
  refine ⟨Ω', inferInstance, Q, W,
    fun ω' => CanonicalWienerSpace.ofCoords x (fun i t => W i t ω') fun i => hW i ω',
    hQ, hB, hind, ?_, hP, fun ω' => ?_⟩
  · refine CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval fun r => ?_
    simp only [CanonicalWienerSpace.ofCoords, ContinuousMap.coe_mk]
    exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hB i).toIsPreBrownianReal.aemeasurable _).smul_const _)
  · have htI : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
    have hsI : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
    simp only [CanonicalWienerSpace.B, htI, hsI, dite_true, CanonicalWienerSpace.ofCoords,
      ContinuousMap.coe_mk]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    simp_rw [sub_smul]

/-- **Subgoal** (P53.A, helper): the `i`-th coordinate of `∑_j a_j e_j` is `a_i`. -/
theorem coord_sum_smul_basisVec (a : Fin d → ℝ) (i : Fin d) :
    Rd.coord i (∑ j, a j • Rd.basisVec j) = a i := by
  simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right, Pi.single_apply]

/-- **Subgoal** (P53.A, helper): each coordinate map `v ↦ v^i` is measurable. -/
theorem measurable_coord (i : Fin d) : Measurable (Rd.coord (d := d) i) :=
  (continuous_id.inner continuous_const).measurable

/-- **Subgoal** (P53.A, increment moments): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, the increment
`B(t) - B(s)` is square integrable, centred, with covariance `(t - s) I`. -/
theorem increment_moments (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    MemLp (fun ω : CanonicalWienerSpace d T =>
        CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) 2 (CanonicalWienerSpace.P (T := T) x) ∧
      (∀ i, ∫ ω, Rd.coord i (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
        ∂CanonicalWienerSpace.P (T := T) x = 0) ∧
      ∀ i j, ∫ ω, Rd.coord i (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) *
          Rd.coord j (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
          ∂CanonicalWienerSpace.P (T := T) x = if i = j then t - s else 0 := by
  obtain ⟨Ω', _, Q, W, G, hQ, hB, hind, hG, hP, hrep⟩ := exists_rep_increment x hs hst ht
  set D : CanonicalWienerSpace d T → Rd d :=
    fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω with hD
  have hDm : Measurable D := (measurable_B t).sub (measurable_B s)
  set Δ : Fin d → Ω' → ℝ := fun i ω' => W i t.toNNReal ω' - W i s.toNNReal ω' with hΔ
  have hlaw : ∀ i, HasLaw (Δ i) (gaussianReal 0 (nndist t.toNNReal.1 s.toNNReal.1)) Q :=
    fun i => (hB i).toIsPreBrownianReal.hasLaw_sub _ _
  have hnd : (nndist t.toNNReal.1 s.toNNReal.1 : ℝ) = t - s := by
    rw [coe_nndist, Real.dist_eq, NNReal.val_eq_coe, NNReal.val_eq_coe,
      Real.coe_toNNReal _ (hs.trans hst), Real.coe_toNNReal _ hs, abs_of_nonneg (by linarith)]
  have hΔ2 : ∀ i, MemLp (Δ i) 2 Q := fun i => (hlaw i).memLp (memLp_id_gaussianReal 2)
  have hΔint : ∀ i, ∫ ω', Δ i ω' ∂Q = 0 := fun i => by
    rw [(hlaw i).integral_eq, integral_id_gaussianReal]
  have hrep' : ∀ ω', D (G ω') = ∑ i, Δ i ω' • Rd.basisVec i := hrep
  have hDG : D ∘ G = fun ω' => ∑ i, Δ i ω' • Rd.basisVec i := funext hrep'
  rw [hP]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · rw [memLp_map_measure_iff hDm.aestronglyMeasurable hG, hDG]
    exact memLp_finsetSum _ fun i _ =>
      (hΔ2 i).smul (q := ⊤) (r := 2) (memLp_top_const (Rd.basisVec i))
  · rw [integral_map (f := fun ω => Rd.coord i (D ω)) hG
      ((measurable_coord i).comp hDm).aestronglyMeasurable]
    simp_rw [hrep', coord_sum_smul_basisVec]
    exact hΔint i
  · rw [integral_map (f := fun ω => Rd.coord i (D ω) * Rd.coord j (D ω)) hG
      (((measurable_coord i).comp hDm).mul ((measurable_coord j).comp hDm)).aestronglyMeasurable]
    simp_rw [hrep', coord_sum_smul_basisVec]
    split_ifs with hij
    · subst hij
      have hv := (hlaw i).variance_eq
      rw [variance_id_gaussianReal, hnd,
        variance_of_integral_eq_zero (hlaw i).aemeasurable (hΔint i)] at hv
      simpa [pow_two] using hv
    · have hI := ((hind.indepFun hij).comp
        (φ := fun f : ℝ≥0 → ℝ => f t.toNNReal - f s.toNNReal)
        (ψ := fun f : ℝ≥0 → ℝ => f t.toNNReal - f s.toNNReal) (by fun_prop) (by fun_prop))
      have h := hI.integral_mul_eq_mul_integral
        (hlaw i).aemeasurable.aestronglyMeasurable (hlaw j).aemeasurable.aestronglyMeasurable
      have h0 := hΔint i
      simp only [Function.comp_def, Pi.mul_apply] at h
      simp only [h, Δ] at h0 ⊢
      rw [h0, zero_mul]

/-- **Subgoal** (P53.A, helper): the coordinate `v^i = ⟨v, e_i⟩` is the `i`-th entry of `v`. -/
theorem coord_apply (i : Fin d) (v : Rd d) : Rd.coord i v = v i := by
  simp [Rd.coord, Rd.basisVec, EuclideanSpace.inner_single_right]

/-- **Subgoal** (P53.A, helper): `⟨v, w⟩ = ∑_i v^i w^i`. -/
theorem inner_eq_sum_coord (v w : Rd d) : ⟪v, w⟫ = ∑ i, Rd.coord i v * Rd.coord i w := by
  simp [coord_apply, PiLp.inner_apply, mul_comm]

/-- **Subgoal** (P53.A, helper): `|v|² = ∑_i (v^i)²`. -/
theorem norm_sq_eq_sum_coord (v : Rd d) : ‖v‖ ^ 2 = ∑ i, Rd.coord i v ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, coord_apply]

/-- **Subgoal** (P53.A, helper): an `𝓕_s`-measurable real variable is independent of any
measurable function of `B(t) - B(s)` under `ℙ_x`. -/
theorem indepFun_naturalSigma_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) {f : CanonicalWienerSpace d T → ℝ}
    (hf : Measurable[IsItoIntegral.naturalSigma d T s] f) {g : Rd d → ℝ} (hg : Measurable g) :
    IndepFun f (fun ω => g (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω))
      (CanonicalWienerSpace.P (T := T) x) := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right
    (indep_naturalSigma_increment x hs hst ht) ?_) hf.comap_le
  rw [show (fun ω => g (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)) =
    g ∘ (fun ω : CanonicalWienerSpace d T =>
      CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- **Subgoal** (P53.A, one-step isometry): for `0 ≤ s ≤ t ≤ T` and `ξ ∈ L²(ℙ_x)`
`𝓕_s`-measurable, `E⟨ξ, B(t) - B(s)⟩² = (t - s) E|ξ|²`. -/
theorem integral_inner_increment_sq (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) {ξ : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T s] ξ)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ ^ 2
        ∂CanonicalWienerSpace.P (T := T) x =
      (t - s) * ∫ ω, ‖ξ ω‖ ^ 2 ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (P53.A, cross terms): for `0 ≤ s ≤ t ≤ s' ≤ t' ≤ T`, `ξ ∈ L²` `𝓕_s`-measurable
and `η ∈ L²` `𝓕_{s'}`-measurable, `E[⟨ξ, B(t) - B(s)⟩ ⟨η, B(t') - B(s')⟩] = 0`. -/
theorem integral_inner_increment_mul_eq_zero (x : Rd d) {s t s' t' : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hts' : t ≤ s') (hst' : s' ≤ t') (ht' : t' ≤ T)
    {ξ η : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T s] ξ)
    (hη : Measurable[IsItoIntegral.naturalSigma d T s'] η)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) (hη2 : MemLp η 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ *
        ⟪η ω, CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω⟫
        ∂CanonicalWienerSpace.P (T := T) x = 0 := by
  sorry

/-- **Subgoal** (P53.B, elementary Itô isometry): for an adapted elementary integrand with
`L²` values on a grid `0 = s_0 ≤ … ≤ s_k = t ≤ T`,
`E[(∫ H dB)²] = E ∫_0^t |H(u)|² du`. -/
theorem elementary_isometry (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    (hξ2 : ∀ j, MemLp (ξ j) 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, IsItoIntegral.elementaryIntegral s ξ ω ^ 2 ∂CanonicalWienerSpace.P (T := T) x =
      ∫ ω, (∫ u in (0 : ℝ)..s (Fin.last k), ‖IsItoIntegral.elementaryValue s ξ u ω‖ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (P53.B, localisation): for an adapted elementary integrand on
`0 = s_0 ≤ … ≤ s_k ≤ T` and `ε, δ > 0`,
`ℙ(|∫ H dB| ≥ ε) ≤ δ / ε² + ℙ(∫ |H|² ≥ δ)`. -/
theorem elementary_localisation (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    CanonicalWienerSpace.P (T := T) x {ω | ε ≤ |IsItoIntegral.elementaryIntegral s ξ ω|} ≤
      ENNReal.ofReal (δ / ε ^ 2) + CanonicalWienerSpace.P (T := T) x
        {ω | δ ≤ ∫ u in (0 : ℝ)..s (Fin.last k), ‖IsItoIntegral.elementaryValue s ξ u ω‖ ^ 2} := by
  sorry

end proposition_5_3

end WeakPathwiseIto
