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
* **P53.B**: elementary isometry (the `L²` construction of the stopped integrals).
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
  set P := CanonicalWienerSpace.P (T := T) x
  have := CanonicalWienerSpace.isProbabilityMeasure_P (T := T) x
  set D : CanonicalWienerSpace d T → Rd d :=
    fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω with hD
  obtain ⟨hD2, -, hcov⟩ := increment_moments x hs hst ht
  have ha2 : ∀ i, MemLp (fun ω => Rd.coord i (ξ ω)) 2 P := fun i => hξ2.inner_const _
  have hb2 : ∀ i, MemLp (fun ω => Rd.coord i (D ω)) 2 P := fun i => hD2.inner_const _
  have hξm : ∀ i j, Measurable[IsItoIntegral.naturalSigma d T s]
      (fun ω => Rd.coord i (ξ ω) * Rd.coord j (ξ ω)) := fun i j =>
    ((measurable_coord i).comp hξ).mul ((measurable_coord j).comp hξ)
  have hind : ∀ i j, IndepFun (fun ω => Rd.coord i (ξ ω) * Rd.coord j (ξ ω))
      (fun ω => Rd.coord i (D ω) * Rd.coord j (D ω)) P := fun i j =>
    indepFun_naturalSigma_increment x hs hst ht (hξm i j)
      ((measurable_coord i).mul (measurable_coord j))
  have hint : ∀ i j, Integrable (fun ω => (Rd.coord i (ξ ω) * Rd.coord j (ξ ω)) *
      (Rd.coord i (D ω) * Rd.coord j (D ω))) P := fun i j =>
    (hind i j).integrable_mul ((ha2 i).integrable_mul (ha2 j)) ((hb2 i).integrable_mul (hb2 j))
  have hexp : ∀ ω, ⟪ξ ω, D ω⟫ ^ 2 = ∑ i, ∑ j, (Rd.coord i (ξ ω) * Rd.coord j (ξ ω)) *
      (Rd.coord i (D ω) * Rd.coord j (D ω)) := fun ω => by
    rw [inner_eq_sum_coord, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [show ∀ ω, ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ ^ 2 =
    ⟪ξ ω, D ω⟫ ^ 2 from fun _ => rfl, hexp, norm_sq_eq_sum_coord]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j,
    integral_finsetSum _ fun i _ => (ha2 i).integrable_sq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  have hcov' : ∀ i j, ∫ ω, Rd.coord i (D ω) * Rd.coord j (D ω) ∂P =
      if i = j then t - s else 0 := hcov
  rw [Finset.sum_congr rfl fun j _ => (hind i j).integral_fun_mul_eq_mul_integral
    ((ha2 i).integrable_mul (ha2 j)).1 ((hb2 i).integrable_mul (hb2 j)).1]
  simp only [hcov', mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [mul_comm]
  simp only [sq]

/-- **Subgoal** (P53.A, helper): for `ξ ∈ L²` `𝓕_s`-measurable, `⟨ξ, B(t) - B(s)⟩ ∈ L²(ℙ_x)`. -/
theorem memLp_inner_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) {ξ : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T s] ξ)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) :
    MemLp (fun ω => ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫) 2
      (CanonicalWienerSpace.P (T := T) x) := by
  set P := CanonicalWienerSpace.P (T := T) x
  have := CanonicalWienerSpace.isProbabilityMeasure_P (T := T) x
  set D : CanonicalWienerSpace d T → Rd d :=
    fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω with hD
  obtain ⟨hD2, -, -⟩ := increment_moments x hs hst ht
  have ha2 : ∀ i, MemLp (fun ω => Rd.coord i (ξ ω)) 2 P := fun i => hξ2.inner_const _
  have hb2 : ∀ i, MemLp (fun ω => Rd.coord i (D ω)) 2 P := fun i => hD2.inner_const _
  have hint : ∀ i j, Integrable (fun ω => (Rd.coord i (ξ ω) * Rd.coord j (ξ ω)) *
      (Rd.coord i (D ω) * Rd.coord j (D ω))) P := fun i j =>
    (indepFun_naturalSigma_increment x hs hst ht
      (((measurable_coord i).comp hξ).mul ((measurable_coord j).comp hξ))
      ((measurable_coord i).mul (measurable_coord j))).integrable_mul
      ((ha2 i).integrable_mul (ha2 j)) ((hb2 i).integrable_mul (hb2 j))
  have hm : AEStronglyMeasurable (fun ω => ⟪ξ ω, D ω⟫) P :=
    hξ2.aestronglyMeasurable.inner hD2.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hexp : (fun ω => ⟪ξ ω, D ω⟫ ^ 2) = fun ω => ∑ i, ∑ j,
      (Rd.coord i (ξ ω) * Rd.coord j (ξ ω)) * (Rd.coord i (D ω) * Rd.coord j (D ω)) := by
    funext ω
    rw [inner_eq_sum_coord, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j

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
  set P := CanonicalWienerSpace.P (T := T) x
  have := CanonicalWienerSpace.isProbabilityMeasure_P (T := T) x
  have hs' : 0 ≤ s' := hs.trans (hst.trans hts')
  have hle : IsItoIntegral.naturalSigma d T s ≤ IsItoIntegral.naturalSigma d T s' := by
    have hr : Measurable fun (g : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s'} → Rd d)
        (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s}) => g ⟨v.1, v.2.trans (hst.trans hts')⟩ :=
      measurable_pi_iff.2 fun _ => measurable_pi_apply _
    exact (hr.comp (comap_measurable (m := (inferInstance : MeasurableSpace
      ({v : Icc (0 : ℝ) T // (v : ℝ) ≤ s'} → Rd d)))
      (fun (ω : CanonicalWienerSpace d T) (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s'}) =>
        ω v))).comap_le
  have hBm : ∀ r, 0 ≤ r → r ≤ s' → r ≤ T →
      Measurable[IsItoIntegral.naturalSigma d T s'] (CanonicalWienerSpace.B (d := d) (T := T) r) := by
    intro r hr0 hrs hrT
    have hr : r ∈ Icc 0 T := ⟨hr0, hrT⟩
    have hpm : Measurable[IsItoIntegral.naturalSigma d T s']
        (fun (ω : CanonicalWienerSpace d T) (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s'}) => ω v) :=
      comap_measurable _
    have h2 := (measurable_pi_apply
      (⟨⟨r, hr⟩, hrs⟩ : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s'})).comp hpm
    convert h2 using 1
    funext ω
    simp [CanonicalWienerSpace.B, hr]
  have hT : t ≤ T := hts'.trans (hst'.trans ht')
  have hDm : Measurable[IsItoIntegral.naturalSigma d T s']
      (fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) :=
    (hBm t (hs.trans hst) hts' hT).sub (hBm s hs (hst.trans hts') (hst.trans hT))
  have hI2 := memLp_inner_increment x hs hst hT hξ hξ2
  obtain ⟨hD'2, hmean, -⟩ := increment_moments x hs' hst' ht'
  have hexp : (fun ω => ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ *
      ⟪η ω, CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω⟫) = fun ω => ∑ j,
      (⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ * Rd.coord j (η ω)) *
        Rd.coord j (CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω) := by
    funext ω
    rw [inner_eq_sum_coord (η ω), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hXm : ∀ j, Measurable[IsItoIntegral.naturalSigma d T s'] (fun ω =>
      ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ * Rd.coord j (η ω)) :=
    fun j => ((hξ.mono hle le_rfl).inner hDm).mul ((measurable_coord j).comp hη)
  have hind : ∀ j, IndepFun (fun ω =>
      ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ * Rd.coord j (η ω))
      (fun ω => Rd.coord j (CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω)) P :=
    fun j => indepFun_naturalSigma_increment x hs' hst' ht' (hXm j) (measurable_coord j)
  have hXint : ∀ j, Integrable (fun ω =>
      ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ * Rd.coord j (η ω)) P :=
    fun j => hI2.integrable_mul (hη2.inner_const _)
  have hYint : ∀ j, Integrable
      (fun ω => Rd.coord j (CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω)) P :=
    fun j => (hD'2.inner_const _).integrable one_le_two
  have hTint : ∀ j, Integrable (fun ω =>
      (⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ * Rd.coord j (η ω)) *
        Rd.coord j (CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω)) P :=
    fun j => (hind j).integrable_mul (hXint j) (hYint j)
  rw [hexp, integral_finsetSum _ fun j _ => hTint j]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [(hind j).integral_fun_mul_eq_mul_integral (hXint j).1 (hYint j).1, hmean j, mul_zero]

/-- **Subgoal** (P53.B, helper): the grid intervals `(s_j, s_{j+1}]` of a monotone grid are
pairwise disjoint. -/
theorem disjoint_Ioc_grid {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s) {j l : Fin k}
    (hjl : j ≠ l) :
    Disjoint (Ioc (s j.castSucc) (s j.succ)) (Ioc (s l.castSucc) (s l.succ)) := by
  rcases lt_or_gt_of_ne hjl with h | h
  · exact Ioc_disjoint_Ioc_of_le (hs (Fin.succ_le_castSucc_iff.2 h))
  · exact (Ioc_disjoint_Ioc_of_le (hs (Fin.succ_le_castSucc_iff.2 h))).symm

/-- **Subgoal** (P53.B, helper): `|∑_j ξ_j 1_{(s_j, s_{j+1}]}(u)|² = ∑_j |ξ_j|² 1_{(s_j, s_{j+1}]}(u)`. -/
theorem norm_sq_elementaryValue {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (ξ : Fin k → CanonicalWienerSpace d T → Rd d) (u : ℝ) (ω : CanonicalWienerSpace d T) :
    ‖IsItoIntegral.elementaryValue s ξ u ω‖ ^ 2 =
      ∑ j : Fin k, (Ioc (s j.castSucc) (s j.succ)).indicator (fun _ => ‖ξ j ω‖ ^ 2) u := by
  unfold IsItoIntegral.elementaryValue
  by_cases h : ∃ j : Fin k, u ∈ Ioc (s j.castSucc) (s j.succ)
  · obtain ⟨j, hj⟩ := h
    have hoff : ∀ l : Fin k, l ≠ j → u ∉ Ioc (s l.castSucc) (s l.succ) := fun l hl hu =>
      Set.disjoint_left.1 (disjoint_Ioc_grid hs hl) hu hj
    rw [Finset.sum_eq_single j (fun l _ hl => indicator_of_notMem (hoff l hl) _)
        (by simp), Finset.sum_eq_single j (fun l _ hl => indicator_of_notMem (hoff l hl) _)
        (by simp), indicator_of_mem hj, indicator_of_mem hj]
  · push Not at h
    simp [indicator_of_notMem (h _)]

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

end proposition_5_3

end WeakPathwiseIto
