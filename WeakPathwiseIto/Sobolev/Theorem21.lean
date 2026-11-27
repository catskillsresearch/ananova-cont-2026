/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.IsCubeOrBall
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakGradient
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Sobolev.Theorem21First
public import WeakPathwiseIto.Sobolev.Theorem21Second

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.1** (first estimate, [BH93, Thm. 1]). For `f ∈ W^{1,1}(ℝ^d)` with precise
representatives and `x, y` in a cube or ball `Q` at which `f̃` is finite and which are Lebesgue
points of `f` (as in [BH93], "outside a null set"; see WeakPathwiseIto.md),
`|f̃(y) - f̃(x)| ≤ C_d (∫_Q |∇f(z)| / |x - z|^{d-1} dz + ∫_Q |∇f(z)| / |y - z|^{d-1} dz)`. -/
theorem theorem_2_1_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G →
    ∀ Q : Set (Rd d), IsCubeOrBall Q → ∀ x y : Rd d, x ∈ Q → y ∈ Q →
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      IsLebesguePoint f x → IsLebesguePoint f y →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x| ≤
        C * ((∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1)) +
          ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun f G _ _ Q _ x y _ _ _ _ _ _ => ?_⟩
    rw [Subsingleton.elim x y, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  obtain ⟨C, hC⟩ := theorem_2_1_first.abs_sub_average_le hd
  refine ⟨C, fun f G hf hG Q hQ x y hx hy _ _ hLx hLy => ?_⟩
  have hfl : LocallyIntegrable f := (memLp_one_iff_integrable.1 hf.1).locallyIntegrable
  obtain ⟨cx, hcx⟩ := hLx
  obtain ⟨cy, hcy⟩ := hLy
  rw [theorem_2_1_first.preciseRepresentative_eq hfl hcx,
    theorem_2_1_first.preciseRepresentative_eq hfl hcy]
  have h1 := hC f G Q x cx hf hG hQ hx hcx
  have h2 := hC f G Q y cy hf hG hQ hy hcy
  calc ENNReal.ofReal |cy - cx|
      ≤ ENNReal.ofReal (|cy - ⨍ z in Q, f z| + |cx - ⨍ z in Q, f z|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc |cy - cx| ≤ |cy - ⨍ z in Q, f z| + |(⨍ z in Q, f z) - cx| :=
            abs_sub_le cy (⨍ z in Q, f z) cx
          _ = _ := by rw [abs_sub_comm (⨍ z in Q, f z) cx]
    _ = ENNReal.ofReal |cy - ⨍ z in Q, f z| + ENNReal.ofReal |cx - ⨍ z in Q, f z| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ C * (∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1)) +
          C * ∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1) := add_le_add h2 h1
    _ = _ := by rw [← mul_add, add_comm]

/-- **Theorem 2.1** (second estimate, stated as [BH93, Thm. 2] with `m = 2`). For
`f ∈ W^{2,1}(ℝ^d)` and `x, y ∈ Q` with `f̃(x), f̃(y), ∇̃f(x)` finite, `x, y` Lebesgue points of
`f` and `x` a Lebesgue point of `∇f`,
`|f̃(y) - f̃(x) - ∇̃f(x)(y - x)| ≤ C_d (I²_Q(|∇²f|)(x) + I²_Q(|∇²f|)(y) + diam Q · I¹_Q(|∇²f|)(x))`
with `I^k_Q(g)(x) = ∫_Q g(z) / |x - z|^{d-k} dz`. The paper omits the last term; without it the
estimate is false for `d ≥ 2` even for smooth `f` (see WeakPathwiseIto.md, "Theorem 2.1:
second estimate"). -/
theorem theorem_2_1_second (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)),
    MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H →
    ∀ Q : Set (Rd d), IsCubeOrBall Q → ∀ x y : Rd d, x ∈ Q → y ∈ Q →
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      preciseRepresentative.VecIsFinite G x →
      IsLebesguePoint f x → IsLebesguePoint f y →
      (∀ i, IsLebesguePoint (fun z => Rd.coord i (G z)) x) →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x -
          ⟪preciseRepresentative.vec G x, y - x⟫| ≤
        C * ((∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2)) +
          (∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2)) +
          Metric.ediam Q * ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun f G H _ _ _ Q _ x y _ _ _ _ _ _ _ _ => ?_⟩
    rw [Subsingleton.elim x y, sub_self, sub_self, inner_zero_right, sub_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  obtain ⟨C1, hC1⟩ := theorem_2_1_second.abs_sub_taylorAverage_le hd
  obtain ⟨C2, hC2⟩ := theorem_2_1_first.abs_sub_average_le hd
  obtain ⟨K0, hK0⟩ := theorem_2_1_first.isCubeOrBall_props hd
  refine ⟨C1 + (d : ℝ≥0) * C2, fun f G H hf hG hH Q hQ x y hx hy _ _ _ hLx hLy hLG => ?_⟩
  obtain ⟨-, hQm, hQb, hQ0, -⟩ := hK0 Q hQ
  have hQt : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hf1 : MemW 1 1 f := ⟨hf.1, fun α h => hf.2 α (h.trans (by norm_num))⟩
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf.1
  have hfl : LocallyIntegrable f := hfi.locallyIntegrable
  have hGi : ∀ i, Integrable fun z => Rd.coord i (G z) :=
    theorem_2_1_first.coord_integrable hf1 hG
  have hexp : ∀ w : Rd d, w = ∑ i, Rd.coord i w • Rd.basisVec i := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rd.coord, Rd.basisVec, real_inner_comm]
  have hGint : Integrable G := by
    have : G = fun z => ∑ i, Rd.coord i (G z) • Rd.basisVec i := funext fun z => hexp (G z)
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hGi i).smul_const _
  have hinner : ∀ v w : Rd d, ⟪v, w⟫ = ∑ i, Rd.coord i v * Rd.coord i w := by
    intro v w
    conv_lhs => rw [hexp v]
    simp [sum_inner, inner_smul_left, Rd.coord, real_inner_comm]
  have hcw : ∀ (i : Fin d) (w : Rd d), |Rd.coord i w| ≤ ‖w‖ := by
    intro i w
    have h := abs_real_inner_le_norm w (Rd.basisVec i)
    have hb : ‖Rd.basisVec i‖ = 1 := by simp [Rd.basisVec]
    rwa [hb, mul_one] at h
  -- Lebesgue values
  obtain ⟨cx, hcx⟩ := hLx
  obtain ⟨cy, hcy⟩ := hLy
  choose g hg using hLG
  rw [theorem_2_1_first.preciseRepresentative_eq hfl hcx,
    theorem_2_1_first.preciseRepresentative_eq hfl hcy]
  have hvec : preciseRepresentative.vec G x = ∑ i, g i • Rd.basisVec i := by
    unfold preciseRepresentative.vec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [theorem_2_1_first.preciseRepresentative_eq (hGi i).locallyIntegrable (hg i)]
  rw [hvec]
  -- the averaged Taylor polynomial
  obtain ⟨R, hR⟩ := hQb.subset_closedBall (0 : Rd d)
  have hTi : ∀ w : Rd d, IntegrableOn (fun z => f z + ⟪G z, w - z⟫) Q := by
    intro w
    refine hfi.integrableOn.add (Integrable.mono' (hGint.integrableOn.norm.mul_const (‖w‖ + R))
      ((hGint.aestronglyMeasurable.inner
        (continuous_const.sub continuous_id).aestronglyMeasurable).restrict) ?_)
    refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs]
    have hz : ‖z‖ ≤ R := by simpa using hR hz
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (norm_sub_le _ _).trans (by linarith)
  set T : Rd d → ℝ := fun w => ⨍ z in Q, (f z + ⟪G z, w - z⟫) with hTdef
  set a : Fin d → ℝ := fun i => ⨍ z in Q, Rd.coord i (G z) with hadef
  have hTdiff : T y - T x = ∑ i, a i * Rd.coord i (y - x) := by
    simp only [hTdef, hadef]
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, ← mul_sub,
      ← integral_sub (hTi y) (hTi x)]
    have e1 : (fun z => f z + ⟪G z, y - z⟫ - (f z + ⟪G z, x - z⟫)) =
        fun z => ∑ i, Rd.coord i (G z) * Rd.coord i (y - x) := by
      funext z
      rw [← hinner]
      simp only [inner_sub_right]
      ring
    rw [e1, integral_finset_sum _ fun i _ => ((hGi i).integrableOn.mul_const _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setAverage_eq, smul_eq_mul, integral_mul_const]
    ring
  have hsplit : cy - cx - ⟪∑ i, g i • Rd.basisVec i, y - x⟫ =
      (cy - T y) - (cx - T x) + ∑ i, (a i - g i) * Rd.coord i (y - x) := by
    have hgi : ⟪∑ i, g i • Rd.basisVec i, y - x⟫ = ∑ i, g i * Rd.coord i (y - x) := by
      simp [sum_inner, inner_smul_left, Rd.coord, real_inner_comm]
    rw [hgi]
    have : ∑ i, (a i - g i) * Rd.coord i (y - x) =
        (T y - T x) - ∑ i, g i * Rd.coord i (y - x) := by
      rw [hTdiff, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]; ring
  -- the gradient coordinates
  set V : Fin d → Rd d → Rd d := fun i z => ∑ j, Rd.coord i (H z (Rd.basisVec j)) • Rd.basisVec j
    with hVdef
  have hVn : ∀ i z, ‖V i z‖ₑ ≤ ‖H z‖ₑ := by
    intro i z
    have hadj : V i z = ContinuousLinearMap.adjoint (H z) (Rd.basisVec i) := by
      conv_rhs => rw [hexp (ContinuousLinearMap.adjoint (H z) (Rd.basisVec i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [Rd.coord]
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    rw [hadj, ← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal (((ContinuousLinearMap.adjoint (H z)).le_opNorm _).trans ?_)
    have hb : ‖Rd.basisVec i‖ = 1 := by simp [Rd.basisVec]
    rw [hb, mul_one, LinearIsometryEquiv.norm_map]
  set I1 : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 1) with hI1
  set Ix : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2) with hIx
  set Iy : ℝ≥0∞ := ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2) with hIy
  have hgrad : ∀ i, ENNReal.ofReal |g i - a i| ≤ C2 * I1 := by
    intro i
    refine (hC2 _ (V i) Q x (g i) (theorem_2_1_second.memW_coord hf hG hH i)
      (theorem_2_1_second.isWeakGradient_coord hG hH i) hQ hx (hg i)).trans ?_
    exact mul_le_mul' le_rfl (lintegral_mono fun z =>
      ENNReal.div_le_div_right (hVn i z) _)
  have hy1 := hC1 f G H Q y cy hf hG hH hQ hy hcy
  have hx1 := hC1 f G H Q x cx hf hG hH hQ hx hcx
  have hD : edist y x ≤ Metric.ediam Q := Metric.edist_le_ediam_of_mem hy hx
  rw [hsplit]
  calc ENNReal.ofReal |cy - T y - (cx - T x) + ∑ i, (a i - g i) * Rd.coord i (y - x)|
      ≤ ENNReal.ofReal (|cy - T y| + |cx - T x| + ∑ i, |g i - a i| * ‖y - x‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hcw i _) (abs_nonneg _)
    _ = ENNReal.ofReal |cy - T y| + ENNReal.ofReal |cx - T x| +
          ∑ i, ENNReal.ofReal |g i - a i| * edist y x := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by positivity),
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _), edist_dist, dist_eq_norm]
    _ ≤ C1 * Iy + C1 * Ix + ∑ _i : Fin d, C2 * I1 * Metric.ediam Q :=
        add_le_add (add_le_add hy1 hx1) (Finset.sum_le_sum fun i _ => mul_le_mul' (hgrad i) hD)
    _ = C1 * (Ix + Iy) + (d : ℝ≥0∞) * C2 * (Metric.ediam Q * I1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ C1 * (Ix + Iy + Metric.ediam Q * I1) + (d : ℝ≥0∞) * C2 * (Ix + Iy + Metric.ediam Q * I1) :=
        add_le_add (mul_le_mul' le_rfl le_self_add) (mul_le_mul' le_rfl le_add_self)
    _ = _ := by push_cast; ring

end WeakPathwiseIto
