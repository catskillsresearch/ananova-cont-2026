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
  sorry

end WeakPathwiseIto
