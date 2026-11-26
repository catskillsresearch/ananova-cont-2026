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

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.1** (first estimate, [BH93, Thm. 1]). For `f ∈ W^{1,1}(ℝ^d)` with precise
representatives and `x, y` in a cube or ball `Q` at which `f̃` is finite,
`|f̃(y) - f̃(x)| ≤ C_d (∫_Q |∇f(z)| / |x - z|^{d-1} dz + ∫_Q |∇f(z)| / |y - z|^{d-1} dz)`. -/
theorem theorem_2_1_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G →
    ∀ Q : Set (Rd d), IsCubeOrBall Q → ∀ x y : Rd d, x ∈ Q → y ∈ Q →
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x| ≤
        C * ((∫⁻ z in Q, ‖G z‖ₑ / edist x z ^ ((d : ℝ) - 1)) +
          ∫⁻ z in Q, ‖G z‖ₑ / edist y z ^ ((d : ℝ) - 1)) := by
  sorry

/-- **Theorem 2.1** (second estimate). For `f ∈ W^{2,1}(ℝ^d)` and `x, y ∈ Q` with
`f̃(x), f̃(y), ∇̃f(x)` finite,
`|f̃(y) - f̃(x) - ∇̃f(x)(y - x)| ≤ C_d (∫_Q |∇²f(z)| / |x - z|^{d-2} dz + ∫_Q |∇²f(z)| / |y - z|^{d-2} dz)`. -/
theorem theorem_2_1_second (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)),
    MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H →
    ∀ Q : Set (Rd d), IsCubeOrBall Q → ∀ x y : Rd d, x ∈ Q → y ∈ Q →
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      preciseRepresentative.VecIsFinite G x →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x -
          ⟪preciseRepresentative.vec G x, y - x⟫| ≤
        C * ((∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ ((d : ℝ) - 2)) +
          ∫⁻ z in Q, ‖H z‖ₑ / edist y z ^ ((d : ℝ) - 2)) := by
  sorry

end WeakPathwiseIto
