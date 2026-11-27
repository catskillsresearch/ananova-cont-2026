/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakGradient
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Sobolev.Theorem23Steps

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Theorem 2.3** (first estimate). For `f ∈ W^{1,1}(ℝ^d)` and `f̃(x), f̃(y)` finite,
`|f̃(y) - f̃(x)| ≤ C_d (M_{|x-y|}|∇f|(x) + M_{|x-y|}|∇f|(y)) |x - y|`. -/
theorem theorem_2_3_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d),
    MemW 1 1 f → IsWeakGradient f G → ∀ x y : Rd d,
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x| ≤
        C * (localMaximalFunction (edist x y) G x + localMaximalFunction (edist x y) G y) *
          edist x y := by
  sorry

/-- **Theorem 2.3** (second estimate). For `f ∈ W^{2,1}(ℝ^d)` and `f̃(x), f̃(y), ∇̃f(x)` finite,
`|f̃(y) - f̃(x) - ∇̃f(x)(y - x)| ≤ C_d (M_{|x-y|}|∇²f|(x) + M_{|x-y|}|∇²f|(y)) |x - y|²`. -/
theorem theorem_2_3_second (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (G : Rd d → Rd d)
    (H : Rd d → (Rd d →L[ℝ] Rd d)),
    MemW 2 1 f → IsWeakGradient f G → IsWeakHessian f H → ∀ x y : Rd d,
      preciseRepresentative.IsFinite f x → preciseRepresentative.IsFinite f y →
      preciseRepresentative.VecIsFinite G x →
      ENNReal.ofReal |preciseRepresentative f y - preciseRepresentative f x -
          ⟪preciseRepresentative.vec G x, y - x⟫| ≤
        C * (localMaximalFunction (edist x y) H x + localMaximalFunction (edist x y) H y) *
          edist x y ^ 2 := by
  sorry

end WeakPathwiseIto
