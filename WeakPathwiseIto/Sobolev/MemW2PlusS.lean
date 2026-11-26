/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakHessian

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Sobolev–Slobodeckij space `W^{2+s,p}(ℝ^d)` (Section 5.2): `f ∈ W^{2,p}` and its weak
Hessian has finite Gagliardo seminorm
`∫∫ |∇²f(x) - ∇²f(y)|^p / |x - y|^{sp + d} dx dy < ∞`. -/
def MemW2PlusS {d : ℕ} (s p : ℝ) (f : Rd d → ℝ) : Prop :=
  MemW 2 (ENNReal.ofReal p) f ∧ ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian f H ∧
    (∫⁻ x, ∫⁻ y, ‖H x - H y‖ₑ ^ p / edist x y ^ (s * p + d)) < ⊤

end WeakPathwiseIto
