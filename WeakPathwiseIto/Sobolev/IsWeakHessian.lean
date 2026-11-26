/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.IsWeakDerivative

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- `H` is a weak Hessian `∇²f` of `f`: the `(i, j)` entry `⟨H(x) e_j, e_i⟩` is the weak
derivative `∂_i ∂_j f`. -/
def IsWeakHessian {d : ℕ} (f : Rd d → ℝ) (H : Rd d → (Rd d →L[ℝ] Rd d)) : Prop :=
  ∀ i j : Fin d, IsWeakDerivative (Pi.single i 1 + Pi.single j 1) f
    (fun x => Rd.coord i (H x (Rd.basisVec j)))

end WeakPathwiseIto
