/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The classical Hessian `∇²F(x)` of a twice differentiable `F : ℝ^d → ℝ`, as the derivative
of the gradient, a linear map `ℝ^d →L ℝ^d`. -/
def smoothHessian {d : ℕ} (F : Rd d → ℝ) (x : Rd d) : Rd d →L[ℝ] Rd d :=
  fderiv ℝ (gradient F) x

end WeakPathwiseIto
