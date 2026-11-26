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

/-- `G` is a weak gradient `∇f` of `f`: each coordinate `G^i` is the weak derivative `∂_i f`. -/
def IsWeakGradient {d : ℕ} (f : Rd d → ℝ) (G : Rd d → Rd d) : Prop :=
  ∀ i : Fin d, IsWeakDerivative (Pi.single i 1) f (fun x => Rd.coord i (G x))

end WeakPathwiseIto
