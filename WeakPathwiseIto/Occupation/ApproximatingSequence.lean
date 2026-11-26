/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Occupation.OccupationSeminorm

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- An approximating sequence for `F` with weak Hessian `H` along `(ω, π)` (eq. (8)), indexed by `m ≥ 1` (the value at `m = 0` is unconstrained):
`F_m ∈ C^2_b ∩ W^{2,1}`, `F_m(ω(t)) → F(ω(t))` for all `t ∈ [0, T]`, and
`‖∇²F_m - ∇²F‖_{W^0_{ω,π}} → 0`. -/
structure ApproximatingSequence {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (ω : ℝ → Rd d)
    (F : Rd d → ℝ) (H : Rd d → (Rd d →L[ℝ] Rd d)) where
  /-- The approximating functions `F_m`, `m ≥ 1`. -/
  seq : ℕ → Rd d → ℝ
  smooth : ∀ m, 1 ≤ m → ContDiffBounded 2 (seq m)
  sobolev : ∀ m, 1 ≤ m → MemW 2 1 (seq m)
  tendsto_path : ∀ t ∈ Icc 0 T, Tendsto (fun m => seq m (ω t)) atTop (𝓝 (F (ω t)))
  tendsto_hessian :
    Tendsto (fun m => occupationSeminorm π ω (fun x => smoothHessian (seq m) x - H x)) atTop (𝓝 0)

end WeakPathwiseIto
