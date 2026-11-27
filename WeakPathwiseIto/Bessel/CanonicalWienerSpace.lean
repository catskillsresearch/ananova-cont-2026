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

/-- The canonical path space `Ω := C([0, T], ℝ^d)` of Section 2.2, with its Borel σ-algebra. -/
abbrev CanonicalWienerSpace (d : ℕ) (T : ℝ) : Type := C(Icc (0 : ℝ) T, Rd d)

namespace CanonicalWienerSpace

variable {d : ℕ} {T : ℝ}

/-- The canonical coordinate process `B(t)(ω) := ω(t)` for `t ∈ [0, T]` (and `0` off `[0, T]`). -/
def B (t : ℝ) (ω : CanonicalWienerSpace d T) : Rd d := if h : t ∈ Icc 0 T then ω ⟨t, h⟩ else 0

/-- The path `t ↦ B(t)(ω)`, as a path `ℝ → ℝ^d` for the pathwise theory along partitions of
`[0, T]`. -/
def path (ω : CanonicalWienerSpace d T) : ℝ → Rd d := fun t => B t ω

/-- The element `t ↦ x + ∑_i W^i(t) e_i` of `Ω` built from `d` continuous real paths `W^i`. -/
def ofCoords (x : Rd d) (W : Fin d → ℝ≥0 → ℝ) (hW : ∀ i, Continuous (W i)) :
    CanonicalWienerSpace d T :=
  ⟨fun s => x + ∑ i, W i (s : ℝ).toNNReal • Rd.basisVec i,
    continuous_const.add (continuous_finsetSum _ fun i _ =>
      ((hW i).comp (continuous_real_toNNReal.comp continuous_subtype_val)).smul continuous_const)⟩

/-- `P` is the law of `d`-dimensional Brownian motion started at `x`, on `Ω`: the image of a
probability `Q` under `ω' ↦ (t ↦ x + ∑_i W^i_t(ω') e_i)` for independent real Brownian motions
`W^1, …, W^d` (Mathlib's `ProbabilityTheory.IsBrownianReal`) with continuous paths. -/
def IsLaw (x : Rd d) (P : Measure (CanonicalWienerSpace d T)) : Prop :=
  ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (W : Fin d → ℝ≥0 → Ω' → ℝ)
    (hW : ∀ i ω', Continuous fun t => W i t ω'),
    IsProbabilityMeasure Q ∧ (∀ i, ProbabilityTheory.IsBrownianReal (W i) Q) ∧
    ProbabilityTheory.iIndepFun (fun i ω' t => W i t ω') Q ∧
    P = Q.map fun ω' => ofCoords x (fun i t => W i t ω') fun i => hW i ω'

/-- The law `ℙ_x` of Brownian motion started at `x` on the canonical space
`Ω = C([0, T], ℝ^d)` (Section 2.2): the measure satisfying `IsLaw x`, which exists and is
unique (`CanonicalWienerSpace.exists_isLaw`, `CanonicalWienerSpace.isLaw_unique`). -/
def P (x : Rd d) : Measure (CanonicalWienerSpace d T) := Classical.epsilon (IsLaw x)

end CanonicalWienerSpace

end WeakPathwiseIto
