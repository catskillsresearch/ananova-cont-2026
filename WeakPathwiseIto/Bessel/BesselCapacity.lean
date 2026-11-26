/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselSpace

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Bessel `(α, p)`-capacity (Definition 2.7):
`B_{α,p}(E) := inf {‖h‖_p^p : g_α ⋆ h ≥ 1_E, h ≥ 0}`. -/
def besselCapacity (d : ℕ) (α : ℝ) (p : ℝ≥0∞) (S : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (h : Rd d → ℝ) (_ : 0 ≤ h) (_ : ∀ x ∈ S, 1 ≤ BesselSpace.potential d α h x),
    eLpNorm h p volume ^ p.toReal

namespace besselCapacity

variable {d : ℕ}

/-- `S` is `(α, p)`-polar: `B_{α,p}(S) = 0` (Definition 2.7). -/
def IsNull (d : ℕ) (α : ℝ) (p : ℝ≥0∞) (S : Set (Rd d)) : Prop := besselCapacity d α p S = 0

/-- Countable subadditivity of the Bessel capacity [Fuk93]. -/
theorem iUnion_le (α : ℝ) (p : ℝ≥0∞) (S : ℕ → Set (Rd d)) :
    besselCapacity d α p (⋃ n, S n) ≤ ∑' n, besselCapacity d α p (S n) := by
  sorry

/-- A countable union of `(α, p)`-polar sets is `(α, p)`-polar. -/
theorem IsNull.iUnion {α : ℝ} {p : ℝ≥0∞} {S : ℕ → Set (Rd d)} (h : ∀ n, IsNull d α (p) (S n)) :
    IsNull d α p (⋃ n, S n) := by
  sorry

/-- Inclusion of exceptional classes [AM71, Thm. 1], as used in Lemma B.1:
every `(2, 1)`-polar set is `(1, 2)`-polar. -/
theorem IsNull.one_two_of_two_one {S : Set (Rd d)} (h : IsNull d 2 1 S) : IsNull d 1 2 S := by
  sorry

/-- Inclusion of exceptional classes [AM71, Thm. 1], as used in Appendix C:
for `p > 1`, every `(2, p)`-polar set is `(1, 2)`-polar. -/
theorem IsNull.one_two_of_two_p {p : ℝ} (hp : 1 < p) {S : Set (Rd d)}
    (h : IsNull d 2 (ENNReal.ofReal p) S) : IsNull d 1 2 S := by
  sorry

end besselCapacity

end WeakPathwiseIto
