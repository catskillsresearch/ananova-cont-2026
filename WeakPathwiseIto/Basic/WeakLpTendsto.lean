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

/-- Weak convergence `f_n ⇀ ℓ` in `L^r(ℝ^d)`, read as weak-* convergence when `r = ∞`
(Remarks 4.4 and 4.5): every `f_n` and `ℓ` lie in `L^r`, and `∫ g f_n → ∫ g ℓ` for every
`g ∈ L^{r'}`, `1/r + 1/r' = 1` (so `r' = 1` when `r = ∞`). -/
def WeakLpTendsto {d : ℕ} (r : ℝ≥0∞) (f : ℕ → Rd d → ℝ) (ℓ : Rd d → ℝ) : Prop :=
  (∀ n, MemLp (f n) r) ∧ MemLp ℓ r ∧ ∀ g : Rd d → ℝ, MemLp g r.conjExponent →
    Tendsto (fun n => ∫ x, g x * f n x) atTop (𝓝 (∫ x, g x * ℓ x))

end WeakPathwiseIto
