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

namespace IsWeakDerivative

variable {d : ℕ}

/-- The order `|α| = α_1 + ⋯ + α_d` of a multi-index `α`. -/
def order (α : Fin d → ℕ) : ℕ := ∑ i, α i

/-- The list of directions `e_1 (α_1 times), …, e_d (α_d times)` of a multi-index `α`. -/
def directions (α : Fin d → ℕ) : List (Rd d) :=
  (List.finRange d).flatMap fun i => List.replicate (α i) (Rd.basisVec i)

/-- The classical partial derivative `D^α φ` of a smooth test function. -/
def testDeriv (α : Fin d → ℕ) (φ : Rd d → ℝ) (x : Rd d) : ℝ :=
  iteratedFDeriv ℝ (directions α).length φ x (fun k => (directions α).get k)

end IsWeakDerivative

/-- `g` is the weak derivative `D^α f` of `f` (Section 2.1): both are locally integrable and
`∫ f D^α φ = (-1)^{|α|} ∫ g φ` for all smooth compactly supported test functions `φ`. -/
def IsWeakDerivative {d : ℕ} (α : Fin d → ℕ) (f g : Rd d → ℝ) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable g ∧
    ∀ φ : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * IsWeakDerivative.testDeriv α φ x =
        (-1) ^ IsWeakDerivative.order α * ∫ x, g x * φ x

end WeakPathwiseIto
