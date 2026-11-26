/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Basic.Partition

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace pathwiseCovariation

/-- Discrete covariation
`∑_k (f(ω(t_{k+1} ∧ t)) - f(ω(t_k ∧ t))) · (ω(t_{k+1} ∧ t) - ω(t_k ∧ t))` along `π_n`. -/
def riemannSum {T : ℝ} {d : ℕ} (π : Partition T) (f : Rd d → Rd d) (ω : ℝ → Rd d) (t : ℝ) : ℝ :=
  ∑ k : Fin π.m, ⟪f (ω (min (π.right k) t)) - f (ω (min (π.left k) t)),
    ω (min (π.right k) t) - ω (min (π.left k) t)⟫

end pathwiseCovariation

/-- The pathwise covariation `[f(ω), ω]_π(t)` (Proposition 3.1), as the limit of the discrete
covariations along `(π_n)`. -/
def pathwiseCovariation {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (f : Rd d → Rd d) (ω : ℝ → Rd d)
    (t : ℝ) : ℝ :=
  limUnder atTop fun n => pathwiseCovariation.riemannSum (π n) f ω t

end WeakPathwiseIto
