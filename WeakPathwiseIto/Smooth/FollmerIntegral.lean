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

namespace follmerIntegral

/-- Left Riemann sum `∑_k ⟨g(ω(t_k ∧ t)), ω(t_{k+1} ∧ t) - ω(t_k ∧ t)⟩` along `π_n`. -/
def riemannSum {T : ℝ} {d : ℕ} (π : Partition T) (g : Rd d → Rd d) (ω : ℝ → Rd d) (t : ℝ) : ℝ :=
  ∑ k : Fin π.m, ⟪g (ω (min (π.left k) t)), ω (min (π.right k) t) - ω (min (π.left k) t)⟫

end follmerIntegral

/-- The pathwise (Föllmer) integral `∫_0^t g(ω) d^π ω`, defined as the limit of left Riemann
sums along `(π_n)` (Corollary 3.2, [Föl81]). -/
def follmerIntegral {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (g : Rd d → Rd d) (ω : ℝ → Rd d)
    (t : ℝ) : ℝ :=
  limUnder atTop fun n => follmerIntegral.riemannSum (π n) g ω t

end WeakPathwiseIto
