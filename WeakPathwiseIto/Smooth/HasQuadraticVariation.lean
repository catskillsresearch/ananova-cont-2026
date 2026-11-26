/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd
public import WeakPathwiseIto.Smooth.HasScalarQuadraticVariation

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- A path `ω = (ω^1, …, ω^d)` has finite quadratic variation along `π` (Section 3): every
`ω^i` and every `ω^i + ω^j` has finite quadratic variation along `π`. The quadratic
covariation `[ω]_{ij}` is then obtained by polarization. -/
structure HasQuadraticVariation {T : ℝ} {d : ℕ} (π : ℕ → Partition T) (ω : ℝ → Rd d) where
  coord : ∀ i : Fin d, HasScalarQuadraticVariation π (fun t => Rd.coord i (ω t))
  pair : ∀ i j : Fin d,
    HasScalarQuadraticVariation π (fun t => Rd.coord i (ω t) + Rd.coord j (ω t))

namespace HasQuadraticVariation

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d} (h : HasQuadraticVariation π ω)

/-- The quadratic covariation `[ω]_{ij} = ([ω^i + ω^j] - [ω^i] - [ω^j]) / 2`. -/
def covariation (i j : Fin d) (t : ℝ) : ℝ :=
  ((h.pair i j).qv t - (h.coord i).qv t - (h.coord j).qv t) / 2

/-- The trace `tr [ω]_π(t) = ∑_i [ω^i]_π(t)`. -/
def trace (t : ℝ) : ℝ := ∑ i, (h.coord i).qv t

theorem trace_monotone : Monotone h.trace := fun _ _ hab =>
  Finset.sum_le_sum fun i _ => (h.coord i).monotone hab

/-- The Stieltjes measure `d tr[ω]_π`. -/
def traceMeasure : Measure ℝ := h.trace_monotone.stieltjesFunction.measure

/-- The matrix Stieltjes integral `∫_0^t ⟨G(u), d[ω]_π(u)⟩ = ∑_{i,j} ∫_0^t G_{ij}(u) d[ω]_{ij}(u)`,
computed by polarization. -/
def matrixIntegral (G : ℝ → Fin d → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, ((h.pair i j).integral (fun u => G u i j) t - (h.coord i).integral (fun u => G u i j) t -
    (h.coord j).integral (fun u => G u i j) t) / 2

open scoped Classical in
/-- Section 3: the discrete cross sums
`∑_{t_{k+1} ≤ t} (ω^i(t_{k+1}) - ω^i(t_k))(ω^j(t_{k+1}) - ω^j(t_k))` converge to `[ω]_{ij}(t)`. -/
theorem tendsto_cross (i j : Fin d) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      (Rd.coord i (ω ((π n).right k)) - Rd.coord i (ω ((π n).left k))) *
        (Rd.coord j (ω ((π n).right k)) - Rd.coord j (ω ((π n).left k))))
      atTop (𝓝 (h.covariation i j t)) := by
  sorry

end HasQuadraticVariation

end WeakPathwiseIto
