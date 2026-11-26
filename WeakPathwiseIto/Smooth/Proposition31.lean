/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Smooth.HasQuadraticVariation
public import WeakPathwiseIto.Smooth.PathOscillation
public import WeakPathwiseIto.Smooth.PathwiseCovariation
public import WeakPathwiseIto.Occupation.Lemma42

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace proposition_3_1

variable {T : ℝ} {d : ℕ} {π : ℕ → Partition T}

/-- **Subgoal** (Proposition 3.1 proof: Stieltjes measure of an interval): for `0 ≤ a ≤ b ≤ T`,
`d[x]_π((a, b]) = [x]_π(b) - [x]_π(a)`. -/
theorem stieltjesMeasure_Ioc {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    h.stieltjesMeasure.real (Ioc a b) = h.qv b - h.qv a := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof, convergence of `I_1^n`, grid step): with the grid
`s_k = k t / K` and `g` continuous on `[0,T]` varying by at most `η` over distances `≤ t/K` in
`[0,t]`, `|∫_0^t g d[x]_π - ∑_{k<K} g(s_{k+1}) ([x](s_{k+1}) - [x](s_k))| ≤ η ([x](t) - [x](0))`. -/
theorem abs_integral_sub_grid_le {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {t : ℝ}
    (ht : t ∈ Icc 0 T) {K : ℕ} (hK : 0 < K) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 T)) {η : ℝ}
    (hη : ∀ y ∈ Icc 0 t, ∀ z ∈ Icc 0 t, |y - z| ≤ t / K → |g y - g z| ≤ η) :
    |h.integral g t - ∑ k ∈ Finset.range K, g ((k + 1 : ℕ) * t / K) *
        (h.qv ((k + 1 : ℕ) * t / K) - h.qv ((k : ℕ) * t / K))| ≤ η * (h.qv t - h.qv 0) := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof, convergence of `I_1^n`, [CF10]): for `g` continuous on
`[0,T]` and `t ∈ [0,T]`, `∑_{t_{k+1} ≤ t} g(t_{k+1}) (x(t_{k+1}) - x(t_k))² → ∫_0^t g d[x]_π`
(weak convergence of the discrete quadratic-variation measures). -/
theorem tendsto_riemannStieltjes {x : ℝ → ℝ} (h : HasScalarQuadraticVariation π x) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      g ((π n).right k) * (x ((π n).right k) - x ((π n).left k)) ^ 2)
      atTop (𝓝 (h.integral g t)) := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof, (6)): for `s ∈ [t_k, t_{k+1}]`,
`|ω(s) - ω(t_k)| ≤ osc(ω, π_n)`. -/
theorem norm_sub_left_le {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T)) (p : Partition T)
    (i : Fin p.m) {s : ℝ} (hs : s ∈ Icc (p.left i) (p.right i)) :
    ‖ω s - ω (p.left i)‖ ≤ pathOscillation ω p := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof, Newton–Leibniz remainder `r_k^n`): if
`|∇f(z) - ∇f(y)| ≤ ε` on the segment `[x, y]`, then `|f(y) - f(x) - ∇f(y)(y - x)| ≤ ε |y - x|`. -/
theorem norm_taylor_le {f : Rd d → Rd d} (hf : Differentiable ℝ f) {x y : Rd d} {ε : ℝ}
    (hε : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ ε) :
    ‖f y - f x - fderiv ℝ f y (y - x)‖ ≤ ε * ‖y - x‖ := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof: splitting the discrete covariation): the stopped sum
equals the sum over complete intervals `t_{k+1} ≤ t` plus the straddling interval
`t_k < t < t_{k+1}`. -/
theorem riemannSum_eq (p : Partition T) (f : Rd d → Rd d) (ω : ℝ → Rd d) (t : ℝ) :
    pathwiseCovariation.riemannSum p f ω t =
      ∑ k ∈ Finset.univ.filter (fun k => p.right k ≤ t),
        ⟪f (ω (p.right k)) - f (ω (p.left k)), ω (p.right k) - ω (p.left k)⟫ +
      ∑ k ∈ Finset.univ.filter (fun k => p.left k < t ∧ t < p.right k),
        ⟪f (ω t) - f (ω (p.left k)), ω t - ω (p.left k)⟫ := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof, `⟨∇f, δω ᵗδω⟩` by polarization):
`⟨A v, v⟩ = ∑_{i,j} A_{ij} ((v_i + v_j)² - v_i² - v_j²) / 2`. -/
theorem inner_apply_eq (A : Rd d →L[ℝ] Rd d) (v : Rd d) :
    ⟪A v, v⟫ = ∑ i, ∑ j, Rd.coord i (A (Rd.basisVec j)) *
      ((Rd.coord i v + Rd.coord j v) ^ 2 - Rd.coord i v ^ 2 - Rd.coord j v ^ 2) / 2 := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof: `I_1^n(t) → ∫_0^t ⟨∇f(ω(u)), d[ω]_π(u)⟩`). -/
theorem tendsto_main {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
        ω ((π n).right k) - ω ((π n).left k)⟫) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof: `I_2^n(t) → 0`, `|δω · r| ≤ ρ_{∇f}(osc) |δω|²`). -/
theorem tendsto_remainder {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hQV : HasQuadraticVariation π ω) (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d}
    (hf : ContDiffBounded 1 f) (t : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).right k ≤ t),
      (⟪f (ω ((π n).right k)) - f (ω ((π n).left k)), ω ((π n).right k) - ω ((π n).left k)⟫ -
        ⟪fderiv ℝ f (ω ((π n).right k)) (ω ((π n).right k) - ω ((π n).left k)),
          ω ((π n).right k) - ω ((π n).left k)⟫)) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Proposition 3.1 proof: the straddling interval `t_k < t < t_{k+1}` contributes
at most `sup |∇f| · osc(ω, π_n)² → 0`). -/
theorem tendsto_boundary {ω : ℝ → Rd d} (hω : ContinuousOn ω (Icc 0 T))
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∑ k ∈ Finset.univ.filter (fun k => (π n).left k < t ∧ t < (π n).right k),
      ⟪f (ω t) - f (ω ((π n).left k)), ω t - ω ((π n).left k)⟫) atTop (𝓝 0) := by
  sorry

end proposition_3_1

/-- **Proposition 3.1.** Let `ω ∈ C^0([0,T], ℝ^d) ∩ Q^π` satisfy (6). For `f ∈ C^1_b(ℝ^d, ℝ^d)`
the limit `[f(ω), ω]_π(t)` exists and equals `∫_0^t ⟨∇f(ω(u)), d[ω]_π(u)⟩`. -/
theorem proposition_3_1 {T : ℝ} {d : ℕ} {π : ℕ → Partition T} {ω : ℝ → Rd d}
    (hω : ContinuousOn ω (Icc 0 T)) (hQV : HasQuadraticVariation π ω)
    (hosc : pathOscillation.Vanishes ω π) {f : Rd d → Rd d} (hf : ContDiffBounded 1 f) :
    ∀ t ∈ Icc 0 T, Tendsto (fun n => pathwiseCovariation.riemannSum (π n) f ω t) atTop
      (𝓝 (hQV.matrixIntegral (fun u i j => Rd.coord i (fderiv ℝ f (ω u) (Rd.basisVec j))) t)) := by
  sorry

end WeakPathwiseIto
