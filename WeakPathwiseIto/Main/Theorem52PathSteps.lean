/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Occupation.OccupationSeminorm
public import WeakPathwiseIto.Appendix.PotentialProfile
public import WeakPathwiseIto.Bessel.CanonicalWienerSpace
public import WeakPathwiseIto.Sobolev.MemW
public import WeakPathwiseIto.Sobolev.IsWeakHessian
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian

/-! # Path-side steps of the proof of Theorem 5.2 (Appendix C)

The first partition interval is treated separately (`J_{m,n}(x₀)`), since the finite-valued
representative `g_m = (M_1 u_m)·1_{N_m^c}` need not dominate `M_1 u_m` at `B(0) = x₀`; the
modified (10)/(11) then give `‖u_m‖_{W⁰_{B,π}} ≤ C_{p,B} limsup_n ‖h_m‖^{1/p}_{n,1,B}` with a
constant independent of `m`. Also: the standard mollifier sequence, measurability and a.e.
finiteness of `M_1`, and the Brownian path facts `B(0) = x₀` and continuity. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Appendix C, `i = 0` increment: the kernel centred at `a = x₀` is kept explicit,
`∫ |f| 𝓛^{n,0} ≤ C (∫_{B̄(a,|b-a|)} |f| |z - a|^{2-d} dz + M_1 f(b) |b - a|²)`). -/
theorem lintegral_piece_le_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (f : Rd d → ℝ) (a b : Rd d),
    AEStronglyMeasurable f → ‖b - a‖ ≤ 1 →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity.piece a b x) ≤
      C * (∫⁻ x in Metric.closedBall a ‖b - a‖, ‖f x‖ₑ * ENNReal.ofReal (‖x - a‖ ^ (2 - (d : ℝ))) +
        localMaximalFunction 1 f b * ENNReal.ofReal (‖b - a‖ ^ 2)) := by
  sorry

/-- **Subgoal** (Appendix C, (10) with the first increment kept explicit): if `g ≥ M_1 f` at the
path's partition points `ω(t_j)`, `j ≥ 1`, then
`∫ |f| 𝓛^π_ω ≤ C (J + ∑_i (g(ω(t_{i+1})) + g(ω(t_i))) |Δω_i|²)`, `J` the kernel integral at `ω(0)`
over the ball of radius `osc(ω, π)`. -/
theorem lintegral_le_maximal_first (d : ℕ) : ∃ C : ℝ≥0, ∀ (π : Partition T) (ω : ℝ → Rd d)
    (f : Rd d → ℝ) (g : Rd d → ℝ≥0∞), ContinuousOn ω (Icc 0 T) → LocallyIntegrable f →
    pathOscillation ω π ≤ 1 →
    (∀ j : Fin (π.m + 1), j ≠ 0 → localMaximalFunction 1 f (ω (π.t j)) ≤ g (ω (π.t j))) →
    ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (discreteOccupationDensity π ω x) ≤
      C * (∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω π),
          ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ))) +
        ∑ i : Fin π.m, (g (ω (π.right i)) + g (ω (π.left i))) *
          ENNReal.ofReal (‖ω (π.right i) - ω (π.left i)‖ ^ 2)) := by
  sorry

/-- **Subgoal** (Appendix C, `‖z - x₀‖^{2-d} ≤ ν(‖z - x₀‖)` on small balls). -/
theorem rpow_le_potentialProfile {r : ℝ} (hr1 : r ≤ 1) :
    r ^ (2 - (d : ℝ)) ≤ potentialProfile d r := by
  sorry

/-- **Subgoal** (Appendix C, `J_{m,n}(x₀) → 0`): if `∫ |f(z)| ν(|z - x₀|) dz < ∞` and the radii
shrink to `0`, the kernel integrals over `B̄(x₀, ρ_n)` tend to `0`. -/
theorem tendsto_lintegral_closedBall_kernel {f : Rd d → ℝ} (hfm : AEStronglyMeasurable f)
    {x₀ : Rd d} (hf : ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) < ⊤)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ (ρ n),
      ‖f x‖ₑ * ENNReal.ofReal (‖x - x₀‖ ^ (2 - (d : ℝ)))) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Appendix C, (11) with the first increment kept explicit: Hölder and
`sup_n ‖ρ_{n,ω}‖_{L^q} < ∞`). The constant depends only on `(π, ω, p)`, not on `f` or `g`. -/
theorem le_limsup_discreteSeminorm_first {p q : ℝ} (hpq : p.HolderConjugate q)
    (π : ℕ → Partition T) (ω : ℝ → Rd d) (hω : ContinuousOn ω (Icc 0 T))
    (hosc : pathOscillation.Vanishes ω π)
    (hρ : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n,
      eLpNorm (normalizedQuadraticDensity (π n) ω) (ENNReal.ofReal q) (volume.restrict (Icc 0 T)) ≤ K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : Rd d → ℝ) (g : Rd d → ℝ≥0∞), LocallyIntegrable f →
      (∀ n, ∀ j : Fin ((π n).m + 1), j ≠ 0 →
        localMaximalFunction 1 f (ω ((π n).t j)) ≤ g (ω ((π n).t j))) →
      Tendsto (fun n => ∫⁻ x in Metric.closedBall (ω 0) (pathOscillation ω (π n)),
          ‖f x‖ₑ * ENNReal.ofReal (‖x - ω 0‖ ^ (2 - (d : ℝ)))) atTop (𝓝 0) →
      occupationSeminorm π ω f ≤ C * limsup (fun n => discreteSeminorm (π n) p g ω) atTop := by
  sorry

/-- **Subgoal** (Appendix C, `‖g‖_{n,p,B} = ‖g^p‖^{1/p}_{n,1,B}` for `g ≥ 0`). -/
theorem discreteSeminorm_enorm_rpow {p : ℝ} (hp : 0 < p) (π : Partition T) {g : Rd d → ℝ}
    (hg : 0 ≤ g) (ω : ℝ → Rd d) :
    discreteSeminorm π p (fun x => ‖g x‖ₑ) ω =
      discreteSeminorm π 1 (fun x => ‖g x ^ p‖ₑ) ω ^ (1 / p) := by
  sorry

/-- **Subgoal** (Appendix C, `M_1 f` is Borel: a supremum of lower semicontinuous ball averages). -/
theorem measurable_localMaximalFunction (f : Rd d → ℝ) :
    Measurable (localMaximalFunction 1 f) := by
  sorry

/-- **Subgoal** (Appendix C, `N_m = {M_1 u_m = ∞}` is Lebesgue-null: `M_1 u_m ∈ L^p`). -/
theorem ae_localMaximalFunction_lt_top {p : ℝ} (hp : 1 < p) {f : Rd d → ℝ}
    (hf : MemLp f (ENNReal.ofReal p)) : ∀ᵐ x, localMaximalFunction 1 f x < ⊤ := by
  sorry

/-- **Subgoal** (Appendix C, `‖h_m‖_{L^1} = ‖g_m‖^p_{L^p} → 0`). -/
theorem tendsto_eLpNorm_rpow_one {p : ℝ} (hp : 0 < p) {g : ℕ → Rd d → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hlim : Tendsto (fun m => eLpNorm (g m) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun x => g m x ^ p) 1 volume) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Appendix C, standard mollifier `η_m(x) = m^d η(m x)`). -/
theorem exists_mollifier (d : ℕ) : ∃ ψ : ℕ → Rd d → ℝ,
    (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
    (∀ n x, 0 ≤ ψ n x) ∧ (∀ n, ∫ x, ψ n x = 1) ∧
    (∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) ∧
    ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d := by
  sorry

/-- **Subgoal** (Appendix C, `u_m ∈ L^1` for Lemma B.1): for `G ∈ C²_b ∩ W^{2,1}` and `F ∈ W^{2,1}`
with weak Hessian `H`, `‖∇²G - H‖` is integrable. -/
theorem integrable_norm_hessian_sub {F G : Rd d → ℝ} (hF : MemW 2 1 F)
    {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H) (hG : ContDiffBounded 2 G)
    (hG1 : MemW 2 1 G) : Integrable fun x => ‖smoothHessian G x - H x‖ := by
  sorry

/-- **Subgoal** (Appendix C, `B(0) = x₀`, `ℙ_{x₀}`-almost surely). -/
theorem ae_path_zero (hT : 0 ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), CanonicalWienerSpace.path ω 0 = x₀ := by
  sorry

/-- **Subgoal** (Appendix C, Brownian paths are continuous on `[0, T]`). -/
theorem continuousOn_path (ω : CanonicalWienerSpace d T) :
    ContinuousOn (CanonicalWienerSpace.path ω) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Icc 0 T).domRestrict (CanonicalWienerSpace.path ω) = ω := by
    funext t
    simp [Set.domRestrict, CanonicalWienerSpace.path, CanonicalWienerSpace.B, t.2]
  rw [h]
  exact ω.continuous

end theorem_5_2

end WeakPathwiseIto
