/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.Proposition53Steps
public import WeakPathwiseIto.Main.IsLocalItoIntegral
public import WeakPathwiseIto.Main.ItoRiemannSum
public import WeakPathwiseIto.Main.GeometricMeshDecay

/-! # Proof of Proposition 5.3, following the paper step by step

* **P53.C** (subsequence and polar set): the deterministic subsequence with
  `∑_m ‖∇F_m - ∇F‖²_{L²(B_R)} < ∞` for every `R`; `H_R`, `G_R ∈ L¹`; the polar sets `E_R^1`,
  `E_R^2` from Lemma B.1; `E E∫_0^{T∧τ_R}|∇F(B)|² < ∞`; existence of the local integral `J`.
* **P53.D** (Riemann sums): `S_n^m` is the elementary integral of `∇F_m(B(η_n))`; BDG (`p = 2`);
  `E sup|S_n^m - J_m|² ≤ C_{d,T} ‖∇²F_m‖²_∞ |π_n|`; `∑_n |π_n| < ∞` (Assumption 2); Tonelli;
  `sup|D_m^R| → 0` a.s. via `H_R`; `τ_R > T` for some `R`.
* **P53.E**: assembly (`proposition_5_3`).

Further stubs of C and D are added as their statements are fixed. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace proposition_5_3

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (P53.C, deterministic subsequence): if `g_m → G` in `L²_loc`, a subsequence
satisfies `∑_m ‖g_m - G‖²_{L²(B_R)} < ∞` for every integer `R ≥ 1` (chosen inductively with
`‖g_m - G‖²_{L²(B_j)} ≤ 2^{-m}`, `1 ≤ j ≤ m`). -/
theorem exists_subseq_summable_L2_ball (g : ℕ → Rd d → Rd d) (G : Rd d → Rd d)
    (h : ∀ R : ℕ, Tendsto (fun m => ∫⁻ y in Metric.ball (0 : Rd d) R, ‖g m y - G y‖ₑ ^ 2)
      atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ R : ℕ, 1 ≤ R →
      ∑' m, ∫⁻ y in Metric.ball (0 : Rd d) R, ‖g (φ m) y - G y‖ₑ ^ 2 < ∞ := by
  sorry

/-- **Subgoal** (P53.D, Assumption 2 ⇒ summable mesh): `∑_n |π_n| < ∞`. -/
theorem summable_mesh {π : ℕ → Partition T} (h2 : GeometricMeshDecay π) :
    Summable fun n => (π n).mesh := by
  sorry

/-- **Subgoal** (P53.D, Burkholder–Davis–Gundy inequality, `p = 2`): there is a universal constant
`C` such that for every `L²` stochastic integral process `I(t) = ∫_0^t H dB`, `t ∈ [0, T]`, with
continuous paths, `E sup_{t ≤ T} |I(t)|² ≤ C E ∫_0^T |H(s)|² ds`. -/
theorem bdg_two : ∃ C : ℝ≥0, ∀ (x : Rd d) (H : ℝ → CanonicalWienerSpace d T → Rd d)
    (I : ℝ → CanonicalWienerSpace d T → ℝ),
    (∀ t ∈ Icc 0 T, IsL2ItoIntegral x H t (I t)) →
    (∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => I t ω) (Icc 0 T)) →
    ∫⁻ ω, (⨆ t ∈ Icc 0 T, ‖I t ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x ≤
      C * ∫⁻ ω, (∫⁻ u in Ioc 0 T, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (P53.D, Tonelli step): if `∑_n E X_n < ∞` for nonnegative `X_n`, then
`∑_n X_n < ∞` almost surely, hence `X_n → 0` almost surely. -/
theorem ae_tendsto_zero_of_tsum_lintegral_lt_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ≥0∞} (hX : ∀ n, AEMeasurable (X n) μ) (h : ∑' n, ∫⁻ ω, X n ω ∂μ < ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (P53.D, `τ_R > T` for some `R`): Brownian paths are bounded on `[0, T]`, so every
path has `τ_R = ∞` for some integer `R ≥ 1`. -/
theorem exists_exitTime_eq_top (ω : CanonicalWienerSpace d T) :
    ∃ R : ℕ, 1 ≤ R ∧ CanonicalWienerSpace.exitTime R ω = ⊤ := by
  sorry

end proposition_5_3

end WeakPathwiseIto
