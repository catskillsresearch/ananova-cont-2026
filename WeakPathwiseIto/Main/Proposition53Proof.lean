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
public import WeakPathwiseIto.Main.PartitionEta
public import WeakPathwiseIto.Appendix.LemmaB1
public import WeakPathwiseIto.Appendix.HeatKernel
public import WeakPathwiseIto.Sobolev.MemWLoc
public import WeakPathwiseIto.Sobolev.IsWeakGradient
public import WeakPathwiseIto.Smooth.FollmerIntegral

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

/-- **Subgoal** (P53.D, Assumption 2 ⇒ summable mesh): `∑_n |π_n| < ∞` (eq. (30)). -/
theorem summable_mesh {π : ℕ → Partition T} (hT : 0 < T) (h2 : GeometricMeshDecay π) :
    Summable fun n => (π n).mesh :=
  (summable_nat_add_iff 1).1 (h2.summable_mesh hT)

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

/-- **Subgoal** (P53.C, `H_R ∈ L¹`): for Borel `g_m`, `G` with
`∑_m ‖g_m - G‖²_{L²(B_R)} < ∞`, the function `H_R := 1_{B_R} ∑_m |g_m - G|²` has finite
integral (Tonelli). The paper takes `g_m = ∇F_m`, `G` a finite-valued Borel representative
of `∇F`. -/
theorem lintegral_HR_lt_top (g : ℕ → Rd d → Rd d) (G : Rd d → Rd d) (hg : ∀ m, Measurable (g m))
    (hG : Measurable G) (R : ℕ)
    (h : ∑' m, ∫⁻ y in Metric.ball (0 : Rd d) R, ‖g m y - G y‖ₑ ^ 2 < ∞) :
    ∫⁻ y in Metric.ball (0 : Rd d) R, ∑' m, ‖g m y - G y‖ₑ ^ 2 < ∞ := by
  sorry

/-- **Subgoal** (P53.C, `G_R ∈ L¹`): since `∇F ∈ L²_loc` (`F ∈ W^{1,2}_loc`),
`G_R := 1_{B_R} |∇F|²` has finite integral. -/
theorem lintegral_GR_lt_top {F : Rd d → ℝ} (hFloc : MemWLoc 1 2 F) {G : Rd d → Rd d}
    (hG : IsWeakGradient F G) (R : ℕ) :
    ∫⁻ y in Metric.ball (0 : Rd d) R, ‖G y‖ₑ ^ 2 < ∞ := by
  sorry

/-- **Subgoal** (P53.C, the polar set `E_1` via Lemma B.1): for families `H_R`, `G_R` (`R ≥ 1`)
of finite integral, Lemma B.1 gives polar sets `E_R^1`, `E_R^2` with
`∫ H_R(x) ν(|x - x₀|) dx < ∞` for `x₀ ∉ E_R^1` and `∫ G_R(x) ν(|x - x₀|) dx < ∞` for
`x₀ ∉ E_R^2`; `E_1 := ⋃_{R ≥ 1} (E_R^1 ∪ E_R^2)` is polar. -/
theorem exists_polar_E1 (HR GR : ℕ → Rd d → ℝ≥0∞) (hHm : ∀ R, Measurable (HR R))
    (hGm : ∀ R, Measurable (GR R)) (hH : ∀ R, 1 ≤ R → ∫⁻ x, HR R x < ∞)
    (hG : ∀ R, 1 ≤ R → ∫⁻ x, GR R x < ∞) :
    ∃ E₁ : Set (Rd d), IsBrownianPolar d T E₁ ∧ ∀ x₀ ∉ E₁, ∀ R : ℕ, 1 ≤ R →
      ∫⁻ x, HR R x * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) < ∞ ∧
      ∫⁻ x, GR R x * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) < ∞ := by
  sorry

/-- **Subgoal** (P53.C, stopped energy via the Brownian transition density and eq. (32)
`∫_0^T p_s(x) ds ≤ C(R) ν(|x|)`; the paper cites it as "estimate (46)", a dangling reference):
`E_{x₀} ∫_0^{T∧τ_R} f(B(s)) ds ≤ ∫_{B_R} f(x) ∫_0^T p_s(x - x₀) ds dx
≤ C_{R,x₀} ∫_{B_R} f(x) ν(|x - x₀|) dx`. -/
theorem lintegral_stopped_le_potential (hd : 1 ≤ d) (x₀ : Rd d) (R : ℕ) :
    ∃ C : ℝ≥0, ∀ f : Rd d → ℝ≥0∞, Measurable f →
      ∫⁻ ω, (∫⁻ u in Ioc 0 T,
          if ENNReal.ofReal u ≤ CanonicalWienerSpace.exitTime R ω
          then f (CanonicalWienerSpace.path ω u) else 0) ∂CanonicalWienerSpace.P (T := T) x₀ ≤
        C * ∫⁻ x in Metric.ball (0 : Rd d) R,
          f x * ENNReal.ofReal (potentialProfile d ‖x - x₀‖) := by
  sorry

/-- **Subgoal** (P53.C, the local Itô integral `J`): if `E ∫_0^{T∧τ_R} |G(B(s))|² ds < ∞` for
every `R ≥ 1`, the stopped stochastic integrals `J^R(t) := ∫_0^{t∧τ_R} G(B(s)) dB(s)` are well
defined, consistent under stopping, and (`τ_R ↑ ∞`) define the local Itô integral
`J(t) = ∫_0^t G(B(s)) dB(s)`, `t ∈ [0, T]`. -/
theorem exists_isLocalItoIntegral (x₀ : Rd d) {G : Rd d → Rd d} (hG : Measurable G)
    (h : ∀ R : ℕ, 1 ≤ R → ∫⁻ ω, (∫⁻ u in Ioc 0 T,
      ‖stoppedIntegrand (fun u ω => G (CanonicalWienerSpace.path ω u)) R u ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x₀ < ∞) :
    ∃ J : ℝ → CanonicalWienerSpace d T → ℝ,
      IsLocalItoIntegral x₀ (fun u ω => G (CanonicalWienerSpace.path ω u)) J := by
  sorry

/-- **Subgoal** (P53.D, `S_n^m` is an elementary integral): since the integrand is a
predictable step process, `S(t) = ∫_0^t g(B(η(s))) dB(s)` (the paper's
`S_n^m(t) = ∫_0^t ∇F_m(B(η_n(s))) dB(s)`). -/
theorem isL2ItoIntegral_itoRiemannSum (x : Rd d) (π : Partition T) {g : Rd d → Rd d}
    (hg : Continuous g) (hgb : ∃ C, ∀ y, ‖g y‖ ≤ C) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsL2ItoIntegral x (fun u ω => g (CanonicalWienerSpace.path ω (π.eta u))) t
      (itoRiemannSum π g t) := by
  sorry

/-- **Subgoal** (P53.D, the last step of the BDG bound):
`E ∫_0^T |B(η(s)) - B(s)|² ds ≤ d T |π|` (the source of `C_{d,T} |π_n|`). -/
theorem lintegral_path_eta_sub_le (x : Rd d) (π : Partition T) :
    ∫⁻ ω, (∫⁻ u in Ioc 0 T,
        ‖CanonicalWienerSpace.path ω (π.eta u) - CanonicalWienerSpace.path ω u‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x ≤ ENNReal.ofReal (d * T * π.mesh) := by
  sorry

/-- **Subgoal** (P53.D, existence of `J_m`): for globally Lipschitz `g` (the paper's `∇F_m`,
`F_m ∈ C^2_b`), `J_m(t) = ∫_0^t g(B(s)) dB(s)` exists as an `L²` stochastic integral with
continuous paths on `[0, T]`. -/
theorem exists_isL2ItoIntegral_of_lipschitz (x : Rd d) {g : Rd d → Rd d} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    ∃ J : ℝ → CanonicalWienerSpace d T → ℝ,
      (∀ t ∈ Icc 0 T, IsL2ItoIntegral x (fun u ω => g (CanonicalWienerSpace.path ω u)) t (J t)) ∧
      ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => J t ω) (Icc 0 T) := by
  sorry

/-- **Subgoal** (P53.D, BDG bound for `S_n^m - J_m`): with `∇F_m` globally Lipschitz
(constant `K`, the paper's `‖∇²F_m‖_∞`),
`E sup_{t ≤ T} |S_n^m(t) - J_m(t)|² ≤ C E ∫_0^T |∇F_m(B(η_n(s))) - ∇F_m(B(s))|² ds
≤ C K² E ∫_0^T |B(η_n(s)) - B(s)|² ds ≤ C K² d T |π_n|`. -/
theorem lintegral_sup_itoRiemannSum_sub_le : ∃ C : ℝ≥0, ∀ (x : Rd d) (π : Partition T)
    (g : Rd d → Rd d) (K : ℝ≥0), LipschitzWith K g →
    ∀ J : ℝ → CanonicalWienerSpace d T → ℝ,
    (∀ t ∈ Icc 0 T, IsL2ItoIntegral x (fun u ω => g (CanonicalWienerSpace.path ω u)) t (J t)) →
    (∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => J t ω) (Icc 0 T)) →
    ∫⁻ ω, (⨆ t ∈ Icc 0 T, ‖itoRiemannSum π g t ω - J t ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x ≤
      C * (K : ℝ≥0∞) ^ 2 * ENNReal.ofReal (d * T * π.mesh) := by
  sorry

/-- **Subgoal** (P53.D, Tonelli for `S_n^m`): by the BDG bound and `∑_n |π_n| < ∞`,
`∑_n E sup_{t ≤ T} |S_n^m(t) - J_m(t)|² < ∞`, so by Tonelli
`sup_{t ≤ T} |S_n^m(t) - J_m(t)| → 0` almost surely. -/
theorem ae_tendsto_sup_itoRiemannSum_sub (hT : 0 < T) {π : ℕ → Partition T}
    (h2 : GeometricMeshDecay π) (x : Rd d) {g : Rd d → Rd d} {K : ℝ≥0} (hg : LipschitzWith K g)
    (J : ℝ → CanonicalWienerSpace d T → ℝ)
    (hJ : ∀ t ∈ Icc 0 T, IsL2ItoIntegral x (fun u ω => g (CanonicalWienerSpace.path ω u)) t (J t))
    (hJc : ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => J t ω) (Icc 0 T)) :
    ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x,
      Tendsto (fun n => ⨆ t ∈ Icc 0 T, ‖itoRiemannSum (π n) g t ω - J t ω‖ₑ) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (P53.D, pathwise integral of `∇F_m` is `J_m`): if for every `m`,
`sup_{t ≤ T} |S_n^m(t) - J_m(t)| → 0` almost surely, then outside one null set (countably many
`m`), `∫_0^t ∇F_m(B(s)) d^π B(s) = J_m(t)` for every `m` and every `t ∈ [0, T]`. -/
theorem ae_follmerIntegral_eq {π : ℕ → Partition T} (x : Rd d) (g : ℕ → Rd d → Rd d)
    (J : ℕ → ℝ → CanonicalWienerSpace d T → ℝ)
    (h : ∀ m, ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x,
      Tendsto (fun n => ⨆ t ∈ Icc 0 T, ‖itoRiemannSum (π n) (g m) t ω - J m t ω‖ₑ) atTop
        (𝓝 0)) :
    ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ∀ m, ∀ t ∈ Icc 0 T,
      follmerIntegral π (g m) (CanonicalWienerSpace.path ω) t = J m t ω := by
  sorry

/-- **Subgoal** (P53.D, `D_m^R → 0`): for `D_m^R(t) := ∫_0^{t∧τ_R} (g_m(B) - G(B)) dB`, BDG and
Tonelli with `∑_m E ∫_0^{T∧τ_R} |g_m(B(s)) - G(B(s))|² ds < ∞` (bounded through `H_R`) give
`sup_{t ≤ T} |D_m^R(t)| → 0` almost surely. -/
theorem ae_tendsto_sup_stopped (x₀ : Rd d) (R : ℕ) (g : ℕ → Rd d → Rd d) (G : Rd d → Rd d)
    (D : ℕ → ℝ → CanonicalWienerSpace d T → ℝ)
    (hD : ∀ m, ∀ t ∈ Icc 0 T, IsL2ItoIntegral x₀ (stoppedIntegrand
      (fun u ω => g m (CanonicalWienerSpace.path ω u) - G (CanonicalWienerSpace.path ω u)) R)
        t (D m t))
    (hDc : ∀ m, ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x₀,
      ContinuousOn (fun t => D m t ω) (Icc 0 T))
    (h : ∑' m, ∫⁻ ω, (∫⁻ u in Ioc 0 T, ‖stoppedIntegrand
      (fun u ω => g m (CanonicalWienerSpace.path ω u) - G (CanonicalWienerSpace.path ω u)) R
        u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x₀ < ∞) :
    ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x₀,
      Tendsto (fun m => ⨆ t ∈ Icc 0 T, ‖D m t ω‖ₑ) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (P53.D, `D_m^R = J_m - J` when `τ_R > T`): almost surely, on paths with
`τ_R = ∞` (the path stays in `B_R` on `[0, T]`), `D_m^R(t) = J_m(t) - J(t)` for `t ∈ [0, T]`. -/
theorem ae_stopped_eq_sub (x₀ : Rd d) {R : ℕ} (hR : 1 ≤ R) (g G : Rd d → Rd d)
    (D Jm J : ℝ → CanonicalWienerSpace d T → ℝ)
    (hD : ∀ t ∈ Icc 0 T, IsL2ItoIntegral x₀ (stoppedIntegrand
      (fun u ω => g (CanonicalWienerSpace.path ω u) - G (CanonicalWienerSpace.path ω u)) R)
        t (D t))
    (hDc : ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x₀, ContinuousOn (fun t => D t ω) (Icc 0 T))
    (hJm : ∀ t ∈ Icc 0 T,
      IsL2ItoIntegral x₀ (fun u ω => g (CanonicalWienerSpace.path ω u)) t (Jm t))
    (hJmc : ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x₀, ContinuousOn (fun t => Jm t ω) (Icc 0 T))
    (hJ : IsLocalItoIntegral x₀ (fun u ω => G (CanonicalWienerSpace.path ω u)) J) :
    ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x₀, CanonicalWienerSpace.exitTime R ω = ⊤ →
      ∀ t ∈ Icc 0 T, D t ω = Jm t ω - J t ω := by
  sorry

end proposition_5_3

end WeakPathwiseIto
