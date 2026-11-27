/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Main.Proposition53Steps
public import WeakPathwiseIto.Main.IsL2ItoIntegral
public import WeakPathwiseIto.Main.DoobL2

/-! # The standard `L²` Itô integral used in the proof of Proposition 5.3

The paper invokes the standard `L²` stochastic integral (for the stopped integrals `J^R`, for
`J_m`, and for `D_m^R`) and the Burkholder–Davis–Gundy inequality. Neither is in Mathlib or the
vendored code for the `d`-dimensional canonical process, so they are built here.

* **L2.M** (martingale structure): increments are orthogonal to the past; conditional
  expectation of an elementary integral; common refinement of two elementary integrands;
  the isometry in `∫⁻` form; uniqueness of the `L²` integral; `E[I(t) | 𝓕_{t'}] = I(t')`.
* **L2.BDG** (`p = 2`): Doob's `L²` inequality along finite time sets, then the supremum over
  `[0, T]` by path continuity; this proves `proposition_5_3.bdg_two` with `C = 4`.
* **L2.E** (existence): density of elementary integrands in `L²(dℙ ⊗ ds)` for progressive
  integrands (bounded continuous adapted; bounded progressive; truncation), existence at a fixed
  time, and a version with continuous paths on `[0, T]`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace itoL2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (L2.M, increments are orthogonal to the past): for `a ≤ c ≤ b ≤ T`,
`ξ ∈ L²` `𝓕_a`-measurable and `A ∈ 𝓕_c`, `∫_A ⟨ξ, B(b) - B(c)⟩ dℙ_x = 0`. -/
theorem setIntegral_inner_increment_eq_zero (x : Rd d) {a b c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hcb : c ≤ b) (hb : b ≤ T) {ξ : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T a] ξ)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) {A : Set (CanonicalWienerSpace d T)}
    (hA : MeasurableSet[IsItoIntegral.naturalSigma d T c] A) :
    ∫ ω in A, ⟪ξ ω, CanonicalWienerSpace.B b ω - CanonicalWienerSpace.B c ω⟫
      ∂CanonicalWienerSpace.P (T := T) x = 0 := by
  sorry

/-- **Subgoal** (L2.M, conditional expectation of an elementary integral): for `0 ≤ r ≤ T`,
`E[∫_0^{s_k} H dB | 𝓕_r] = ∫_0^{s_k ∧ r} H dB` for an elementary predictable `H`. -/
theorem condExp_elementaryIntegral (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T) {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    (hξ2 : ∀ j, MemLp (ξ j) 2 (CanonicalWienerSpace.P (T := T) x)) {r : ℝ} (hr : 0 ≤ r)
    (hrT : r ≤ T) :
    (CanonicalWienerSpace.P (T := T) x)[IsItoIntegral.elementaryIntegral s ξ |
        IsItoIntegral.naturalSigma d T r] =ᵐ[CanonicalWienerSpace.P (T := T) x]
      IsItoIntegral.elementaryIntegral (fun j => min (s j) r) ξ := by
  sorry

/-- **Subgoal** (L2.M, common refinement): the difference of two elementary integrands on grids
of `[0, t]` is an elementary integrand on the merged grid, and the elementary integrals
subtract. -/
theorem exists_elementary_sub (x : Rd d) {t : ℝ} {k k' : ℕ} {s : Fin (k + 1) → ℝ}
    {s' : Fin (k' + 1) → ℝ} (hs : Monotone s) (hs0 : s 0 = 0) (hst : s (Fin.last k) = t)
    (hs' : Monotone s') (hs0' : s' 0 = 0) (hst' : s' (Fin.last k') = t)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d} {ξ' : Fin k' → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    (hξ' : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s' j.castSucc)] (ξ' j))
    (hξ2 : ∀ j, MemLp (ξ j) 2 (CanonicalWienerSpace.P (T := T) x))
    (hξ2' : ∀ j, MemLp (ξ' j) 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∃ (k'' : ℕ) (s'' : Fin (k'' + 1) → ℝ) (ξ'' : Fin k'' → CanonicalWienerSpace d T → Rd d),
      Monotone s'' ∧ s'' 0 = 0 ∧ s'' (Fin.last k'') = t ∧
      (∀ j, Measurable[IsItoIntegral.naturalSigma d T (s'' j.castSucc)] (ξ'' j)) ∧
      (∀ j, MemLp (ξ'' j) 2 (CanonicalWienerSpace.P (T := T) x)) ∧
      (∀ ω, IsItoIntegral.elementaryIntegral s'' ξ'' ω =
        IsItoIntegral.elementaryIntegral s ξ ω - IsItoIntegral.elementaryIntegral s' ξ' ω) ∧
      ∀ u ω, IsItoIntegral.elementaryValue s'' ξ'' u ω =
        IsItoIntegral.elementaryValue s ξ u ω - IsItoIntegral.elementaryValue s' ξ' u ω := by
  sorry

/-- **Subgoal** (L2.M, the elementary isometry in `∫⁻` form on `(0, s_k]`). -/
theorem lintegral_elementaryIntegral_sq (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ}
    (hs : Monotone s) (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    (hξ2 : ∀ j, MemLp (ξ j) 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫⁻ ω, ‖IsItoIntegral.elementaryIntegral s ξ ω‖ₑ ^ 2 ∂CanonicalWienerSpace.P (T := T) x =
      ∫⁻ ω, (∫⁻ u in Ioc 0 (s (Fin.last k)), ‖IsItoIntegral.elementaryValue s ξ u ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (L2.M, uniqueness): the `L²` stochastic integral at a time `t ∈ [0, T]` is unique
up to `ℙ_x`-null sets. -/
theorem isL2ItoIntegral_unique (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d} {t : ℝ}
    (ht : t ∈ Icc 0 T) {I I' : CanonicalWienerSpace d T → ℝ} (hI : IsL2ItoIntegral x H t I)
    (hI' : IsL2ItoIntegral x H t I') : I =ᵐ[CanonicalWienerSpace.P (T := T) x] I' := by
  sorry

/-- **Subgoal** (L2.M, the isometry for the `L²` integral): `E I(t)² = E ∫_0^t |H(s)|² ds`. -/
theorem lintegral_sq_isL2ItoIntegral (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d}
    {t : ℝ} (ht : t ∈ Icc 0 T) {I : CanonicalWienerSpace d T → ℝ}
    (hI : IsL2ItoIntegral x H t I) :
    ∫⁻ ω, ‖I ω‖ₑ ^ 2 ∂CanonicalWienerSpace.P (T := T) x =
      ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (L2.M, martingale property): for `0 ≤ t' ≤ t ≤ T`, `E[I(t) | 𝓕_{t'}] = I(t')`. -/
theorem condExp_isL2ItoIntegral (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d}
    {t t' : ℝ} (ht' : 0 ≤ t') (htt : t' ≤ t) (ht : t ≤ T) {I I' : CanonicalWienerSpace d T → ℝ}
    (hI : IsL2ItoIntegral x H t I) (hI' : IsL2ItoIntegral x H t' I') :
    (CanonicalWienerSpace.P (T := T) x)[I | IsItoIntegral.naturalSigma d T t'] =ᵐ[
      CanonicalWienerSpace.P (T := T) x] I' := by
  sorry

/-- **Subgoal** (L2.BDG, finite time sets): Doob's `L²` inequality along times
`0 ≤ r_0 ≤ ⋯ ≤ r_N ≤ T`: `E max_j |I(r_j)|² ≤ 4 E |I(r_N)|²`. -/
theorem lintegral_sup_sq_finite_le (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d}
    {I : ℝ → CanonicalWienerSpace d T → ℝ}
    (hI : ∀ t ∈ Icc 0 T, IsL2ItoIntegral x H t (I t)) {N : ℕ} {r : Fin (N + 1) → ℝ}
    (hr : Monotone r) (hr0 : 0 ≤ r 0) (hrT : r (Fin.last N) ≤ T) :
    ∫⁻ ω, (⨆ j, ‖I (r j) ω‖ₑ) ^ 2 ∂CanonicalWienerSpace.P (T := T) x ≤
      4 * ∫⁻ ω, ‖I (r (Fin.last N)) ω‖ₑ ^ 2 ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (L2.BDG, `p = 2`): for an `L²` integral process with continuous paths on
`[0, T]`, `E sup_{t ≤ T} |I(t)|² ≤ 4 E ∫_0^T |H(s)|² ds` (finite dyadic time sets increase to a
dense set; continuity and monotone convergence). -/
theorem lintegral_sup_sq_le (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d}
    {I : ℝ → CanonicalWienerSpace d T → ℝ}
    (hI : ∀ t ∈ Icc 0 T, IsL2ItoIntegral x H t (I t))
    (hc : ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => I t ω) (Icc 0 T)) :
    ∫⁻ ω, (⨆ t ∈ Icc 0 T, ‖I t ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x ≤
      4 * ∫⁻ ω, (∫⁻ u in Ioc 0 T, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (L2.E, density for bounded integrands continuous in time): a bounded adapted
`H` with continuous paths is the `L²(dℙ ⊗ ds)` limit on `(0, t]` of the elementary integrands
`H(η_n(s))` along dyadic grids. -/
theorem exists_elementary_approx_of_continuous (x : Rd d) {t : ℝ} (ht : t ∈ Icc 0 T)
    {H : ℝ → CanonicalWienerSpace d T → Rd d} (hH : IsProgressive H) {C : ℝ}
    (hC : ∀ u ω, ‖H u ω‖ ≤ C) (hcont : ∀ ω, Continuous fun u => H u ω) :
    ∃ (k : ℕ → ℕ) (s : ∀ n, Fin (k n + 1) → ℝ)
      (ξ : ∀ n, Fin (k n) → CanonicalWienerSpace d T → Rd d),
      (∀ n, Monotone (s n) ∧ s n 0 = 0 ∧ s n (Fin.last (k n)) = t) ∧
      (∀ n j, Measurable[IsItoIntegral.naturalSigma d T (s n j.castSucc)] (ξ n j)) ∧
      (∀ n j, MemLp (ξ n j) 2 (CanonicalWienerSpace.P (T := T) x)) ∧
      Tendsto (fun n => ∫⁻ ω, (∫⁻ u in Ioc 0 t,
          ‖IsItoIntegral.elementaryValue (s n) (ξ n) u ω - H u ω‖ₑ ^ 2)
          ∂CanonicalWienerSpace.P (T := T) x) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (L2.E, bounded progressive ⇒ continuous in time): a bounded progressive `H` is
the `L²(dℙ ⊗ ds)` limit on `(0, t]` of the bounded progressive processes with continuous paths
`H_n(u) = n ∫_{(u - 1/n) ∨ 0}^u H(v) dv`. -/
theorem exists_continuous_approx_of_bounded (x : Rd d) {t : ℝ} (ht : t ∈ Icc 0 T)
    {H : ℝ → CanonicalWienerSpace d T → Rd d} (hH : IsProgressive H) {C : ℝ}
    (hC : ∀ u ω, ‖H u ω‖ ≤ C) :
    ∃ Hn : ℕ → ℝ → CanonicalWienerSpace d T → Rd d, (∀ n, IsProgressive (Hn n)) ∧
      (∀ n u ω, ‖Hn n u ω‖ ≤ C) ∧ (∀ n ω, Continuous fun u => Hn n u ω) ∧
      Tendsto (fun n => ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖Hn n u ω - H u ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (L2.E, truncation): a progressive `H` with `E ∫_0^t |H|² < ∞` is the
`L²(dℙ ⊗ ds)` limit on `(0, t]` of its bounded truncations. -/
theorem exists_bounded_approx (x : Rd d) {t : ℝ} {H : ℝ → CanonicalWienerSpace d T → Rd d}
    (hH : IsProgressive H)
    (hE : ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x < ∞) :
    ∃ Hn : ℕ → ℝ → CanonicalWienerSpace d T → Rd d, (∀ n, IsProgressive (Hn n)) ∧
      (∀ n, ∃ C, ∀ u ω, ‖Hn n u ω‖ ≤ C) ∧
      Tendsto (fun n => ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖Hn n u ω - H u ω‖ₑ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (L2.E, density): elementary predictable integrands are dense in the progressive
`L²(dℙ ⊗ ds)` on `(0, t]`. -/
theorem exists_elementary_approx (x : Rd d) {t : ℝ} (ht : t ∈ Icc 0 T)
    {H : ℝ → CanonicalWienerSpace d T → Rd d} (hH : IsProgressive H)
    (hE : ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x < ∞) :
    ∃ (k : ℕ → ℕ) (s : ∀ n, Fin (k n + 1) → ℝ)
      (ξ : ∀ n, Fin (k n) → CanonicalWienerSpace d T → Rd d),
      (∀ n, Monotone (s n) ∧ s n 0 = 0 ∧ s n (Fin.last (k n)) = t) ∧
      (∀ n j, Measurable[IsItoIntegral.naturalSigma d T (s n j.castSucc)] (ξ n j)) ∧
      (∀ n j, MemLp (ξ n j) 2 (CanonicalWienerSpace.P (T := T) x)) ∧
      Tendsto (fun n => ∫⁻ ω, (∫⁻ u in Ioc 0 t,
          ‖IsItoIntegral.elementaryValue (s n) (ξ n) u ω - H u ω‖ₑ ^ 2)
          ∂CanonicalWienerSpace.P (T := T) x) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (L2.E, existence at a fixed time): the elementary integrals of an approximating
sequence are Cauchy in `L²(ℙ_x)` by the isometry; their limit is the `L²` integral. -/
theorem exists_isL2ItoIntegral (x : Rd d) {t : ℝ} (ht : t ∈ Icc 0 T)
    {H : ℝ → CanonicalWienerSpace d T → Rd d} (hH : IsProgressive H)
    (hE : ∫⁻ ω, (∫⁻ u in Ioc 0 t, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x < ∞) :
    ∃ I : CanonicalWienerSpace d T → ℝ, IsL2ItoIntegral x H t I := by
  sorry

/-- **Subgoal** (L2.E, continuous version): the `L²` integral process has a version with
continuous paths on `[0, T]` (elementary integral processes are continuous; Doob's `L²`
inequality and Borel–Cantelli along a fast subsequence give uniform convergence). -/
theorem exists_continuous_isL2ItoIntegral (x : Rd d) {H : ℝ → CanonicalWienerSpace d T → Rd d}
    (hH : IsProgressive H)
    (hE : ∫⁻ ω, (∫⁻ u in Ioc 0 T, ‖H u ω‖ₑ ^ 2) ∂CanonicalWienerSpace.P (T := T) x < ∞) :
    ∃ J : ℝ → CanonicalWienerSpace d T → ℝ,
      (∀ t ∈ Icc 0 T, IsL2ItoIntegral x H t (J t)) ∧
      ∀ᵐ ω ∂CanonicalWienerSpace.P (T := T) x, ContinuousOn (fun t => J t ω) (Icc 0 T) := by
  sorry

end itoL2

end WeakPathwiseIto
