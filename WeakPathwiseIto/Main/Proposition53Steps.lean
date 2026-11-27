/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.WienerLawExists
public import WeakPathwiseIto.Main.IsItoIntegral

/-! # Steps of the proof of Proposition 5.3

Route A (approved): a direct `d`-dimensional elementary Itô calculus for the canonical process
`B` under `ℙ_x` and its natural filtration.

* **P53.A** (this file, first part): `B` under `ℙ_x` has increments independent of the past
  `𝓕_s = σ(B(v) : v ≤ s)`, with covariance `(t - s) I`; hence the elementary isometry inputs
  `E⟨ξ, B_t - B_s⟩² = (t - s) E|ξ|²` and the vanishing of cross terms.
* **P53.B**: elementary isometry and localisation (stubs below); limit in probability.
* **P53.C**: `∇F_m(B) → G(B)` in `L²(ds)` in probability, off a polar set.
* **P53.D**: Riemann sums along `π` converge in probability to the Itô integral.
* **P53.E**: assembly (`proposition_5_3`). -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace proposition_5_3

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (P53.A, independent Brownian coordinates: the joint past is independent of the
joint future increments). For independent real Brownian motions `W^1, …, W^d` and `s ≥ 0`, the
past `(W^i_v)_{i, v ≤ s}` is independent of the shifted increments `(W^i_{s+u} - W^i_s)_{i, u}`. -/
theorem indepFun_coords_past_shift {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Fin d → ℝ≥0 → Ω' → ℝ}
    (hB : ∀ i, IsBrownianReal (W i) Q)
    (hind : iIndepFun (fun i ω' t => W i t ω') Q) (s : ℝ≥0) :
    IndepFun (fun ω' (i : Fin d) (v : Iic s) => W i v ω')
      (fun ω' (i : Fin d) (u : ℝ≥0) => W i (s + u) ω' - W i s ω') Q := by
  sorry

/-- **Subgoal** (P53.A, canonical space): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, the past path
`(B(v))_{v ≤ s}` is independent of the increment `B(t) - B(s)`. -/
theorem indepFun_past_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IndepFun (fun (ω : CanonicalWienerSpace d T) (v : {v : Icc (0 : ℝ) T // (v : ℝ) ≤ s}) => ω v)
      (fun ω => CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
      (CanonicalWienerSpace.P (T := T) x) := by
  sorry

/-- **Subgoal** (P53.A): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, `B(t) - B(s)` is independent of the
natural `σ`-algebra `𝓕_s`. -/
theorem indep_naturalSigma_increment (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) :
    Indep (IsItoIntegral.naturalSigma d T s)
      (MeasurableSpace.comap (fun ω : CanonicalWienerSpace d T =>
        CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) inferInstance)
      (CanonicalWienerSpace.P (T := T) x) := by
  sorry

/-- **Subgoal** (P53.A, increment moments): under `ℙ_x`, for `0 ≤ s ≤ t ≤ T`, the increment
`B(t) - B(s)` is square integrable, centred, with covariance `(t - s) I`. -/
theorem increment_moments (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    MemLp (fun ω : CanonicalWienerSpace d T =>
        CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) 2 (CanonicalWienerSpace.P (T := T) x) ∧
      (∀ i, ∫ ω, Rd.coord i (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
        ∂CanonicalWienerSpace.P (T := T) x = 0) ∧
      ∀ i j, ∫ ω, Rd.coord i (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω) *
          Rd.coord j (CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω)
          ∂CanonicalWienerSpace.P (T := T) x = if i = j then t - s else 0 := by
  sorry

/-- **Subgoal** (P53.A, one-step isometry): for `0 ≤ s ≤ t ≤ T` and `ξ ∈ L²(ℙ_x)`
`𝓕_s`-measurable, `E⟨ξ, B(t) - B(s)⟩² = (t - s) E|ξ|²`. -/
theorem integral_inner_increment_sq (x : Rd d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) {ξ : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T s] ξ)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ ^ 2
        ∂CanonicalWienerSpace.P (T := T) x =
      (t - s) * ∫ ω, ‖ξ ω‖ ^ 2 ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (P53.A, cross terms): for `0 ≤ s ≤ t ≤ s' ≤ t' ≤ T`, `ξ ∈ L²` `𝓕_s`-measurable
and `η ∈ L²` `𝓕_{s'}`-measurable, `E[⟨ξ, B(t) - B(s)⟩ ⟨η, B(t') - B(s')⟩] = 0`. -/
theorem integral_inner_increment_mul_eq_zero (x : Rd d) {s t s' t' : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hts' : t ≤ s') (hst' : s' ≤ t') (ht' : t' ≤ T)
    {ξ η : CanonicalWienerSpace d T → Rd d}
    (hξ : Measurable[IsItoIntegral.naturalSigma d T s] ξ)
    (hη : Measurable[IsItoIntegral.naturalSigma d T s'] η)
    (hξ2 : MemLp ξ 2 (CanonicalWienerSpace.P (T := T) x)) (hη2 : MemLp η 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, ⟪ξ ω, CanonicalWienerSpace.B t ω - CanonicalWienerSpace.B s ω⟫ *
        ⟪η ω, CanonicalWienerSpace.B t' ω - CanonicalWienerSpace.B s' ω⟫
        ∂CanonicalWienerSpace.P (T := T) x = 0 := by
  sorry

/-- **Subgoal** (P53.B, elementary Itô isometry): for an adapted elementary integrand with
`L²` values on a grid `0 = s_0 ≤ … ≤ s_k = t ≤ T`,
`E[(∫ H dB)²] = E ∫_0^t |H(u)|² du`. -/
theorem elementary_isometry (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    (hξ2 : ∀ j, MemLp (ξ j) 2 (CanonicalWienerSpace.P (T := T) x)) :
    ∫ ω, IsItoIntegral.elementaryIntegral s ξ ω ^ 2 ∂CanonicalWienerSpace.P (T := T) x =
      ∫ ω, (∫ u in (0 : ℝ)..s (Fin.last k), ‖IsItoIntegral.elementaryValue s ξ u ω‖ ^ 2)
        ∂CanonicalWienerSpace.P (T := T) x := by
  sorry

/-- **Subgoal** (P53.B, localisation): for an adapted elementary integrand on
`0 = s_0 ≤ … ≤ s_k ≤ T` and `ε, δ > 0`,
`ℙ(|∫ H dB| ≥ ε) ≤ δ / ε² + ℙ(∫ |H|² ≥ δ)`. -/
theorem elementary_localisation (x : Rd d) {k : ℕ} {s : Fin (k + 1) → ℝ} (hs : Monotone s)
    (hs0 : s 0 = 0) (hsT : s (Fin.last k) ≤ T)
    {ξ : Fin k → CanonicalWienerSpace d T → Rd d}
    (hξ : ∀ j, Measurable[IsItoIntegral.naturalSigma d T (s j.castSucc)] (ξ j))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    CanonicalWienerSpace.P (T := T) x {ω | ε ≤ |IsItoIntegral.elementaryIntegral s ξ ω|} ≤
      ENNReal.ofReal (δ / ε ^ 2) + CanonicalWienerSpace.P (T := T) x
        {ω | δ ≤ ∫ u in (0 : ℝ)..s (Fin.last k), ‖IsItoIntegral.elementaryValue s ξ u ω‖ ^ 2} := by
  sorry

end proposition_5_3

end WeakPathwiseIto
