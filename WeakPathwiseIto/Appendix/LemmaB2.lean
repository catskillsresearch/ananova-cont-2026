/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Occupation.DiscreteSeminorm
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Lemma B.2.** Let `π` satisfy Assumptions 1 and 2 and `(h_m)_{m ≥ 1} ⊂ L^1(ℝ^d)` be
nonnegative finite-valued Borel functions with `‖h_m‖_{L^1} → 0` and, for every compact `K`,
`∫_K ∫_K |h_m(x) - h_m(y)| / |x - y|^d dx dy < ∞`. Then there are a polar set `E` and a
subsequence `(h_{m_k})_{k ≥ 1}` with `lim_k limsup_n ‖h_{m_k}‖_{n,1,B} = 0`, `ℙ_{x₀}`-a.s. for
every `x₀ ∉ E`. Here `‖h‖_{n,1,B} = ∑_i (|h(B(t_i))| + |h(B(t_{i+1}))|)(t_{i+1} - t_i)` is the
`p = 1` case of the seminorm `‖h‖_{n,p,ω}` of Section 4.2; the paper prints an extra `∫_0^T`
in front of this sum, which we read as a typo — see `lemma_B_2_literal`, which shows the
literal reading follows (and for `T > 0` the two readings are equivalent). -/
theorem lemma_B_2 {T : ℝ} {d : ℕ} {π : ℕ → Partition T}
    (hT : 0 < T) (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {h : ℕ → Rd d → ℝ}
    (hmeas : ∀ m, 1 ≤ m → Measurable (h m)) (hnonneg : ∀ m, 1 ≤ m → 0 ≤ h m)
    (hint : ∀ m, 1 ≤ m → Integrable (h m))
    (hL1 : Tendsto (fun m => eLpNorm (h m) 1 volume) atTop (𝓝 0))
    (hreg : ∀ m, 1 ≤ m → ∀ K : Set (Rd d), IsCompact K →
      ∫⁻ x in K, ∫⁻ y in K, ‖h m x - h m y‖ₑ / edist x y ^ (d : ℝ) < ⊤) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, 1 ≤ φ k) ∧
      ∀ x₀ ∉ E, ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), Tendsto
        (fun k => limsup (fun n => discreteSeminorm (π n) 1 (fun x => ‖h (φ k) x‖ₑ)
          (CanonicalWienerSpace.path ω)) atTop) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Lemma B.2, literal reading): the conclusion of Lemma B.2 with `‖h‖_{n,1,B}`
read literally as printed, `∫_0^T ∑_i (|h(B(t_i))| + |h(B(t_{i+1}))|)(t_{i+1} - t_i) dt`
(an integral of a function constant in `t`, i.e. `T` times the Riemann sum). -/
theorem lemma_B_2_literal {T : ℝ} {d : ℕ} {π : ℕ → Partition T}
    (hT : 0 < T) (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {h : ℕ → Rd d → ℝ}
    (hmeas : ∀ m, 1 ≤ m → Measurable (h m)) (hnonneg : ∀ m, 1 ≤ m → 0 ≤ h m)
    (hint : ∀ m, 1 ≤ m → Integrable (h m))
    (hL1 : Tendsto (fun m => eLpNorm (h m) 1 volume) atTop (𝓝 0))
    (hreg : ∀ m, 1 ≤ m → ∀ K : Set (Rd d), IsCompact K →
      ∫⁻ x in K, ∫⁻ y in K, ‖h m x - h m y‖ₑ / edist x y ^ (d : ℝ) < ⊤) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, 1 ≤ φ k) ∧
      ∀ x₀ ∉ E, ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), Tendsto
        (fun k => limsup (fun n => ∫⁻ _ in Icc 0 T, discreteSeminorm (π n) 1
          (fun x => ‖h (φ k) x‖ₑ) (CanonicalWienerSpace.path ω)) atTop) atTop (𝓝 0) := by
  obtain ⟨E, hE, φ, hφ, hφ1, hlim⟩ := lemma_B_2 hT h1 h2 hmeas hnonneg hint hL1 hreg
  refine ⟨E, hE, φ, hφ, hφ1, fun x₀ hx₀ => ?_⟩
  filter_upwards [hlim x₀ hx₀] with ω hω
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  simp_rw [mul_comm _ (ENNReal.ofReal T)]
  simp_rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  simpa using ENNReal.Tendsto.const_mul hω (Or.inr ENNReal.ofReal_ne_top)

end WeakPathwiseIto
