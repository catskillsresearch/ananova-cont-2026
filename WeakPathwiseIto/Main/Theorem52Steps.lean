/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Bessel.Theorem29
public import WeakPathwiseIto.Sobolev.MemW2Plus
public import WeakPathwiseIto.Sobolev.PreciseRepresentative
public import WeakPathwiseIto.Sobolev.IsLebesguePoint
public import WeakPathwiseIto.Sobolev.LocalMaximalFunction
public import WeakPathwiseIto.Basic.ContDiffBounded
public import WeakPathwiseIto.Basic.SmoothHessian
public import WeakPathwiseIto.Sobolev.Theorem21Second
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace

/-! # Steps of the proof of Theorem 5.2 (Appendix C)

Appendix C: mollify `F_m := η_m ⋆ F`; the non-Lebesgue points `E₁` of `F` are polar
(Theorem 2.9, [AM71], [Fuk93]); `u_m := ‖∇²F_m - ∇²F‖ → 0` in `L^p` and `W^{s,p}`; the truncated
maximal operator `M_1` is bounded on `L^p` and `W^{s,p}`; `h_m := (M_1 u_m)^p` satisfies the
hypotheses of Lemma B.2; Brownian motion avoids Lebesgue-null sets at the (countably many)
positive partition times; the first partition interval is treated with Lemma B.1; then (10),
Hölder and Lemma A.1 give `‖u_m‖_{W⁰_{B,π}} ≤ C limsup_n ‖h_m‖_{n,1,B}^{1/p}`. Only the first
steps are stubbed here; the path-side steps are stubbed after the plan is approved. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

namespace theorem_5_2

variable {d : ℕ} {T : ℝ}

/-- **Subgoal** (Appendix C, mollification: a `W^{1,1}` function has a weak gradient, assembled
from its first-order weak derivatives). -/
theorem exists_isWeakGradient {k : ℕ} (hk : 1 ≤ k) {F : Rd d → ℝ} (hF : MemW k 1 F) :
    ∃ G : Rd d → Rd d, IsWeakGradient F G := by
  sorry

/-- **Subgoal** (Appendix C, mollification: a `W^{2,1}` function has a weak Hessian, assembled
from its second-order weak derivatives). -/
theorem exists_isWeakHessian {F : Rd d → ℝ} (hF : MemW 2 1 F) :
    ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `|h * ψ| ≤ ‖h‖_1 ‖ψ‖_∞`). -/
theorem abs_convolution_le {h ψ : Rd d → ℝ} (hh : Integrable h) {C : ℝ}
    (hC : ∀ x, |ψ x| ≤ C) (x : Rd d) :
    |∫ y, h y * ψ (x - y)| ≤ (∫ y, |h y|) * C := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `F * ψ ∈ C²_b` for `F ∈ W^{2,1}`: its derivatives of
order `≤ 2` are `F * ψ`, `∇F * ψ`, `∇²F * ψ`, bounded by `‖·‖_1 ‖ψ‖_∞`). -/
theorem contDiffBounded_convolution {F : Rd d → ℝ} (hF : MemW 2 1 F) {G : Rd d → Rd d}
    (hG : IsWeakGradient F G) {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiffBounded 2 (fun x => ∫ y, F y * ψ (x - y)) := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `D^0 f = f` weakly). -/
theorem isWeakDerivative_zero {f : Rd d → ℝ} (hf : LocallyIntegrable f) :
    IsWeakDerivative 0 f f := by
  sorry

/-- **Subgoal** (Appendix C, mollification: the classical partial derivative of a `C¹` function
is its weak derivative, by integration by parts). -/
theorem isWeakDerivative_single_of_contDiff {f : Rd d → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin d) :
    IsWeakDerivative (Pi.single i 1) f (fun x => fderiv ℝ f x (Rd.basisVec i)) := by
  sorry

/-- **Subgoal** (Appendix C, mollification: the multi-indices of order `≤ 2` are `0`, `e_i` and
`e_i + e_j`). -/
theorem order_le_two_cases {α : Fin d → ℕ} (hα : IsWeakDerivative.order α ≤ 2) :
    α = 0 ∨ (∃ i, α = Pi.single i 1) ∨ ∃ i j, α = Pi.single i 1 + Pi.single j 1 := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `F * ψ ∈ W^{2,1}` for `F ∈ W^{2,1}`: Young's inequality
for `F * ψ`, `∇F * ψ`, `∇²F * ψ`, which are its classical, hence weak, derivatives). -/
theorem memW_convolution {F : Rd d → ℝ} (hF : MemW 2 1 F) {G : Rd d → Rd d}
    (hG : IsWeakGradient F G) {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H)
    {ψ : Rd d → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    MemW 2 1 (fun x => ∫ y, F y * ψ (x - y)) := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `F_m ∈ C²_b ∩ W^{2,1}`). -/
theorem mollify_mem {F : Rd d → ℝ} (hF : MemW 2 1 F) {ψ : Rd d → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ContDiffBounded 2 (fun x => ∫ y, F y * ψ (x - y)) ∧
      MemW 2 1 (fun x => ∫ y, F y * ψ (x - y)) := by
  sorry

/-- **Subgoal** (Appendix C, mollification: `F_m(x) → F̃(x)` at every Lebesgue point). -/
theorem tendsto_mollify_of_isLebesguePoint {F : Rd d → ℝ} (hF : LocallyIntegrable F)
    {ψ : ℕ → Rd d → ℝ} (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)))
    (hψb : ∃ C : ℝ, ∀ n x, ψ n x ≤ C * ((n : ℝ) + 1) ^ d) {x : Rd d}
    (hx : IsLebesguePoint F x) :
    Tendsto (fun n => ∫ y, F y * ψ n (x - y)) atTop (𝓝 (preciseRepresentative F x)) := by
  sorry

/-- **Subgoal** (Appendix C, `E₁` is polar: Theorem 2.9, [AM71, Thm. 1], [Fuk93]). -/
theorem isBrownianPolar_nonLebesgue (hT : 0 < T) {p : ℝ} (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2Plus p F) : IsBrownianPolar d T {x | ¬ IsLebesguePoint F x} := by
  sorry

/-- **Subgoal** (Appendix C, Brownian motion does not enter a polar set at positive times). -/
theorem ae_forall_path_not_mem {E : Set (Rd d)} (hE : IsBrownianPolar d T E) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ Ioc 0 T,
      CanonicalWienerSpace.path ω t ∉ E := by
  sorry

/-- **Subgoal** (Appendix C, mollification converges in `W^{2+s,p}`: `u_m → 0` in `L^p` and in
the Gagliardo seminorm `[·]_{W^{s,p}}`). -/
theorem tendsto_mollify_hessian {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {F : Rd d → ℝ}
    (hF : MemW2PlusS s p F) {H : Rd d → (Rd d →L[ℝ] Rd d)} (hH : IsWeakHessian F H)
    {ψ : ℕ → Rd d → ℝ} (hψ : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n))
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n, ∫ x, ψ n x = 1)
    (hψs : ∀ n, Function.support (ψ n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => eLpNorm (fun x => smoothHessian (fun z => ∫ y, F y * ψ n (z - y)) x - H x)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x, ∫⁻ y,
        ‖‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) x - H x‖ -
          ‖smoothHessian (fun z => ∫ w, F w * ψ n (z - w)) y - H y‖‖ₑ ^ p /
            edist x y ^ (s * p + d)) atTop (𝓝 0) := by
  sorry

/-- **Subgoal** (Appendix C, Hardy–Littlewood: `M_1` is bounded on `L^p`, `p > 1`). -/
theorem eLpNorm_maximal_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    eLpNorm (localMaximalFunction 1 f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

/-- **Subgoal** (Appendix C, `M_1` is bounded on `W^{s,p}`: translation invariance and
sublinearity, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}`). -/
theorem gagliardo_maximal_le {s p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0, ∀ f : Rd d → ℝ,
    MemLp f (ENNReal.ofReal p) →
      ∫⁻ x, ∫⁻ y, ‖(localMaximalFunction 1 f x).toReal - (localMaximalFunction 1 f y).toReal‖ₑ ^ p /
          edist x y ^ (s * p + d) ≤
        C * ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ p / edist x y ^ (s * p + d) := by
  sorry

/-- **Subgoal** (Appendix C, second hypothesis of Lemma B.2 for `h = g^p`: Hölder on `K × K`). -/
theorem lintegral_rpow_sub_le {s p : ℝ} (hs : 0 < s) (hp : 1 < p) {g : Rd d → ℝ}
    (hg0 : 0 ≤ g) (hgm : Measurable g) (hgp : MemLp g (ENNReal.ofReal p))
    (hgs : ∫⁻ x, ∫⁻ y, ‖g x - g y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤)
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∫⁻ x in K, ∫⁻ y in K, ‖g x ^ p - g y ^ p‖ₑ / edist x y ^ (d : ℝ) < ⊤ := by
  sorry

/-- **Subgoal** (Appendix C, Brownian motion has a density at positive times: it a.s. avoids a
Lebesgue-null set at countably many positive times, e.g. the partition points `t^n_i > 0`). -/
theorem ae_forall_mem_not_mem_null {N : Set (Rd d)} (hN : volume N = 0) {S : Set ℝ}
    (hS : S.Countable) (hpos : ∀ t ∈ S, 0 < t ∧ t ≤ T) (x₀ : Rd d) :
    ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), ∀ t ∈ S, CanonicalWienerSpace.path ω t ∉ N := by
  sorry

end theorem_5_2

end WeakPathwiseIto
