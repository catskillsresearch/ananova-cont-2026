/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.BesselSpace
public import WeakPathwiseIto.Bessel.NonnegPotential

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The Bessel `(α, p)`-capacity (Definition 2.7):
`B_{α,p}(E) := inf {‖h‖_p^p : g_α ⋆ h ≥ 1_E, h ≥ 0}`, over measurable `h ≥ 0` (elements of
`L^p`), with `g_α ⋆ h ∈ [0, ∞]` the extended-real potential `BesselSpace.nonnegPotential`. -/
def besselCapacity (d : ℕ) (α : ℝ) (p : ℝ≥0∞) (S : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (h : Rd d → ℝ) (_ : Measurable h) (_ : 0 ≤ h)
    (_ : ∀ x ∈ S, 1 ≤ BesselSpace.nonnegPotential d α h x),
    eLpNorm h p volume ^ p.toReal

namespace besselCapacity

variable {d : ℕ}

/-- `S` is `(α, p)`-polar: `B_{α,p}(S) = 0` (Definition 2.7). -/
def IsNull (d : ℕ) (α : ℝ) (p : ℝ≥0∞) (S : Set (Rd d)) : Prop := besselCapacity d α p S = 0

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 1): for `α ≠ 0` the potential
`g_α ⋆ h ∈ [0, ∞]` is monotone under a.e. inequality of `h`. -/
theorem nonnegPotential_mono_ae {α : ℝ} (hα : α ≠ 0) {h₁ h₂ : Rd d → ℝ}
    (hle : ∀ᵐ y, ENNReal.ofReal (h₁ y) ≤ ENNReal.ofReal (h₂ y)) (x : Rd d) :
    BesselSpace.nonnegPotential d α h₁ x ≤ BesselSpace.nonnegPotential d α h₂ x := by
  simp only [BesselSpace.nonnegPotential, ite_eq_right hα]
  exact lintegral_mono_ae (hle.mono fun y hy => mul_le_mul_right hy _)

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 2): for `0 < p < ∞`,
`‖h‖_p^p = ∫ |h|^p`. -/
theorem eLpNorm_rpow_eq {p : ℝ≥0∞} (hp : 0 < p.toReal) {h : Rd d → ℝ} (hh : Measurable h) :
    eLpNorm h p volume ^ p.toReal = ∫⁻ y, ‖h y‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := fun h0 => by simp [h0] at hp
  have hpt : p ≠ ⊤ := fun ht => by simp [ht] at hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hh.aestronglyMeasurable, ← ENNReal.rpow_mul,
    one_div,
    inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 3): when `p.toReal = 0`
(`p ∈ {0, ∞}`), every admissible value `‖h‖_p^0` is `1`, so `B_{α,p}(E) ≥ 1`. -/
theorem one_le_of_toReal_eq_zero {α : ℝ} {p : ℝ≥0∞} (hp : p.toReal = 0) (S : Set (Rd d)) :
    1 ≤ besselCapacity d α p S := by
  simp only [besselCapacity, hp, ENNReal.rpow_zero]
  exact le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_rfl

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 4): `(sup_n a_n)^q ≤ ∑_n a_n^q`
for `q > 0`. -/
theorem iSup_rpow_le_tsum {q : ℝ} (hq : 0 < q) (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ^ q ≤ ∑' n, a n ^ q := by
  rw [ENNReal.iSup_rpow_of_pos hq]
  exact iSup_le fun n => ENNReal.le_tsum (f := fun n => a n ^ q) n

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 5): below any `c > B_{α,p}(E)`
there is an admissible `h`. -/
theorem exists_feasible_lt {α : ℝ} {p : ℝ≥0∞} {S : Set (Rd d)} {c : ℝ≥0∞}
    (hc : besselCapacity d α p S < c) :
    ∃ h : Rd d → ℝ, Measurable h ∧ 0 ≤ h ∧ (∀ x ∈ S, 1 ≤ BesselSpace.nonnegPotential d α h x) ∧
      eLpNorm h p volume ^ p.toReal < c := by
  simp only [besselCapacity, iInf_lt_iff] at hc
  obtain ⟨h, hm, h0, hS, hlt⟩ := hc
  exact ⟨h, hm, h0, hS, hlt⟩

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 6): the admissible function
`sup_n h_n`, taken as `1` on the (null) set where the supremum is `∞`. -/
noncomputable def supFn (h : ℕ → Rd d → ℝ) (y : Rd d) : ℝ :=
  if ⨆ n, ENNReal.ofReal (h n y) = ⊤ then 1 else (⨆ n, ENNReal.ofReal (h n y)).toReal

/-- **Subgoal** (Definition 2.7, countable subadditivity, step 6): `sup_n h_n` is measurable,
nonnegative, dominates each `h_n` where finite, and `|sup_n h_n|^q ≤ ∑_n h_n^q`. -/
theorem supFn_props {h : ℕ → Rd d → ℝ} (hm : ∀ n, Measurable (h n)) :
    Measurable (supFn h) ∧ 0 ≤ supFn h ∧
      (∀ n y, ⨆ k, ENNReal.ofReal (h k y) ≠ ⊤ →
        ENNReal.ofReal (h n y) ≤ ENNReal.ofReal (supFn h y)) ∧
      ∀ {q : ℝ}, 0 < q → ∀ y, ‖supFn h y‖ₑ ^ q ≤ ∑' n, ENNReal.ofReal (h n y) ^ q := by
  sorry

/-- **Subgoal** (Definition 2.7, countable subadditivity [Fuk93]). Countable subadditivity of the Bessel capacity [Fuk93]. -/
theorem iUnion_le (α : ℝ) (p : ℝ≥0∞) (S : ℕ → Set (Rd d)) :
    besselCapacity d α p (⋃ n, S n) ≤ ∑' n, besselCapacity d α p (S n) := by
  sorry

/-- **Subgoal** (Definition 2.7, countable unions). A countable union of `(α, p)`-polar sets is `(α, p)`-polar. -/
theorem IsNull.iUnion {α : ℝ} {p : ℝ≥0∞} {S : ℕ → Set (Rd d)} (h : ∀ n, IsNull d α (p) (S n)) :
    IsNull d α p (⋃ n, S n) := by
  refine le_antisymm ((iUnion_le α p S).trans ?_) zero_le
  simp only [IsNull] at h
  simp [h]

/-- **Subgoal** (Lemma B.1 proof, [AM71]). Inclusion of exceptional classes [AM71, Thm. 1], as used in Lemma B.1:
every `(2, 1)`-polar set is `(1, 2)`-polar. -/
theorem IsNull.one_two_of_two_one {S : Set (Rd d)} (h : IsNull d 2 1 S) : IsNull d 1 2 S := by
  sorry

/-- **Subgoal** (Appendix C proof of Theorem 5.2, [AM71]). Inclusion of exceptional classes [AM71, Thm. 1], as used in Appendix C:
for `p > 1`, every `(2, p)`-polar set is `(1, 2)`-polar. -/
theorem IsNull.one_two_of_two_p {p : ℝ} (hp : 1 < p) {S : Set (Rd d)}
    (h : IsNull d 2 (ENNReal.ofReal p) S) : IsNull d 1 2 S := by
  sorry

end besselCapacity

end WeakPathwiseIto
