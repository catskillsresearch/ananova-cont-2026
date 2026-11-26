/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Sobolev.MemWLoc
public import WeakPathwiseIto.Sobolev.MemW2Plus

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- **Remark 5.4** (dimension one). For `d = 1`, `F ∈ W^{1,2}_loc(ℝ)` iff `F` is (a.e. equal to)
a locally absolutely continuous function with `F' ∈ L^2_loc(ℝ)`. -/
theorem remark_5_4_dim_one (F : Rd 1 → ℝ) :
    MemWLoc 1 2 F ↔ ∃ G : ℝ → ℝ, (∀ᵐ v, F v = G (Rd.coord 0 v)) ∧
      (∀ a b, AbsolutelyContinuousOnInterval G a b) ∧
      ∀ a b, MemLp (deriv G) 2 (volume.restrict (Icc a b)) := by
  sorry

/-- **Remark 5.4** (no automatic implication). `F ∈ W^{2+,p}(ℝ^d) ∩ W^{2,1}(ℝ^d)` does not
imply `F ∈ W^{1,2}_loc(ℝ^d)` for every `p > 1` and every dimension `d`. -/
theorem remark_5_4_not_implied : ∃ (d : ℕ) (p : ℝ) (F : Rd d → ℝ),
    1 < p ∧ MemW2Plus p F ∧ MemW 2 1 F ∧ ¬ MemWLoc 1 2 F := by
  sorry

/-- **Remark 5.4** (sufficient Sobolev embedding condition). If `F ∈ W^{2+s,p}(ℝ^d)` for some
`s ∈ (0, 1)`, `p > 1`, with `1 + s > d (1/p - 1/2)`, then `F ∈ W^{1,2}_loc(ℝ^d)`. -/
theorem remark_5_4_sufficient {d : ℕ} {s p : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2PlusS s p F) (hcond : (d : ℝ) * (1 / p - 1 / 2) < 1 + s) :
    MemWLoc 1 2 F := by
  sorry

/-- **Remark 5.4** (`p ≥ 2`). For `p ≥ 2`, `F ∈ W^{2+,p}(ℝ^d)` implies `F ∈ W^{1,2}_loc(ℝ^d)`. -/
theorem remark_5_4_two_le {d : ℕ} {p : ℝ} (hp : 2 ≤ p) {F : Rd d → ℝ} (hF : MemW2Plus p F) :
    MemWLoc 1 2 F := by
  obtain ⟨s, hs, hS⟩ := hF
  refine remark_5_4_sufficient hs (by linarith) hS ?_
  have h1 : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
  have h2 : (d : ℝ) * (1 / p - 1 / 2) ≤ (d : ℝ) * 0 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
  linarith [hs.1]

end WeakPathwiseIto
