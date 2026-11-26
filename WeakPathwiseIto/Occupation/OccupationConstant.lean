/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Basic.Rd

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

/-- The normalising constant `c_d := 2 / |B(0,1)|` of eq. (7). -/
def occupationConstant (d : ℕ) : ℝ := 2 / (volume (Metric.ball (0 : Rd d) 1)).toReal

namespace occupationConstant

/-- **Subgoal** (Eq. (7) c_d, step 1: ball scaling): `|B(0,1/2)| = 2^{-d} |B(0,1)|`. -/
theorem volume_ball_half {d : ℕ} (hd : 0 < d) :
    (volume (Metric.ball (0 : Rd d) (1 / 2))).toReal =
      (1 / 2 : ℝ) ^ d * (volume (Metric.ball (0 : Rd d) 1)).toReal := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [Measure.addHaar_ball volume (0 : Rd d) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **Subgoal** (Eq. (7) c_d, step 2: reflection `x ↦ -x`): the two terms of eq. (7) have the
same integral over `B(0,1/2)`. -/
theorem integral_reflect {d : ℕ} (hd : 0 < d) :
    ∫ x in Metric.ball (0 : Rd d) (1 / 2), ‖x + (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) =
      ∫ x in Metric.ball (0 : Rd d) (1 / 2), ‖x - (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, step 3: local integrability): `x ↦ |x - y|^{2-d}` is integrable on
a ball. -/
theorem integrableOn_term {d : ℕ} (y : Rd d) (R : ℝ) :
    IntegrableOn (fun x : Rd d => ‖x - y‖ ^ (2 - (d : ℝ))) (Metric.ball 0 R) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d, step 4: Newton's theorem for a ball): for `|y| = R > 0`,
`∫_{B(0,R)} |x - y|^{2-d} dx = |B(0,R)| R^{2-d}` (mean value property of the Newton kernel). -/
theorem newton_ball {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) {y : Rd d} (hy : ‖y‖ = R) :
    ∫ x in Metric.ball (0 : Rd d) R, ‖x - y‖ ^ (2 - (d : ℝ)) =
      (volume (Metric.ball (0 : Rd d) R)).toReal * R ^ (2 - (d : ℝ)) := by
  sorry

/-- **Subgoal** (Eq. (7) c_d). Eq. (7): `c_d = [∫_{B(0,1/2)} (|x - e_1/2|^{2-d} + |x + e_1/2|^{2-d}) dx]⁻¹`. -/
theorem eq_inv_integral {d : ℕ} (hd : 0 < d) :
    occupationConstant d = (∫ x in Metric.ball (0 : Rd d) (1 / 2),
      (‖x - (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ)) +
        ‖x + (1 / 2 : ℝ) • Rd.basisVec ⟨0, hd⟩‖ ^ (2 - (d : ℝ))))⁻¹ := by
  sorry

end occupationConstant

end WeakPathwiseIto
