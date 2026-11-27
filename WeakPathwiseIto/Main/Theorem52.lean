/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import Mathlib
public import WeakPathwiseIto.Bessel.IsBrownianPolar
public import WeakPathwiseIto.Sobolev.MemW2Plus
public import WeakPathwiseIto.Occupation.PathwiseSobolevSpace
public import WeakPathwiseIto.Main.BalancedPartitions
public import WeakPathwiseIto.Main.GeometricMeshDecay
public import WeakPathwiseIto.Main.Theorem52Steps
public import WeakPathwiseIto.Main.Theorem52PathSteps
public import WeakPathwiseIto.Appendix.LemmaA1
public import WeakPathwiseIto.Appendix.LemmaB2

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open WeakPathwiseIto.theorem_5_2
open scoped ENNReal NNReal RealInnerProductSpace

namespace WeakPathwiseIto

variable {T : ℝ} {d : ℕ}

/-- **Theorem 5.2** (equivalent form, as constructed in the paper's proof): there are a weak
Hessian `H` and a single deterministic sequence `F_m ∈ C^2_b ∩ W^{2,1}`, chosen before the
starting point, and a polar set `E` such that for every `x₀ ∉ E` the sequence `F_m` works
`ℙ_{x₀}`-almost surely. -/
theorem theorem_5_2_deterministic {π : ℕ → Partition T}
    (hT : 0 < T) (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {p : ℝ} (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2Plus p F) (hF1 : MemW 2 1 F)
    (hFrep : ∀ x, IsLebesguePoint F x → F x = preciseRepresentative F x) :
    ∃ H : Rd d → (Rd d →L[ℝ] Rd d), IsWeakHessian F H ∧ ∃ Fm : ℕ → Rd d → ℝ,
      (∀ m, 1 ≤ m → ContDiffBounded 2 (Fm m) ∧ MemW 2 1 (Fm m)) ∧
      ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
        ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀),
          (∀ t ∈ Icc 0 T, Tendsto (fun m => Fm m (CanonicalWienerSpace.path ω t)) atTop
            (𝓝 (F (CanonicalWienerSpace.path ω t)))) ∧
          Tendsto (fun m => occupationSeminorm π (CanonicalWienerSpace.path ω)
            (fun x => smoothHessian (Fm m) x - H x)) atTop (𝓝 0) := by
  -- step 1: mollifier, `F_n = ψ_n ⋆ F`, the Hessian errors `u_n`, and the index shift
  obtain ⟨s, hs, hFs⟩ := hF
  obtain ⟨H, hH⟩ := exists_isWeakHessian hF1
  obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs, hψb⟩ := exists_mollifier d
  set Fn : ℕ → Rd d → ℝ := fun n x => ∫ y, F y * ψ n (x - y) with hFn
  have hmem : ∀ n, ContDiffBounded 2 (Fn n) ∧ MemW 2 1 (Fn n) := fun n =>
    mollify_mem hF1 (hψ n) (hψc n)
  obtain ⟨hA, hG⟩ := tendsto_mollify_hessian hs.1 hp hFs hH hψ hψ0 hψ1 hψs
  obtain ⟨N, hN⟩ := exists_index_memLp_gagliardo hA hG
  set v : ℕ → Rd d → ℝ := fun m x => ‖smoothHessian (Fn (m + N)) x - H x‖ with hv
  have hvp : ∀ m, MemLp (v m) (ENNReal.ofReal p) := fun m => (hN (m + N) (by omega)).1
  have hvs : ∀ m, ∫⁻ x, ∫⁻ y, ‖v m x - v m y‖ₑ ^ p / edist x y ^ (s * p + d) < ⊤ := fun m =>
    (hN (m + N) (by omega)).2
  have hvint : ∀ m, Integrable (v m) := fun m =>
    integrable_norm_hessian_sub hF1 hH (hmem _).1 (hmem _).2
  have hvlim : Tendsto (fun m => eLpNorm (v m) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_add_atTop_iff_nat N).2 hA) (fun _ => zero_le) fun m => ?_
    exact eLpNorm_mono_enorm (hvp m).aestronglyMeasurable fun x => by simp only [v, enorm_norm]; exact le_rfl
  -- step 2: Lemma B.2 for `h_m = (M_1 u_m)^p`
  have hhyp := fun m => lemma_B_2_hyps_maximal hs.1 hp (hvp m) (hvs m)
  obtain ⟨E2, hE2, φ, hφ, -, hB2⟩ := lemma_B_2 hT h1 h2
    (h := fun m x => (localMaximalFunction 1 (v m) x).toReal ^ p)
    (fun m _ => (hhyp m).1) (fun m _ => (hhyp m).2.1) (fun m _ => (hhyp m).2.2.1)
    (tendsto_eLpNorm_maximal_rpow hp hvlim) (fun m _ => (hhyp m).2.2.2)
  -- step 3: the polar set
  obtain ⟨E1, hE1, hpot⟩ := exists_polar_forall_potential_lt_top T hvint
  refine ⟨H, hH, fun m => Fn (φ m + N), fun m _ => hmem _, ({x | ¬ IsLebesguePoint F x} ∪ E2) ∪ E1,
    isBrownianPolar_union (isBrownianPolar_union
    (isBrownianPolar_nonLebesgue hT hp ⟨s, hs, hFs⟩) hE2) hE1, fun x₀ hx₀ => ?_⟩
  have hx₂ : x₀ ∉ E2 := fun h => hx₀ (Or.inl (Or.inr h))
  have hx₁ : x₀ ∉ E1 := fun h => hx₀ (Or.inr h)
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hφN : StrictMono fun m => φ m + N := fun a b hab => Nat.add_lt_add_right (hφ hab) N
  have hFl : LocallyIntegrable F := (memLp_one_iff_integrable.1 hF1.1).locallyIntegrable
  have hnull := volume_iUnion_maximal_eq_top hp (u := fun k => v (φ k)) fun k => hvp _
  filter_upwards [ae_tendsto_mollify_path hT.le hFl hFrep hψ0 hψ1 hψs hψb
      (isBrownianPolar_union (isBrownianPolar_union
        (isBrownianPolar_nonLebesgue hT hp ⟨s, hs, hFs⟩) hE2) hE1)
      (fun x hx => Or.inl (Or.inl hx)) hx₀ hφN,
    hB2 x₀ hx₂, lemma_A_1_bounded (h2.summable_mesh hT) hpq.symm.lt x₀, ae_path_zero hT.le x₀,
    ae_forall_partition_not_mem hnull π x₀] with ω hconv hlim hρ h0 hfin
  -- step 4: path convergence; step 5: occupation seminorm
  refine ⟨hconv, ?_⟩
  have heq : ∀ m, occupationSeminorm π (CanonicalWienerSpace.path ω)
      (fun x => smoothHessian (Fn (φ m + N)) x - H x) =
      occupationSeminorm π (CanonicalWienerSpace.path ω) (v (φ m)) := fun m =>
    occupationSeminorm_norm _ _ _
  refine Tendsto.congr (fun m => (heq m).symm) ?_
  refine tendsto_occupationSeminorm_of_maximal hpq π _ (continuousOn_path ω)
    (vanishes_path hT h2 ω) hρ (u := fun k => v (φ k)) (fun k => (hvint _).locallyIntegrable)
    (fun k n j hj hc => hfin n j hj (mem_iUnion.2 ⟨k, hc⟩)) (fun k => ?_) hlim
  rw [h0]
  exact tendsto_lintegral_closedBall_kernel (hpot x₀ hx₁ (φ k)) (vanishes_path hT h2 ω)

/-- **Theorem 5.2.** Let `π` satisfy Assumptions 1 and 2 and
`F ∈ W^{2+,p}(ℝ^d) ∩ W^{2,1}(ℝ^d)`, `1 < p < ∞`, with `F` equal to its precise
representative `F̃` at every Lebesgue point (the paper's implicit convention; see
`WeakPathwiseIto.md`, "Theorem 5.2 and Proposition 5.3: representative of F"). Then there is a polar set `E` such that for
every starting point `x₀ ∉ E`, `ℙ_{x₀}(F ∈ 𝓦^2_{B,π}) = 1`. -/
theorem theorem_5_2 {π : ℕ → Partition T} (hT : 0 < T)
    (h1 : BalancedPartitions π) (h2 : GeometricMeshDecay π) {p : ℝ} (hp : 1 < p)
    {F : Rd d → ℝ} (hF : MemW2Plus p F) (hF1 : MemW 2 1 F)
    (hFrep : ∀ x, IsLebesguePoint F x → F x = preciseRepresentative F x) :
    ∃ E : Set (Rd d), IsBrownianPolar d T E ∧ ∀ x₀ ∉ E,
      ∀ᵐ ω ∂(CanonicalWienerSpace.P (T := T) x₀), F ∈ PathwiseSobolevSpace π (CanonicalWienerSpace.path ω) := by
  obtain ⟨H, hH, Fm, hFm, E, hE, hdet⟩ := theorem_5_2_deterministic hT h1 h2 hp hF hF1 hFrep
  refine ⟨E, hE, fun x₀ hx₀ => ?_⟩
  filter_upwards [hdet x₀ hx₀] with ω hω
  exact ⟨hF1, H, hH, ⟨⟨Fm, fun m hm => (hFm m hm).1, fun m hm => (hFm m hm).2, hω.1, hω.2⟩⟩⟩

end WeakPathwiseIto
