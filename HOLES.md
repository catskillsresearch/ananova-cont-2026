# Proof holes (Ananova–Cont 2026 / WeakPathwiseIto)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-26T20:20:25Z  
**`sorry` occurrences:** 51 · 15 open · 36 blocked · 130 done (goals + subgoals) · goals {'open': 6, 'blocked': 21, 'done': 38} · subgoals {'open': 9, 'blocked': 15, 'done': 92} · 24 file(s) with `sorry`.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, holes-edges.txt, holes.html
scripts/serve_holes.sh           # http://127.0.0.1:8770/holes.html
```

## Paper goals

| Status | Module | Paper | `sorry` | Holes |
|---|---|---|---|---|
| blocked | `Main.Theorem51` | Theorem 5.1 | 3 | `theorem_5_1_tendsto`, `theorem_5_1_unique`, `theorem_5_1` |
| blocked | `Main.Theorem52` | Theorem 5.2 | 2 | `theorem_5_2`, `theorem_5_2_deterministic` |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `proposition_5_3` |

## Open now

| Module | Paper | `sorry` | Holes |
|---|---|---|---|
| `Main.Remark54` | Remark 5.4 | 3 | `remark_5_4_dim_one`, `remark_5_4_not_implied`, `remark_5_4_sufficient` |
| `Smooth.Corollary32` | Corollary 3.2 | 1 | `corollary_3_2` |
| `Smooth.Proposition31` | Proposition 3.1 | 1 | `proposition_3_1` |
| `Sobolev.Lemma22` | Lemma 2.2 | 1 | `lemma_2_2` |
| `Sobolev.Theorem21` | Theorem 2.1 | 2 | `theorem_2_1_first`, `theorem_2_1_second` |
| `Sobolev.Theorem23` | Theorem 2.3 | 2 | `theorem_2_3_first`, `theorem_2_3_second` |

## Subgoals (helper lemmas/defs)

Each helper a goal depends on is its own board node `Module::Name`. Label it by opening its docstring with `**Subgoal** (<paper item>)`.

| Status | Subgoal | Label | `sorry` |
|---|---|---|---|
| done | `Appendix.HeatKernel::heatKernel.div_scaling` | subgoal of Lemma B.2 proof, eq. (34 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integrableOn_Ioc` | subgoal of Lemma B.2 proof, eq. (35 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integrableOn_unitKernel` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integrableOn_unitProfile` | subgoal of Lemma B.2 proof, eq. (34 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integral_div_le` | subgoal of Lemma B.2 proof, eqs. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integral_le_potentialProfile` | subgoal of Lemma B.2 proof, eqs. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integral_le_potentialProfile_of_two_lt` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integral_le_potentialProfile_one` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.integral_le_potentialProfile_two` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.le_inv_two_mul_add` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.le_rpow_mul` | subgoal of Lemma B.2 proof, eq. (35 | 0 |
| done | `Appendix.HeatKernel::heatKernel.riemannSum_le_integral` | subgoal of Lemma B.2 proof, eq. (35 | 0 |
| done | `Appendix.HeatKernel::heatKernel.riemannSum_le_potentialProfile` | subgoal of Lemma B.2 proof, eqs. (32 | 0 |
| done | `Appendix.HeatKernel::heatKernel.scaling` | subgoal of Lemma B.2 proof, eq. (32 | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.B_ofCoords` | subgoal of Lemma A.1 proof, step 2a: coordinates of `B` | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.covariance_coordIncrements_eq_zero` | subgoal of Lemma A.1 proof, step 2d-ii: uncorrelated | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.hasGaussianLaw_coordIncrements` | subgoal of Lemma A.1 proof, step 2d-i: jointly Gaussian | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.hasLaw_increment` | subgoal of Lemma A.1 proof, step 2c: `Z_i^n ∼ N(0, I_d | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.hasLaw_sum_smul_basisVec` | subgoal of Lemma A.1 proof, step 2b: from coordinates to `N(0, I_d | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.iIndepFun_increments` | subgoal of Lemma A.1 proof, step 2d: the `Z_i^n` are independent | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.iIndepFun_map_of_comp` | subgoal of Lemma A.1 proof, step 2d-iii: transport to `ℙ_x = Q ∘ g⁻¹` | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.integral_eq` | subgoal of Lemma A.1 proof, step 3: mean | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.integral_rpow_eq_sum` | subgoal of Lemma A.1 proof, step 1: `‖ρ_{n,B}‖^q_{L^q} = ∑_i |Z_i^n|^{2q} Δ_i^n` | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.integral_rpow_eq_sum_norm` | subgoal of Lemma A.1 proof, step 1 in terms of `Z_i^n` | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.memLp_norm_rpow_stdGaussian` | subgoal of Lemma A.1 proof, step 3: Gaussian moments are finite | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.memLp_two` | subgoal of Lemma A.1 proof, step 3: square integrability | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.tendsto_ae_of_summable_variance` | subgoal of Lemma A.1 proof, step 4: Chebyshev + Borel–Cantelli | 0 |
| done | `Appendix.LemmaA1::lemma_A_1.variance_le` | subgoal of Lemma A.1 proof, step 3: variance | 0 |
| blocked | `Appendix.LemmaB2::lemma_B_2_literal` | subgoal of Lemma B.2, literal reading | 0 |
| done | `Basic.FunctionOscillation::functionOscillation.tendsto_zero` | subgoal of Theorem 5.1 proof, Section 4 osc(φ,δ | 0 |
| done | `Basic.Partition::Partition.gap_le_mesh` | subgoal of Assumption 1 mesh | 0 |
| done | `Basic.Partition::Partition.left_lt_right` | subgoal of Section 3 partitions | 0 |
| done | `Basic.Partition::Partition.mesh_nonneg` | subgoal of Assumption 1 mesh | 0 |
| done | `Basic.Partition::Partition.nonneg` | subgoal of Section 3 partitions | 0 |
| done | `Basic.Partition::Partition.right_le_mul_left` | subgoal of Lemma B.2 proof, eq. (35 | 0 |
| done | `Basic.Partition::Partition.sum_gap` | subgoal of Lemma A.1 proof, step 3: `∑_i Δ_i^n = T` | 0 |
| done | `Basic.Partition::Partition.t_mem` | subgoal of Section 3 partitions | 0 |
| blocked | `Bessel.BesselCapacity::besselCapacity.IsNull.iUnion` | subgoal of Definition 2.7, countable unions | 1 |
| blocked | `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_one` | subgoal of Lemma B.1 proof, [AM71] | 1 |
| blocked | `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_p` | subgoal of Appendix C proof of Theorem 5.2, [AM71] | 1 |
| blocked | `Bessel.BesselCapacity::besselCapacity.iUnion_le` | subgoal of Definition 2.7, countable subadditivity [Fuk93] | 1 |
| done | `Bessel.BesselKernel::besselKernel.asymptotic_origin` | subgoal of Definition 2.4 | 0 |
| done | `Bessel.BesselKernel::besselKernel.fourier_eq` | subgoal of Definition 2.4 | 0 |
| done | `Bessel.BesselKernel::besselKernel.fourier_fubini` | subgoal of Definition 2.4, Fourier transform step 2: Fubini | 0 |
| done | `Bessel.BesselKernel::besselKernel.fourier_slice` | subgoal of Definition 2.4, Fourier transform step 1: Gaussian Fourier transform | 0 |
| done | `Bessel.BesselKernel::besselKernel.integrable` | subgoal of Definition 2.4 | 0 |
| done | `Bessel.BesselKernel::besselKernel.integrableOn_profile` | subgoal of Definition 2.4, integrability step 2: Gamma-type profile | 0 |
| done | `Bessel.BesselKernel::besselKernel.integrable_uncurry` | subgoal of Definition 2.4, integrability step 3: Tonelli | 0 |
| done | `Bessel.BesselKernel::besselKernel.integral_comp_div` | subgoal of Definition 2.4, behaviour at the origin, step 1: substitution `δ = a/u` | 0 |
| done | `Bessel.BesselKernel::besselKernel.integral_exp_slice` | subgoal of Definition 2.4, integrability step 1: Gaussian slice | 0 |
| done | `Bessel.BesselKernel::besselKernel.integral_profile_exp` | subgoal of Definition 2.4, Fourier transform step 3: Gamma integral | 0 |
| done | `Bessel.BesselKernel::besselKernel.mul_eq_integral` | subgoal of Definition 2.4, behaviour at the origin, step 2: rescaled kernel | 0 |
| done | `Bessel.BesselKernel::besselKernel.nonneg` | subgoal of Definition 2.4 | 0 |
| done | `Bessel.BesselKernel::besselKernel.tendsto_integral` | subgoal of Definition 2.4, behaviour at the origin, step 3: dominated convergence | 0 |
| open | `Bessel.BesselSpace::BesselSpace.eLpNorm_potential_le` | subgoal of Definition 2.5, Young's inequality | 1 |
| blocked | `Bessel.IsBrownianPolar::IsBrownianPolar.iUnion` | subgoal of Definition 2.8, countable unions | 1 |
| blocked | `Bessel.IsBrownianPolar::IsBrownianPolar.iff_isNull` | subgoal of Definition 2.8, [Fuk93, p. 25] | 1 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval` | subgoal of Section 2.2 Wiener space, measurability of `ω' ↦ x + W(ω' | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.exists_isLaw` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.ext_of_map_coe` | subgoal of Section 2.2 Wiener space, uniqueness step 2 | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isLaw_P` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isLaw_unique` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isProbabilityMeasure_P` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.map_coords_restrict` | subgoal of Section 2.2 Wiener space, uniqueness step 3: finite-dimensional distributions of `d` independent Brownian motions | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.map_restrict_eq` | subgoal of Section 2.2 Wiener space, uniqueness step 4: f.d.d. of `ℙ` | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.measurableSpace_eq_comap_coe` | subgoal of Section 2.2 Wiener space, uniqueness step 1: Borel = cylinder σ-algebra | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.mesh_succ` | subgoal of Assumption 2, eqs. (30 | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.sum_inv_mesh_le` | subgoal of Assumption 2, eq. (31 | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.summable_mesh` | subgoal of Assumption 2, eq. (30 | 0 |
| blocked | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integrable_piece` | subgoal of Eq. (7 | 1 |
| blocked | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_eq` | subgoal of Eq. (7 | 1 |
| blocked | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_piece` | subgoal of Eq. (7 | 1 |
| blocked | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.piece_nonneg` | subgoal of Eq. (7 | 1 |
| done | `Occupation.NormalizedQuadraticDensity::normalizedQuadraticDensity.memLp` | subgoal of Lemma A.1, finiteness of `‖ρ_n‖_{L^q}` | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.clm_integral_sphere` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.contDiffOn_norm_rpow` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.continuousOn_fderiv_fderiv_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.continuousOn_integral_sphere` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.eq_inv_integral` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.fderiv_fderiv_norm_rpow_apply` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.fderiv_fderiv_norm_sub_rpow_apply` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.harmonicAt_sphereMean` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_fderiv_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_integral_sphere` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_norm_rpow_of_ne` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integrableOn_term` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_ball_polar` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_reflect` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_toSphere_isometry` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.laplacian_newtonKernel` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.newton_ball` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball_dim_one` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball_dim_two` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.newton_ball_of_three_le` | subgoal of Eq. (7 | 1 |
| open | `Occupation.OccupationConstant::occupationConstant.radial_harmonic_eq` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_eq_integral` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.sphereMean_outside` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_radial` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sum_fderiv_fderiv_newtonKernel_sub` | subgoal of Eq. (7 | 0 |
| open | `Occupation.OccupationConstant::occupationConstant.tendsto_sphereMean` | subgoal of Eq. (7 | 1 |
| done | `Occupation.OccupationConstant::occupationConstant.volume_ball_half` | subgoal of Eq. (7 | 0 |
| blocked | `Occupation.OccupationSeminorm::occupationSeminorm.add_le` | subgoal of Section 4.2 seminorm | 1 |
| blocked | `Occupation.OccupationSeminorm::occupationSeminorm.le_limsup_discreteSeminorm` | subgoal of Eq. (11 | 1 |
| blocked | `Occupation.OccupationSeminorm::occupationSeminorm.lintegral_le_maximal` | subgoal of Eq. (10 | 1 |
| blocked | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.contDiffBounded_subset` | subgoal of Definition 4.3 | 1 |
| done | `Occupation.WeightedOccupationMeasure::weightedOccupationMeasure.integral_eq` | subgoal of Lemma 4.2 | 0 |
| open | `Smooth.FollmerItoFormula::follmer_ito_formula` | subgoal of Corollary 3.2 proof, [Föl81] | 1 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.tendsto_cross` | subgoal of Section 3 Q^π(ℝ^d | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.traceExt` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.traceExt_monotone` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.trace_monotoneOn` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasScalarQuadraticVariation::HasScalarQuadraticVariation.qvExt` | subgoal of Eq. (5 | 0 |
| done | `Smooth.HasScalarQuadraticVariation::HasScalarQuadraticVariation.qvExt_monotone` | subgoal of Eq. (5 | 0 |
| done | `Smooth.PathOscillation::pathOscillation.vanishes_of_mesh` | subgoal of Eq. (6 | 0 |

## All modules by section

### Preliminaries

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Basic.ContDiffBounded` | C^k_b | 0 |  |
| done | `Basic.FunctionOscillation` | Section 4 osc(φ,δ) | 0 |  |
| done | `Basic.IsCubeOrBall` | Section 2.1 cube or ball Q | 0 |  |
| done | `Basic.Partition` | Section 3 (partitions) | 0 |  |
| done | `Basic.Rd` |  | 0 |  |
| done | `Basic.SmoothHessian` |  | 0 |  |
| done | `Basic.WeakLpTendsto` | Remarks 4.4/4.5 weak L^r convergence | 0 |  |

### §2.1 Sobolev spaces

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Sobolev.IsLebesguePoint` |  | 0 |  |
| done | `Sobolev.IsWeakDerivative` | Section 2.1 weak derivative | 0 |  |
| done | `Sobolev.IsWeakGradient` |  | 0 |  |
| done | `Sobolev.IsWeakHessian` |  | 0 |  |
| open | `Sobolev.Lemma22` | Lemma 2.2 | 1 |  |
| done | `Sobolev.LocalMaximalFunction` | Section 2.1 M_R f | 0 |  |
| done | `Sobolev.MemW` | Section 2.1 W^{k,p} | 0 |  |
| done | `Sobolev.MemW2Plus` | Section 2.1 W^{2+,p} | 0 |  |
| done | `Sobolev.MemW2PlusS` | Section 5.2 W^{2+s,p} | 0 |  |
| done | `Sobolev.MemWLoc` | W^{1,2}_loc | 0 |  |
| done | `Sobolev.PreciseRepresentative` | Eq. (3) | 0 |  |
| open | `Sobolev.Theorem21` | Theorem 2.1 | 2 |  |
| open | `Sobolev.Theorem23` | Theorem 2.3 | 2 |  |

### §2.2 Bessel potentials, capacity, polar sets

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| blocked | `Bessel.BesselCapacity` | Definition 2.7 | 4 | `Bessel.BesselCapacity::besselCapacity.IsNull.iUnion`, `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_one`, `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_p`, `Bessel.BesselCapacity::besselCapacity.iUnion_le`, `Bessel.BesselSpace` |
| done | `Bessel.BesselKernel` | Definition 2.4 | 0 |  |
| blocked | `Bessel.BesselSpace` | Definition 2.5 | 1 | `Bessel.BesselSpace::BesselSpace.eLpNorm_potential_le` |
| done | `Bessel.CanonicalWienerSpace` | Section 2.2 Wiener space | 0 |  |
| blocked | `Bessel.IsBrownianPolar` | Definition 2.8 | 2 | `Bessel.BesselCapacity`, `Bessel.IsBrownianPolar::IsBrownianPolar.iUnion`, `Bessel.IsBrownianPolar::IsBrownianPolar.iff_isNull` |
| blocked | `Bessel.Theorem26` | Theorem 2.6 | 1 | `Bessel.BesselSpace` |
| blocked | `Bessel.Theorem29` | Theorem 2.9 | 1 | `Bessel.BesselCapacity` |
| done | `Bessel.WienerLawExists` | Section 2.2 ℙ_x exists (subgoals) | 0 |  |

### §3 Smooth change of variable

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| open | `Smooth.Corollary32` | Corollary 3.2 | 1 |  |
| done | `Smooth.DiscreteQuadraticVariation` | Eq. (5) sums | 0 |  |
| done | `Smooth.FollmerIntegral` | Corollary 3.2 integral | 0 |  |
| blocked | `Smooth.FollmerItoFormula` | [Föl81] Itô formula | 1 | `Smooth.FollmerItoFormula::follmer_ito_formula` |
| done | `Smooth.HasQuadraticVariation` | Section 3 Q^π(ℝ^d) | 0 |  |
| done | `Smooth.HasScalarQuadraticVariation` | Eq. (5) | 0 |  |
| done | `Smooth.PathOscillation` | Eq. (6) | 0 |  |
| done | `Smooth.PathwiseCovariation` | Proposition 3.1 covariation | 0 |  |
| open | `Smooth.Proposition31` | Proposition 3.1 | 1 |  |

### §4 Occupation measures and 𝓦²_{ω,π}

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| blocked | `Occupation.ApproximatingSequence` | Eq. (8) | 0 | `Occupation.OccupationSeminorm` |
| done | `Occupation.DiscreteLocalTime` | Remark 4.5 λ^{n,±}_T [DOS18] | 0 |  |
| blocked | `Occupation.DiscreteOccupationDensity` | Eq. (7) | 4 | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integrable_piece`, `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_eq`, `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_piece`, `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.piece_nonneg`, `Occupation.OccupationConstant` |
| done | `Occupation.DiscreteSeminorm` | Section 4.2 ‖h‖_{n,p,ω} | 0 |  |
| done | `Occupation.IncrementBall` | Eq. (7) Q^n_i | 0 |  |
| blocked | `Occupation.Lemma42` | Lemma 4.2 | 1 | `Occupation.DiscreteOccupationDensity` |
| done | `Occupation.NormalizedQuadraticDensity` | Eq. (28) | 0 |  |
| blocked | `Occupation.OccupationConstant` | Eq. (7) c_d | 7 | `Occupation.OccupationConstant::occupationConstant.eq_inv_integral`, `Occupation.OccupationConstant::occupationConstant.harmonicAt_sphereMean`, `Occupation.OccupationConstant::occupationConstant.newton_ball`, `Occupation.OccupationConstant::occupationConstant.newton_ball_of_three_le`, `Occupation.OccupationConstant::occupationConstant.radial_harmonic_eq`, `Occupation.OccupationConstant::occupationConstant.sphereMean_outside`, `Occupation.OccupationConstant::occupationConstant.tendsto_sphereMean` |
| blocked | `Occupation.OccupationSeminorm` | Section 4.2 seminorm, (10), (11) | 3 | `Occupation.DiscreteOccupationDensity`, `Occupation.OccupationSeminorm::occupationSeminorm.add_le`, `Occupation.OccupationSeminorm::occupationSeminorm.le_limsup_discreteSeminorm`, `Occupation.OccupationSeminorm::occupationSeminorm.lintegral_le_maximal` |
| blocked | `Occupation.PathwiseSobolevSpace` | Definition 4.3 | 1 | `Occupation.ApproximatingSequence`, `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.contDiffBounded_subset` |
| blocked | `Occupation.Remark44` | Remark 4.4 | 3 | `Occupation.PathwiseSobolevSpace` |
| blocked | `Occupation.Remark45` | Remark 4.5 | 4 | `Main.Theorem51`, `Occupation.Remark44` |
| done | `Occupation.WeightedOccupationMeasure` | Lemma 4.2 μ^T_ω | 0 |  |

### §5 Main results

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Main.BalancedPartitions` | Assumption 1 | 0 |  |
| done | `Main.GeometricMeshDecay` | Assumption 2, (30), (31) | 0 |  |
| done | `Main.IsItoIntegral` | Itô integral | 0 |  |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `Main.Theorem52`, `Main.WeakCovariation`, `Main.WeakPathwiseIntegral` |
| open | `Main.Remark54` | Remark 5.4 | 3 |  |
| blocked | `Main.Theorem51` | Theorem 5.1 | 3 | `Main.WeakCovariation`, `Main.WeakPathwiseIntegral` |
| blocked | `Main.Theorem52` | Theorem 5.2 | 2 | `Bessel.IsBrownianPolar`, `Occupation.PathwiseSobolevSpace` |
| blocked | `Main.WeakCovariation` | Eq. (15) | 0 | `Occupation.ApproximatingSequence` |
| blocked | `Main.WeakPathwiseIntegral` | Eq. (16) | 0 | `Occupation.ApproximatingSequence` |

### Appendices A–B

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Appendix.GaussianMoment` | Lemma A.1 c_{q,d} | 0 |  |
| done | `Appendix.HeatKernel` | Eqs. (32), (34), (35) | 0 |  |
| done | `Appendix.LemmaA1` | Lemma A.1 | 0 |  |
| blocked | `Appendix.LemmaB1` | Lemma B.1 | 1 | `Bessel.IsBrownianPolar` |
| blocked | `Appendix.LemmaB2` | Lemma B.2 | 1 | `Appendix.LemmaB2::lemma_B_2_literal`, `Bessel.IsBrownianPolar` |
| done | `Appendix.PotentialProfile` | Eq. (33) | 0 |  |

