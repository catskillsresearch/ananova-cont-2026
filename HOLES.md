# Proof holes (Ananova–Cont 2026 / WeakPathwiseIto)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-27T02:47:58Z  
**`sorry` occurrences:** 27 · 5 open · 18 blocked · 264 done (goals + subgoals) · goals {'open': 4, 'blocked': 11, 'done': 54} · subgoals {'open': 1, 'blocked': 7, 'done': 210} · 14 file(s) with `sorry`.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, holes-edges.txt, holes.html
scripts/serve_holes.sh           # http://127.0.0.1:8770/holes.html
```

## Paper goals

| Status | Module | Paper | `sorry` | Holes |
|---|---|---|---|---|
| done | `Main.Theorem51` | Theorem 5.1 | 0 |  |
| blocked | `Main.Theorem52` | Theorem 5.2 | 2 | `theorem_5_2`, `theorem_5_2_deterministic` |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `proposition_5_3` |

## Open now

| Module | Paper | `sorry` | Holes |
|---|---|---|---|
| `Main.Remark54` | Remark 5.4 | 3 | `remark_5_4_dim_one`, `remark_5_4_not_implied`, `remark_5_4_sufficient` |
| `Occupation.Remark44` | Remark 4.4 | 3 | `remark_4_4_density`, `remark_4_4_seminorm`, `remark_4_4` |
| `Sobolev.Theorem21First` |  | 0 | (review → VERIFIED) |
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
| done | `Main.Eq18::theorem_5_1.eq_18` | subgoal of Theorem 5.1 proof, eq. (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.abs_inner_increment_le` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.abs_inner_increment_le_lintegral` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.abs_riemannSum_le` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.eventually_hessian_close` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.eventually_sum_abs_le` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.Eq18::theorem_5_1.eq_18.le_lintegral_piece` | subgoal of Theorem 5.1 proof, (18 | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.mesh_succ` | subgoal of Assumption 2, eqs. (30 | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.sum_inv_mesh_le` | subgoal of Assumption 2, eq. (31 | 0 |
| done | `Main.GeometricMeshDecay::GeometricMeshDecay.summable_mesh` | subgoal of Assumption 2, eq. (30 | 0 |
| done | `Main.SmoothItoAt::theorem_5_1.ito_at` | subgoal of Theorem 5.1 proof, eq. (21 | 0 |
| done | `Main.SmoothItoAt::theorem_5_1.ito_at.abs_trapezoid_le` | subgoal of Theorem 5.1 proof, (21 | 0 |
| done | `Main.SmoothItoAt::theorem_5_1.ito_at.stopped_sum_eq` | subgoal of Theorem 5.1 proof, (21 | 0 |
| done | `Main.SmoothItoAt::theorem_5_1.ito_at.sub_eq_sum_stopped` | subgoal of Theorem 5.1 proof, (21 | 0 |
| done | `Main.SmoothItoAt::theorem_5_1.ito_at.tendsto_trapezoid` | subgoal of Theorem 5.1 proof, (21 | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.abs_covariation_sub_le` | subgoal of Theorem 5.1 proof, eqs. (19 | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.contDiffBounded_sub` | subgoal of Theorem 5.1 proof: `C²_b` is closed under differences, used for `F_m - F_k` | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.gradient_smoothHessian_sub` | subgoal of Theorem 5.1 proof: linearity of `∇` and `∇²` on `C²` | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.isWeakDerivative_ae_unique` | subgoal of Theorem 5.1 proof, uniqueness: weak derivatives are unique a.e., by the fundamental lemma of the calculus of variations | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.isWeakHessian_ae` | subgoal of Theorem 5.1 proof, uniqueness: weak Hessians are unique a.e. and a.e.-strongly measurable | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.pathwiseCovariation_sub` | subgoal of Theorem 5.1 proof: linearity of the covariation on `C²_b` | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.tendsto_covariation` | subgoal of Theorem 5.1 proof, (20 | 0 |
| done | `Main.Theorem51Steps::theorem_5_1.tendsto_integral` | subgoal of Theorem 5.1 proof, (22 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.exists_isometry_basisVec` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integrable_piece` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_closedBall_affine` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_eq` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.integral_piece` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.piece_nonneg` | subgoal of Eq. (7 | 0 |
| done | `Occupation.DiscreteOccupationDensity::discreteOccupationDensity.setIntegral_closedBall_eq_ball` | subgoal of Eq. (7 | 0 |
| done | `Occupation.Lemma42::lemma_4_2.abs_integral_sub_grid_le` | subgoal of Lemma 4.2 proof, `tendsto_riemannStieltjes` grid step b: the Stieltjes integral | 0 |
| done | `Occupation.Lemma42::lemma_4_2.abs_integral_sub_le` | subgoal of Lemma 4.2 proof, first display | 0 |
| done | `Occupation.Lemma42::lemma_4_2.abs_sum_sub_grid_le` | subgoal of Lemma 4.2 proof, `tendsto_riemannStieltjes` grid step a: discrete sums | 0 |
| done | `Occupation.Lemma42::lemma_4_2.norm_increment_le` | subgoal of Lemma 4.2 proof: increments are bounded by the oscillation | 0 |
| done | `Occupation.Lemma42::lemma_4_2.tendsto_discreteTrace` | subgoal of Lemma 4.2 proof: discrete trace | 0 |
| done | `Occupation.Lemma42::lemma_4_2.tendsto_riemannStieltjes` | subgoal of Lemma 4.2 proof: Riemann–Stieltjes convergence | 0 |
| done | `Occupation.Lemma42::lemma_4_2.tendsto_sum_left` | subgoal of Lemma 4.2 proof, last display | 0 |
| done | `Occupation.Lemma42::lemma_4_2.tendsto_sum_sq` | subgoal of Lemma 4.2 proof: total discrete quadratic variation | 0 |
| done | `Occupation.Lemma42::lemma_4_2.traceMeasure_Ioc` | subgoal of Lemma 4.2 proof: Stieltjes measure of an interval | 0 |
| done | `Occupation.NormalizedQuadraticDensity::normalizedQuadraticDensity.memLp` | subgoal of Lemma A.1, finiteness of `‖ρ_n‖_{L^q}` | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.clm_integral_sphere` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.contDiffOn_norm_rpow` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.continuousOn_fderiv_fderiv_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.continuousOn_integral_sphere` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.eq_inv_integral` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.fderiv_fderiv_comp_norm_apply` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.fderiv_fderiv_norm_rpow_apply` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.fderiv_fderiv_norm_sub_rpow_apply` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.harmonicAt_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_comp_norm` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_fderiv_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_integral_sphere` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_norm_rpow_of_ne` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.hasFDerivAt_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integrableOn_term` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_Ioo_pow_mul` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_ball_polar` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_reflect` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_sphere_eq_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.integral_toSphere_isometry` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.laplacian_comp_norm` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.laplacian_newtonKernel` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball_dim_one` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball_dim_two` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.newton_ball_of_three_le` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.radial_eq_profile` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.radial_harmonic_eq` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.radial_ode_eq` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_bounds` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_eq_integral` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_outside` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sphereMean_radial` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.sum_fderiv_fderiv_newtonKernel_sub` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.tendsto_sphereMean` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.toSphere_real_univ` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.volume_ball_eq` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationConstant::occupationConstant.volume_ball_half` | subgoal of Eq. (7 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.add_le` | subgoal of Section 4.2 seminorm | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.lintegral_closedBall_le` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.lintegral_kernel_le_of_le_two` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.lintegral_kernel_le_of_three_le` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.lintegral_piece_le` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.lintegral_shell_le` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.norm_increment_le` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_10.volume_ball_eq` | subgoal of Eq. (10 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_11.sum_le_holder` | subgoal of Eq. (11 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_11.sum_rpow_le` | subgoal of Eq. (11 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.eq_11.sum_rpow_le_eLpNorm` | subgoal of Eq. (11 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.le_limsup_discreteSeminorm` | subgoal of Eq. (11 | 0 |
| done | `Occupation.OccupationSeminorm::occupationSeminorm.lintegral_le_maximal` | subgoal of Eq. (10 | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.contDiffBounded_subset` | subgoal of Definition 4.3 | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.coord_smoothHessian` | subgoal of Definition 4.3 proof, `C²` functions have a weak Hessian: Hessian entries | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.directions_single_add_single` | subgoal of Definition 4.3 proof, `C²` functions have a weak Hessian: the multi-index `e_i + e_j` | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.integral_mul_fderiv_fderiv` | subgoal of Definition 4.3 proof, `C²` functions have a weak Hessian: integration by parts twice | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.isWeakHessian_smoothHessian` | subgoal of Definition 4.3 proof | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.occupationSeminorm_sub_self` | subgoal of Definition 4.3 proof, the constant approximating sequence `F_m = F` | 0 |
| done | `Occupation.PathwiseSobolevSpace::PathwiseSobolevSpace.testDeriv_single_add_single` | subgoal of Definition 4.3 proof, `C²` functions have a weak Hessian: the test derivative | 0 |
| done | `Occupation.WeightedOccupationMeasure::weightedOccupationMeasure.integral_eq` | subgoal of Lemma 4.2 | 0 |
| done | `Smooth.Corollary32::corollary_3_2.pathwiseCovariation_eq` | subgoal of Corollary 3.2 proof, "by Proposition 3.1" | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula` | subgoal of Corollary 3.2 proof, [Föl81] | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.abs_taylor2_le` | subgoal of [Föl81] proof: second-order Taylor remainder | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.contDiffBounded_gradient` | subgoal of [Föl81] proof: `∇f ∈ C^1_b` for `f ∈ C^2_b` | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.hessian_symm` | subgoal of [Föl81] proof: the Hessian of a `C²` function is symmetric | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.riemannSum_eq` | subgoal of [Föl81] proof: at `t = T` the stopped left Riemann sum is the plain one | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.sub_eq_sum` | subgoal of [Föl81] proof: telescoping `f(ω(T | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.tendsto_hessian_left` | subgoal of [Föl81] proof: `∑_k ⟨∇²f(ω(t_k | 0 |
| done | `Smooth.FollmerItoFormula::follmer_ito_formula.tendsto_remainder` | subgoal of [Föl81] proof: the second-order Taylor remainders sum to `o(1 | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.tendsto_cross` | subgoal of Section 3 Q^π(ℝ^d | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.traceExt` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.traceExt_monotone` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasQuadraticVariation::HasQuadraticVariation.trace_monotoneOn` | subgoal of Lemma 4.2 trace measure | 0 |
| done | `Smooth.HasScalarQuadraticVariation::HasScalarQuadraticVariation.qvExt` | subgoal of Eq. (5 | 0 |
| done | `Smooth.HasScalarQuadraticVariation::HasScalarQuadraticVariation.qvExt_monotone` | subgoal of Eq. (5 | 0 |
| done | `Smooth.PathOscillation::pathOscillation.vanishes_of_mesh` | subgoal of Eq. (6 | 0 |
| done | `Smooth.Proposition31::proposition_3_1.abs_integral_sub_grid_le` | subgoal of Proposition 3.1 proof, convergence of `I_1^n`, grid step | 0 |
| done | `Smooth.Proposition31::proposition_3_1.inner_apply_eq` | subgoal of Proposition 3.1 proof, `⟨∇f, δω ᵗδω⟩` by polarization | 0 |
| done | `Smooth.Proposition31::proposition_3_1.norm_sub_left_le` | subgoal of Proposition 3.1 proof, (6 | 0 |
| done | `Smooth.Proposition31::proposition_3_1.norm_taylor_le` | subgoal of Proposition 3.1 proof, Newton–Leibniz remainder `r_k^n` | 0 |
| done | `Smooth.Proposition31::proposition_3_1.riemannSum_eq` | subgoal of Proposition 3.1 proof: splitting the discrete covariation | 0 |
| done | `Smooth.Proposition31::proposition_3_1.stieltjesMeasure_Ioc` | subgoal of Proposition 3.1 proof: Stieltjes measure of an interval | 0 |
| done | `Smooth.Proposition31::proposition_3_1.tendsto_boundary` | subgoal of Proposition 3.1 proof: the straddling interval `t_k < t < t_{k+1}` contributes at most `sup |∇f| · osc(ω, π_n | 0 |
| done | `Smooth.Proposition31::proposition_3_1.tendsto_main` | subgoal of Proposition 3.1 proof: `I_1^n(t | 0 |
| done | `Smooth.Proposition31::proposition_3_1.tendsto_remainder` | subgoal of Proposition 3.1 proof: `I_2^n(t | 0 |
| done | `Smooth.Proposition31::proposition_3_1.tendsto_riemannStieltjes` | subgoal of Proposition 3.1 proof, convergence of `I_1^n`, [CF10] | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_kernel_le_of_ge` | subgoal of Lemma 2.2 proof, `d ≤ α` | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_kernel_le_of_lt` | subgoal of Lemma 2.2 proof, `α < d` | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_le` | subgoal of Lemma 2.2 proof, maximal function on a closed ball | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_shell_le` | subgoal of Lemma 2.2 proof, `α < d`, one dyadic shell | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.subset_closedBall` | subgoal of Lemma 2.2 proof, `Q ⊂ B̄(x, diam Q | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.abs_sub_average_le` | subgoal of Theorem 2.1 proof, the Lebesgue-point limit | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.abs_sub_le_lintegral_segment` | subgoal of Theorem 2.1 proof, (2 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.ball_subset_subset` | subgoal of Theorem 2.1 proof: ball sandwich for cubes and balls | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.contDiff_convolution` | subgoal of Theorem 2.1 proof, mollification step 1 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.coord_integrable` | subgoal of Theorem 2.1 proof, mollification: the weak gradient of `f ∈ W^{1,1}` is integrable, since it agrees a.e. with the `L¹` weak derivatives given by `W^{1,1}` | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.exists_mollifier` | subgoal of Theorem 2.1 proof, mollification: a smooth approximate identity exists | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.exists_subseq_ae_tendsto_zero` | subgoal of Theorem 2.1 proof, mollification: `L¹` convergence gives a.e. convergence of a subsequence, for `ℝ≥0∞`-valued functions | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.isCubeOrBall_props` | subgoal of Theorem 2.1 proof: cubes and balls | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.lintegral_Ioc_rpow_indicator_le` | subgoal of Theorem 2.1 proof, (2 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.lintegral_ball_kernel_le` | subgoal of Theorem 2.1 proof, [BH93, Lemma 2] with `α = 1` | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.lintegral_comp_homothety_le` | subgoal of Theorem 2.1 proof, (2 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.lintegral_convolution_le` | subgoal of Theorem 2.1 proof, mollification step 2: Young's inequality in `L¹` | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.lintegral_potential_le` | subgoal of Theorem 2.1 proof: the Riesz potential `I¹_Q` is bounded on `L¹(Q | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.poincare_ae` | subgoal of Theorem 2.1 proof, eq. (2 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.poincare_of_contDiff` | subgoal of Theorem 2.1 proof, eq. (2 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.preciseRepresentative_eq` | subgoal of Theorem 2.1 proof: at a Lebesgue point the precise representative is the Lebesgue value | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.tendsto_convolution` | subgoal of Theorem 2.1 proof, mollification step 4 | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.tendsto_convolution_of_hasCompactSupport` | subgoal of Theorem 2.1 proof, mollification step 3: continuous compactly supported case | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.tendsto_lintegral_gradient` | subgoal of Theorem 2.1 proof, mollification: `∇(f * ψ_n | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.testDeriv_single` | subgoal of Theorem 2.1 proof, mollification step 1, first-order test derivative | 0 |
| done | `Sobolev.Theorem21First::theorem_2_1_first.volume_inter_ball_ge` | subgoal of Theorem 2.1 proof: cubes and balls have positive density at each of their points | 0 |

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
| done | `Sobolev.Lemma22` | Lemma 2.2 | 0 |  |
| done | `Sobolev.LocalMaximalFunction` | Section 2.1 M_R f | 0 |  |
| done | `Sobolev.MemW` | Section 2.1 W^{k,p} | 0 |  |
| done | `Sobolev.MemW2Plus` | Section 2.1 W^{2+,p} | 0 |  |
| done | `Sobolev.MemW2PlusS` | Section 5.2 W^{2+s,p} | 0 |  |
| done | `Sobolev.MemWLoc` | W^{1,2}_loc | 0 |  |
| done | `Sobolev.PreciseRepresentative` | Eq. (3) | 0 |  |
| blocked | `Sobolev.Theorem21` | Theorem 2.1 | 1 | `Sobolev.Theorem21First` |
| open | `Sobolev.Theorem21First` |  | 0 |  |
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
| done | `Smooth.Corollary32` | Corollary 3.2 | 0 |  |
| done | `Smooth.DiscreteQuadraticVariation` | Eq. (5) sums | 0 |  |
| done | `Smooth.FollmerIntegral` | Corollary 3.2 integral | 0 |  |
| done | `Smooth.FollmerItoFormula` | [Föl81] Itô formula | 0 |  |
| done | `Smooth.HasQuadraticVariation` | Section 3 Q^π(ℝ^d) | 0 |  |
| done | `Smooth.HasScalarQuadraticVariation` | Eq. (5) | 0 |  |
| done | `Smooth.PathOscillation` | Eq. (6) | 0 |  |
| done | `Smooth.PathwiseCovariation` | Proposition 3.1 covariation | 0 |  |
| done | `Smooth.Proposition31` | Proposition 3.1 | 0 |  |

### §4 Occupation measures and 𝓦²_{ω,π}

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Occupation.ApproximatingSequence` | Eq. (8) | 0 |  |
| done | `Occupation.DiscreteLocalTime` | Remark 4.5 λ^{n,±}_T [DOS18] | 0 |  |
| done | `Occupation.DiscreteOccupationDensity` | Eq. (7) | 0 |  |
| done | `Occupation.DiscreteSeminorm` | Section 4.2 ‖h‖_{n,p,ω} | 0 |  |
| done | `Occupation.IncrementBall` | Eq. (7) Q^n_i | 0 |  |
| done | `Occupation.Lemma42` | Lemma 4.2 | 0 |  |
| done | `Occupation.NormalizedQuadraticDensity` | Eq. (28) | 0 |  |
| done | `Occupation.OccupationConstant` | Eq. (7) c_d | 0 |  |
| done | `Occupation.OccupationSeminorm` | Section 4.2 seminorm, (10), (11) | 0 |  |
| done | `Occupation.PathwiseSobolevSpace` | Definition 4.3 | 0 |  |
| open | `Occupation.Remark44` | Remark 4.4 | 3 |  |
| blocked | `Occupation.Remark45` | Remark 4.5 | 4 | `Occupation.Remark44` |
| done | `Occupation.WeightedOccupationMeasure` | Lemma 4.2 μ^T_ω | 0 |  |

### §5 Main results

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Main.BalancedPartitions` | Assumption 1 | 0 |  |
| done | `Main.Eq18` |  | 0 |  |
| done | `Main.GeometricMeshDecay` | Assumption 2, (30), (31) | 0 |  |
| done | `Main.IsItoIntegral` | Itô integral | 0 |  |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `Main.Theorem52` |
| open | `Main.Remark54` | Remark 5.4 | 3 |  |
| done | `Main.SmoothItoAt` |  | 0 |  |
| done | `Main.Theorem51` | Theorem 5.1 | 0 |  |
| done | `Main.Theorem51Steps` |  | 0 |  |
| blocked | `Main.Theorem52` | Theorem 5.2 | 2 | `Bessel.IsBrownianPolar` |
| done | `Main.WeakCovariation` | Eq. (15) | 0 |  |
| done | `Main.WeakPathwiseIntegral` | Eq. (16) | 0 |  |

### Appendices A–B

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Appendix.GaussianMoment` | Lemma A.1 c_{q,d} | 0 |  |
| done | `Appendix.HeatKernel` | Eqs. (32), (34), (35) | 0 |  |
| done | `Appendix.LemmaA1` | Lemma A.1 | 0 |  |
| blocked | `Appendix.LemmaB1` | Lemma B.1 | 1 | `Bessel.IsBrownianPolar` |
| blocked | `Appendix.LemmaB2` | Lemma B.2 | 1 | `Appendix.LemmaB2::lemma_B_2_literal`, `Bessel.IsBrownianPolar` |
| done | `Appendix.PotentialProfile` | Eq. (33) | 0 |  |

