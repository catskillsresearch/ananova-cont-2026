# Proof holes (Ananova–Cont 2026 / WeakPathwiseIto)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`. A subgoal is **done** exactly when `sorryAx` is not among its `#print axioms` (recorded by `scripts/axioms_check.py` in `holes-axioms.json`); it is **open** if its own body has `sorry`, and **blocked** if it uses `sorry` only through lemmas it cites.

**Updated:** 2026-11-27T20:50:17Z  
**`sorry` occurrences:** 19 · 13 open · 13 blocked · 419 done (goals + subgoals) · goals {'open': 2, 'blocked': 10, 'done': 66} · subgoals {'open': 11, 'blocked': 3, 'done': 353} · 9 file(s) with `sorry`.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/axioms_check.py  # after lake build: #print axioms per subgoal -> holes-axioms.json
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, holes-edges.txt, holes.html
scripts/serve_holes.sh           # http://127.0.0.1:8770/holes.html
```

## Paper goals

| Status | Module | Paper | `sorry` | Holes |
|---|---|---|---|---|
| done | `Main.Theorem51` | Theorem 5.1 | 0 |  |
| blocked | `Main.Theorem52` | Theorem 5.2 | 0 |  |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `proposition_5_3` |

## Open now

| Module | Paper | `sorry` | Holes |
|---|---|---|---|
| `Bessel.Theorem26` | Theorem 2.6 | 1 | `theorem_2_6` |
| `Main.Remark54` | Remark 5.4 | 3 | `remark_5_4_dim_one`, `remark_5_4_not_implied`, `remark_5_4_sufficient` |

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
| done | `Bessel.BesselCapacity::besselCapacity.IsNull.iUnion` | subgoal of Definition 2.7, countable unions | 0 |
| open | `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_one` | subgoal of Lemma B.1 proof, [AM71] | 1 |
| open | `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_p` | subgoal of Appendix C proof of Theorem 5.2, [AM71] | 1 |
| done | `Bessel.BesselCapacity::besselCapacity.eLpNorm_rpow_eq` | subgoal of Definition 2.7, countable subadditivity, step 2 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.exists_feasible_lt` | subgoal of Definition 2.7, countable subadditivity, step 5 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.iSup_rpow_le_tsum` | subgoal of Definition 2.7, countable subadditivity, step 4 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.iUnion_le` | subgoal of Definition 2.7, countable subadditivity [Fuk93] | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.nonnegPotential_mono_ae` | subgoal of Definition 2.7, countable subadditivity, step 1 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.one_le_of_toReal_eq_zero` | subgoal of Definition 2.7, countable subadditivity, step 3 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.supFn` | subgoal of Definition 2.7, countable subadditivity, step 6 | 0 |
| done | `Bessel.BesselCapacity::besselCapacity.supFn_props` | subgoal of Definition 2.7, countable subadditivity, step 6 | 0 |
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
| done | `Bessel.BesselSpace::BesselSpace.aestronglyMeasurable_potential` | subgoal of Definition 2.5, Young: `g_α ⋆ f` is a.e. strongly measurable | 0 |
| done | `Bessel.BesselSpace::BesselSpace.eLpNorm_potential_le` | subgoal of Definition 2.5, Young's inequality | 0 |
| done | `Bessel.BesselSpace::BesselSpace.enorm_potential_le` | subgoal of Definition 2.5, Young: pointwise bound `|g_α ⋆ f(x | 0 |
| done | `Bessel.IsBrownianPolar::IsBrownianPolar.iUnion` | subgoal of Definition 2.8, countable unions | 0 |
| open | `Bessel.IsBrownianPolar::IsBrownianPolar.iff_isNull` | subgoal of Definition 2.8, [Fuk93, p. 25] | 1 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.aemeasurable_of_aemeasurable_eval` | subgoal of Section 2.2 Wiener space, measurability of `ω' ↦ x + W(ω' | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.exists_isLaw` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.ext_of_map_coe` | subgoal of Section 2.2 Wiener space, uniqueness step 2 | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isLaw_P` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isLaw_unique` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.isProbabilityMeasure_P` | subgoal of Section 2.2 Wiener space | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.map_coords_restrict` | subgoal of Section 2.2 Wiener space, uniqueness step 3: finite-dimensional distributions of `d` independent Brownian motions | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.map_restrict_eq` | subgoal of Section 2.2 Wiener space, uniqueness step 4: f.d.d. of `ℙ` | 0 |
| done | `Bessel.WienerLawExists::CanonicalWienerSpace.measurableSpace_eq_comap_coe` | subgoal of Section 2.2 Wiener space, uniqueness step 1: Borel = cylinder σ-algebra | 0 |
| done | `Bessel.Young::BesselSpace.young.lintegral_conv_le_of_ae_le` | subgoal of Definition 2.5, Young for `p = ∞`: an a.e. bound on `F` passes through | 0 |
| done | `Bessel.Young::BesselSpace.young.lintegral_lintegral_sub_mul` | subgoal of Definition 2.5, Young: Tonelli and translation invariance, `∫∫ K(x - y | 0 |
| done | `Bessel.Young::BesselSpace.young.lintegral_rpow_conv_le` | subgoal of Definition 2.5, Young for `1 ≤ q < ∞` in integrated form, `∫ (∫ K(x - y | 0 |
| done | `Bessel.Young::BesselSpace.young.rpow_lintegral_mul_le` | subgoal of Definition 2.5, Young: weighted Jensen via Hölder, `(∫ u v | 0 |
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
| open | `Main.Proposition53Steps::proposition_5_3.elementary_isometry` | subgoal of P53.B, elementary Itô isometry | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.elementary_localisation` | subgoal of P53.B, localisation | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.increment_moments` | subgoal of P53.A, increment moments | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.indepFun_coords_past_shift` | subgoal of P53.A, independent Brownian coordinates: the joint past is independent of the joint future increments | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.indepFun_past_increment` | subgoal of P53.A, canonical space | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.indep_naturalSigma_increment` | subgoal of P53.A | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.integral_inner_increment_mul_eq_zero` | subgoal of P53.A, cross terms | 1 |
| open | `Main.Proposition53Steps::proposition_5_3.integral_inner_increment_sq` | subgoal of P53.A, one-step isometry | 1 |
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
| done | `Main.Theorem52Mollify::theorem_5_2.abs_convolution_le` | subgoal of Appendix C, mollification: `|h * ψ| ≤ ‖h‖_1 ‖ψ‖_∞` | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.contDiffBounded_convolution` | subgoal of Appendix C, mollification: `F * ψ ∈ C²_b` for `F ∈ W^{2,1}`: its derivatives of order `≤ 2` are `F * ψ`, `F * Dψ`, `F * D²ψ`, bounded by `‖F‖_1 ‖D^k ψ‖_∞` | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.coord_toEuclideanCLM` | subgoal of Appendix C, mollification: the `(i, j | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.eLpNorm_mollify_sub_le` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 3: Minkowski's integral inequality, `‖ψ ⋆ f - f‖_p ≤ sup_{|z| < r} ‖f(· - z | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.exists_isWeakGradient` | subgoal of Appendix C, mollification: a `W^{1,1}` function has a weak gradient, assembled from its first-order weak derivatives | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.exists_isWeakGradient_of_memW` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 1: a `W^{k,q}` function, `k ≥ 1`, has a weak gradient, assembled from its first-order weak derivatives | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.exists_isWeakHessian` | subgoal of Appendix C, mollification: a `W^{2,1}` function has a weak Hessian, assembled from its second-order weak derivatives | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.fderiv_convolution_apply` | subgoal of Appendix C, mollification: `∂_v (F * g | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.isWeakDerivative_single_of_contDiff` | subgoal of Appendix C, mollification: the classical partial derivative of a `C¹` function is its weak derivative, by integration by parts | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.isWeakDerivative_zero` | subgoal of Appendix C, mollification: `D^0 f = f` weakly | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.le_one_cases` | subgoal of Appendix C, mollification: the multi-indices of order `≤ 1` are `0` and `e_i` | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.memLp_of_isWeakHessian` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 4: the weak Hessian of a `W^{2,p}` function is in `L^p`, by uniqueness of weak derivatives | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.memW_convolution` | subgoal of Appendix C, mollification: `F * ψ ∈ W^{2,1}` for `F ∈ W^{2,1}`: its classical, hence weak, derivatives of order `≤ 2` are `F * D^α ψ`, integrable by Young's inequality | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.mollify_mem` | subgoal of Appendix C, mollification: `F_m ∈ C²_b ∩ W^{2,1}` | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.mollify_sub_eq` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 3: `(ψ ⋆ f | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.norm_convolution_le_of_bound` | subgoal of Appendix C, mollification: `‖(F ⋆[L] g | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.order_le_two_cases` | subgoal of Appendix C, mollification: the multi-indices of order `≤ 2` are `0`, `e_i` and `e_i + e_j` | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.smoothHessian_convolution` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 1: the Hessian of the mollification is the mollified weak Hessian, `∇²(F ⋆ ψ | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.tendsto_eLpNorm_comp_sub_sub` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 2: translation is continuous in `L^p`, `‖f(· - z | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.tendsto_eLpNorm_comp_sub_sub_of_hasCompactSupport` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 2: translation is continuous in `L^p` for continuous compactly supported functions | 0 |
| done | `Main.Theorem52Mollify::theorem_5_2.tendsto_eLpNorm_mollify_sub` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 3: mollification converges in `L^p`, `‖ψ_n ⋆ f - f‖_p → 0` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.ae_forall_partition_not_mem` | subgoal of Theorem 5.2, step 5: a Lebesgue-null set `N` is almost surely never visited at the positive partition points `t_j`, `j ≠ 0`, of any `π_n`; these form a countable subset of `(0, T]` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.ae_localMaximalFunction_lt_top` | subgoal of Appendix C, `N_m = {M_1 u_m = ∞}` is Lebesgue-null: `M_1 u_m ∈ L^p` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.ae_path_zero` | subgoal of Appendix C, `B(0 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.ae_tendsto_mollify_path` | subgoal of Theorem 5.2, step 4: if the polar set `E` contains every non-Lebesgue point of `F` and `x₀ ∉ E`, then a.s. the path stays at Lebesgue points on `[0, T]` (at `t = 0` it sits at `x₀` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.continuousOn_path` | subgoal of Appendix C, Brownian paths are continuous on `[0, T]` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.discreteSeminorm_enorm_rpow` | subgoal of Appendix C, `‖g‖_{n,p,B} = ‖g^p‖^{1/p}_{n,1,B}` for `g ≥ 0` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.exists_index_memLp_gagliardo` | subgoal of Theorem 5.2, step 1: since `‖A_n‖_p → 0` and the Gagliardo seminorms of `u_n = |A_n|` tend to `0`, from some index `N` on every `u_n` is in `L^p` with finite Gagliardo seminorm; the sequence is then re-indexed from `N` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.exists_mollifier` | subgoal of Appendix C, standard mollifier `η_m(x | 0 |
| blocked | `Main.Theorem52PathSteps::theorem_5_2.exists_polar_forall_potential_lt_top` | subgoal of Theorem 5.2, step 3: Lemma B.1 for each `u_k`, and a countable union of polar sets is polar, give one polar set off which every `u_k` has finite potential `∫ |u_k(x | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.integrable_norm_hessian_sub` | subgoal of Appendix C, `u_m ∈ L^1` for Lemma B.1 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.isBrownianPolar_union` | subgoal of Theorem 5.2, step 3: the union of two polar sets is polar, since the event of hitting `A ∪ B` at some `t ∈ (0, T]` is the union of the two null hitting events | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.le_limsup_discreteSeminorm_first` | subgoal of Appendix C, (11 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.lemma_B_2_hyps_maximal` | subgoal of Theorem 5.2, step 2: for `u ∈ L^p` with finite Gagliardo seminorm, `h = (M_1 u | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.lintegral_le_maximal_first` | subgoal of Appendix C, (10 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.lintegral_piece_le_first` | subgoal of Appendix C, `i = 0` increment: the kernel centred at `a = x₀` is kept explicit, `∫ |f| 𝓛^{n,0} ≤ C (∫_{B̄(a,|b-a| | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.memLp_maximal_toReal` | subgoal of Theorem 5.2, step 2: `g = (M_1 u | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.occupationSeminorm_norm` | subgoal of Theorem 5.2, step 5: `‖f‖_{B,π}` only sees `|f|`, so the matrix-valued Hessian error can be replaced by its pointwise norm `u_m = ‖∇²F_m - H‖` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.rpow_le_potentialProfile` | subgoal of Appendix C, `‖z - x₀‖^{2-d} ≤ ν(‖z - x₀‖ | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.tendsto_eLpNorm_maximal_rpow` | subgoal of Theorem 5.2, step 2: if `u_m → 0` in `L^p` then `h_m = (M_1 u_m | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.tendsto_eLpNorm_rpow_one` | subgoal of Appendix C, `‖h_m‖_{L^1} = ‖g_m‖^p_{L^p} → 0` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.tendsto_limsup_discreteSeminorm_of_rpow` | subgoal of Theorem 5.2, step 5: Lemma B.2 controls `h_m = g_m^p` in the `n,1` seminorm; this transfers to `g_m` in the `n,p` seminorm, `‖g‖_{n,p} = ‖g^p‖_{n,1}^{1/p}`, and the `limsup` commutes with the continuous increasing map `a ↦ a^{1/p}` | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.tendsto_lintegral_closedBall_kernel` | subgoal of Appendix C, `J_{m,n}(x₀ | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.tendsto_occupationSeminorm_of_maximal` | subgoal of Theorem 5.2, step 5: along one path, Appendix C (11 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.vanishes_path` | subgoal of Theorem 5.2, step 5: under Assumption 2 the mesh tends to `0`, so every Brownian path satisfies the oscillation condition (6 | 0 |
| done | `Main.Theorem52PathSteps::theorem_5_2.volume_iUnion_maximal_eq_top` | subgoal of Theorem 5.2, step 5: for `u_k ∈ L^p`, `p > 1`, the points where some `M_1 u_k` is infinite form a Lebesgue-null set | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.abs_mollify_sub_le` | subgoal of Appendix C, mollification at Lebesgue points: `|F * ψ(x | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.abs_setAverage_sub_le` | subgoal of Appendix C, mollification at Lebesgue points: `|⨍_s f - c| ≤ ⨍_s |f - c|` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.ae_eq_of_isWeakHessian` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 5: the weak Hessian is unique a.e., entrywise by uniqueness of weak derivatives | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.ae_forall_mem_not_mem_null` | subgoal of Appendix C, Brownian motion has a density at positive times: it a.s. avoids a Lebesgue-null set at countably many positive times, e.g. the partition points `t^n_i > 0` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.ae_forall_path_not_mem` | subgoal of Appendix C, Brownian motion does not enter a polar set at positive times | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.ae_localMaximalFunction_ne_top` | subgoal of Appendix C, `M_1 f < ∞` a.e. for `f ∈ L^p`, `p > 1` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.eLpNorm_maximal_le` | subgoal of Appendix C, Hardy–Littlewood: `M_1` is bounded on `L^p`, `p > 1` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.enorm_rpow_sub_rpow_le` | subgoal of Appendix C, `lintegral_rpow_sub_le`: mean value bound `|a^p - b^p| ≤ p |a - b| (a^{p-1} + b^{p-1} | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.enorm_toReal_sub_le` | subgoal of Appendix C, sublinearity of `M_1` at two points: `|M_1 f(x | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.exists_lintegral_edist_rpow_le` | subgoal of Appendix C, `lintegral_rpow_sub_le`: the kernel `|x - y|^{-β}`, `β < d`, has uniformly bounded integrals over a compact set `K` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.gagliardo_maximal_le` | subgoal of Appendix C, `M_1` is bounded on `W^{s,p}`: translation invariance and sublinearity, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.gagliardo_maximal_le_of_measurable` | subgoal of Appendix C, `[M_1 f]_{W^{s,p}} ≤ C_p [f]_{W^{s,p}}` for measurable `f ∈ L^p`, with the Hardy–Littlewood constant of `hardyLittlewood.lintegral_rpow_le` | 0 |
| blocked | `Main.Theorem52Steps::theorem_5_2.isBrownianPolar_nonLebesgue` | subgoal of Appendix C, `E₁` is polar: Theorem 2.9, [AM71, Thm. 1], [Fuk93] | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_gagliardo_eq_shift` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 5: the Gagliardo double integral in difference coordinates, `∫∫ ‖A x - A y‖^p / |x - y|^r = ∫ (∫ ‖A(x + h | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_lintegral_eq_add` | subgoal of Appendix C, Tonelli in difference coordinates: `∫∫ Φ(x, y | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_lintegral_eq_add'` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 5: Tonelli in difference coordinates for a.e.-measurable integrands, `∫∫ Φ(x, y | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_mul_rpow_div_lt_top` | subgoal of Appendix C, `lintegral_rpow_sub_le`: the piece with `g(x | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_mul_rpow_div_lt_top'` | subgoal of Appendix C, `lintegral_rpow_sub_le`: the piece with `g(y | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_rpow_sub_le` | subgoal of Appendix C, second hypothesis of Lemma B.2 for `h = g^p`: Hölder on `K × K` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.lintegral_shift_mollify_sub_le` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 5: domination, `‖a_n(· + h | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.localMaximalFunction_comp_add` | subgoal of Appendix C, `M_1` commutes with translations: `M_1(f(· + h | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.measure_path_mem_null` | subgoal of Appendix C, `ae_forall_mem_not_mem_null` at one time: for `0 < t ≤ T`, `ℙ_{x₀}(B(t | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.mul_rpow_div_le_add` | subgoal of Appendix C, `lintegral_rpow_sub_le`: Young's inequality off the diagonal, `a c^{p-1} / e^d ≤ a^p / e^{sp+d} + c^p / e^{d - sp/(p-1 | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.pi_absolutelyContinuous` | subgoal of Appendix C, `ae_forall_mem_not_mem_null`: a finite product of absolutely continuous measures on `ℝ` is absolutely continuous with respect to the product | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.preciseRepresentative_eq_of_tendsto` | subgoal of Appendix C, mollification at Lebesgue points: at a Lebesgue point with value `c`, `F̃(x | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.tendsto_lintegral_shift_mollify_sub` | subgoal of Appendix C, `tendsto_mollify_hessian`, step 5: for a fixed shift `h`, the difference `a_n(x + h | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.tendsto_mollify_hessian` | subgoal of Appendix C, mollification converges in `W^{2+s,p}`: `u_m → 0` in `L^p` and in the Gagliardo seminorm `[·]_{W^{s,p}}` | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.tendsto_mollify_of_isLebesguePoint` | subgoal of Appendix C, mollification: `F_m(x | 0 |
| done | `Main.Theorem52Steps::theorem_5_2.volume_coords_preimage_null` | subgoal of Appendix C, `ae_forall_mem_not_mem_null`: in coordinates, the preimage of a Lebesgue-null set under `v ↦ x₀ + ∑_i v^i e_i` is Lebesgue-null in `ℝ^{Fin d}` | 0 |
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
| done | `Occupation.Remark44::remark_4_4.aestronglyMeasurable_mollify_sub` | subgoal of Remark 4.4 inclusion, measurability | 0 |
| done | `Occupation.Remark44::remark_4_4.conjExponent_facts` | subgoal of Remark 4.4 inclusion, conjugate exponent | 0 |
| done | `Occupation.Remark44::remark_4_4.integrable_mul_conj` | subgoal of Remark 4.4, Hölder | 0 |
| done | `Occupation.Remark44::remark_4_4.lintegral_le_eLpNorm_mul` | subgoal of Remark 4.4 inclusion, Hölder | 0 |
| done | `Occupation.Remark44::remark_4_4.lintegral_ofReal_mul_eq` | subgoal of Remark 4.4, lower vs. Bochner integral | 0 |
| done | `Occupation.Remark44::remark_4_4.tendsto_mollify_of_continuousAt` | subgoal of Remark 4.4 inclusion, path convergence | 0 |
| done | `Occupation.Remark44::remark_4_4.tendsto_seminorm_mollify_sub` | subgoal of Remark 4.4 inclusion, Hessian convergence | 0 |
| done | `Occupation.Remark45::Partition.reverse_left` | subgoal of Remarks 4.1 and 4.5 | 0 |
| done | `Occupation.Remark45::Partition.reverse_right` | subgoal of Remarks 4.1 and 4.5 | 0 |
| done | `Occupation.Remark45::Rd.coord_one_apply` | subgoal of Remark 4.5, identifying `ℝ` with `ℝ^1` | 0 |
| done | `Occupation.Remark45::Rd.coord_one_injective` | subgoal of Remark 4.5, identifying `ℝ` with `ℝ^1` | 0 |
| done | `Occupation.Remark45::Rd.norm_one_eq` | subgoal of Remark 4.5, identifying `ℝ` with `ℝ^1` | 0 |
| done | `Occupation.Remark45::discreteLocalTime.reversed_eq` | subgoal of Remark 4.5, `λ^{n,-}_T` | 0 |
| done | `Occupation.Remark45::discreteOccupationDensity.piece_one` | subgoal of Remark 4.5, eq. (7 | 0 |
| done | `Occupation.Remark45::incrementBall_one_iff` | subgoal of Remark 4.5, eq. (7 | 0 |
| done | `Occupation.Remark45::occupationConstant_one` | subgoal of Remark 4.5, eq. (7 | 0 |
| done | `Occupation.Remark45::remark_4_5.ae_nonneg_of_weakLpTendsto` | subgoal of Remark 4.5, positivity of weak limits | 0 |
| done | `Occupation.Remark45::remark_4_5.eLpNorm_top_le_of_setIntegral_abs_le` | subgoal of Remark 4.5 bounded case, `L^∞` norm by duality | 0 |
| done | `Occupation.Remark45::remark_4_5.exists_pairing` | subgoal of Remark 4.5 bounded case, the `L^1`–`L^∞` pairing | 0 |
| done | `Occupation.Remark45::remark_4_5.exists_uniform_bound` | subgoal of Remark 4.5 bounded case, Banach–Steinhaus | 0 |
| done | `Occupation.Remark45::remark_4_5.setIntegral_abs_le_opNorm` | subgoal of Remark 4.5 bounded case, testing against signs | 0 |
| done | `Occupation.Remark45::remark_4_5.weakLpTendsto_congr` | subgoal of Remark 4.5, weak convergence is a.e.-invariant | 0 |
| done | `Occupation.Remark45::remark_4_5.weakLpTendsto_half_add` | subgoal of Remark 4.5, averaging | 0 |
| done | `Occupation.Remark45::remark_4_5.weakLpTendsto_posPart` | subgoal of Remark 4.5, positive part | 0 |
| done | `Occupation.Remark45::remark_4_5_term_eq` | subgoal of Remark 4.5, identity off the endpoints | 0 |
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
| done | `Sobolev.HardyLittlewood::hardyLittlewood.le_globalMaximalFunction` | subgoal of Hardy–Littlewood, `M_1 f ≤ M f` pointwise, with `M` Carleson's uncentred `globalMaximalFunction` | 0 |
| done | `Sobolev.HardyLittlewood::hardyLittlewood.lintegral_rpow_le` | subgoal of Hardy–Littlewood, strong type `(p, p | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_kernel_le_of_ge` | subgoal of Lemma 2.2 proof, `d ≤ α` | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_kernel_le_of_lt` | subgoal of Lemma 2.2 proof, `α < d` | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_closedBall_le` | subgoal of Lemma 2.2 proof, maximal function on a closed ball | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.lintegral_shell_le` | subgoal of Lemma 2.2 proof, `α < d`, one dyadic shell | 0 |
| done | `Sobolev.Lemma22::lemma_2_2.subset_closedBall` | subgoal of Lemma 2.2 proof, `Q ⊂ B̄(x, diam Q | 0 |
| done | `Sobolev.LocalMaximalFunction::localMaximalFunction.congr_ae` | subgoal of `M_1`, `M_1 f` depends only on the a.e. class of `f` | 0 |
| done | `Sobolev.LocalMaximalFunction::localMaximalFunction.le_add` | subgoal of `M_1`, sublinearity: `|f| ≤ |g| + |h|` gives `M_1 f ≤ M_1 g + M_1 h` | 0 |
| done | `Sobolev.LocalMaximalFunction::localMaximalFunction.lowerSemicontinuous_mul_measure_ball` | subgoal of `M_1`, `M_1 f` is Borel: `x ↦ c ν(B(x, r | 0 |
| done | `Sobolev.LocalMaximalFunction::localMaximalFunction.measurable` | subgoal of `M_1`, `M_1 f` is Borel: a supremum of lower semicontinuous ball averages | 0 |
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
| done | `Sobolev.Theorem21Second::theorem_2_1_second.abs_sub_taylorAverage_le` | subgoal of Theorem 2.1 proof, second estimate: [BH93, Thm 1, (5 | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.abs_taylor_le` | subgoal of Theorem 2.1 proof, second estimate, (5 | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.coord_hessian_integrable` | subgoal of Theorem 2.1 proof, second estimate: the Hessian entries are integrable | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.hessian_convolution` | subgoal of Theorem 2.1 proof, second estimate: the mollification of a `W^{2,1}` function is `C²`, with second derivatives the mollified weak Hessian entries | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.integrable_hessian` | subgoal of Theorem 2.1 proof, second estimate: the weak Hessian of a `W^{2,1}` function is integrable as an operator-valued map | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.isWeakGradient_coord` | subgoal of Theorem 2.1 proof, second estimate: the coordinates `∂_i f` of the weak gradient have weak gradient `(∂_j ∂_i f | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.lintegral_ball_kernel2_le` | subgoal of Theorem 2.1 proof, second estimate: [BH93, Lemma 2] with `α = 2`, in the unified form `⨍_{B(x,r | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.lintegral_comp_homothety_sq_le` | subgoal of Theorem 2.1 proof, second estimate, (5 | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.lintegral_potential2_le` | subgoal of Theorem 2.1 proof, second estimate: the local Riesz potential of order `2` is bounded on `L¹(Q | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.memW_coord` | subgoal of Theorem 2.1 proof, second estimate: `∂_i f ∈ W^{1,1}` | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.norm_le_sum_entries` | subgoal of Theorem 2.1 proof, second estimate: a bilinear form is bounded by the sum of its entries in the standard basis | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.poincare2_ae` | subgoal of Theorem 2.1 proof, second estimate, (5 | 0 |
| done | `Sobolev.Theorem21Second::theorem_2_1_second.poincare2_of_contDiff` | subgoal of Theorem 2.1 proof, second estimate, (5 | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.abs_average_sub_average_le` | subgoal of Theorem 2.3 proof: averages over comparable concentric balls are close, `|f_{B(x,s | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.abs_average_sub_average_le_maximal` | subgoal of Theorem 2.3 proof: telescoping over dyadic radii, `|f_{B(x,s | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.closedBall_midpoint` | subgoal of Theorem 2.3 proof: the ball with diameter `[x, y]` | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.isLebesguePoint_of_maximal_lt_top` | subgoal of Theorem 2.3 proof: if `M_R|∇f|(x | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.lintegral_abs_sub_average_ball_le` | subgoal of Theorem 2.3 proof, Poincaré on balls: `∫_B |f - f_B| ≤ C r ∫_B |∇f|` | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.lintegral_ball_potential_le` | subgoal of Theorem 2.3 proof, Poincaré on balls, step 1: the Riesz potential `I¹` on a ball `B` of radius `r` is bounded on `L¹(B | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.lintegral_kernel_le_maximal` | subgoal of Theorem 2.3 proof: Lemma 2.2 for vector- or operator-valued integrands, with the maximal radius enlarged to any `R ≥ diam Q` | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.maximal_coord_hessian_le` | subgoal of Theorem 2.3 proof: the gradient of `∂_i f` is dominated by the Hessian | 0 |
| done | `Sobolev.Theorem23Steps::theorem_2_3.maximal_lt_top_of_isLebesguePoint` | subgoal of Theorem 2.3 proof: at a common Lebesgue point of the coordinates of a locally integrable `G`, some local maximal function of `G` is finite | 0 |

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
| done | `Sobolev.HardyLittlewood` | Hardy–Littlewood bound for M_1 (Appendix C; bridge to Carleson project) | 0 |  |
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
| done | `Sobolev.Theorem21` | Theorem 2.1 | 0 |  |
| done | `Sobolev.Theorem21First` |  | 0 |  |
| done | `Sobolev.Theorem21Second` |  | 0 |  |
| done | `Sobolev.Theorem23` | Theorem 2.3 | 0 |  |
| done | `Sobolev.Theorem23Steps` |  | 0 |  |

### §2.2 Bessel potentials, capacity, polar sets

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| blocked | `Bessel.BesselCapacity` | Definition 2.7 | 2 | `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_one`, `Bessel.BesselCapacity::besselCapacity.IsNull.one_two_of_two_p` |
| done | `Bessel.BesselKernel` | Definition 2.4 | 0 |  |
| done | `Bessel.BesselSpace` | Definition 2.5 | 0 |  |
| done | `Bessel.CanonicalWienerSpace` | Section 2.2 Wiener space | 0 |  |
| blocked | `Bessel.IsBrownianPolar` | Definition 2.8 | 1 | `Bessel.BesselCapacity`, `Bessel.IsBrownianPolar::IsBrownianPolar.iff_isNull` |
| done | `Bessel.NonnegPotential` | Definition 2.7 g_α ⋆ h | 0 |  |
| open | `Bessel.Theorem26` | Theorem 2.6 | 1 |  |
| blocked | `Bessel.Theorem29` | Theorem 2.9 | 1 | `Bessel.BesselCapacity` |
| done | `Bessel.WienerLawExists` | Section 2.2 ℙ_x exists (subgoals) | 0 |  |
| done | `Bessel.Young` |  | 0 |  |

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
| done | `Occupation.Remark44` | Remark 4.4 | 0 |  |
| done | `Occupation.Remark45` | Remark 4.5 | 0 |  |
| done | `Occupation.WeightedOccupationMeasure` | Lemma 4.2 μ^T_ω | 0 |  |

### §5 Main results

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Main.BalancedPartitions` | Assumption 1 | 0 |  |
| done | `Main.Eq18` |  | 0 |  |
| done | `Main.GeometricMeshDecay` | Assumption 2, (30), (31) | 0 |  |
| done | `Main.IsItoIntegral` | Itô integral | 0 |  |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `Main.Theorem52` |
| blocked | `Main.Proposition53Steps` | Proposition 5.3 proof steps (route A: P53.A–E) | 8 | `Main.Proposition53Steps::proposition_5_3.elementary_isometry`, `Main.Proposition53Steps::proposition_5_3.elementary_localisation`, `Main.Proposition53Steps::proposition_5_3.increment_moments`, `Main.Proposition53Steps::proposition_5_3.indepFun_coords_past_shift`, `Main.Proposition53Steps::proposition_5_3.indepFun_past_increment`, `Main.Proposition53Steps::proposition_5_3.indep_naturalSigma_increment`, `Main.Proposition53Steps::proposition_5_3.integral_inner_increment_mul_eq_zero`, `Main.Proposition53Steps::proposition_5_3.integral_inner_increment_sq` |
| open | `Main.Remark54` | Remark 5.4 | 3 |  |
| done | `Main.SmoothItoAt` |  | 0 |  |
| done | `Main.Theorem51` | Theorem 5.1 | 0 |  |
| done | `Main.Theorem51Steps` |  | 0 |  |
| blocked | `Main.Theorem52` | Theorem 5.2 | 0 | `Appendix.LemmaB2`, `Bessel.IsBrownianPolar`, `Main.Theorem52PathSteps`, `Main.Theorem52Steps` |
| done | `Main.Theorem52Mollify` | Appendix C mollification steps | 0 |  |
| blocked | `Main.Theorem52PathSteps` |  | 0 | `Appendix.LemmaB1`, `Main.Theorem52PathSteps::theorem_5_2.exists_polar_forall_potential_lt_top`, `Main.Theorem52Steps` |
| blocked | `Main.Theorem52Steps` |  | 0 | `Bessel.IsBrownianPolar`, `Bessel.Theorem29`, `Main.Theorem52Steps::theorem_5_2.isBrownianPolar_nonLebesgue` |
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

