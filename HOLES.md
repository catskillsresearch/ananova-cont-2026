# Proof holes (Ananova–Cont 2026 / WeakPathwiseIto)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-26T16:54:21Z  
**`sorry` occurrences:** 52 · 10 open · 25 blocked · 24 done · 31 file(s) with `sorry`.

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
| `Basic.FunctionOscillation` | Section 4 osc(φ,δ) | 1 | `tendsto_zero` |
| `Bessel.BesselKernel` | Definition 2.4 | 4 | `fourier_eq`, `nonneg`, `integrable`, `asymptotic_origin` |
| `Bessel.CanonicalWienerSpace` | Section 2.2 Wiener space | 1 | `nonempty` |
| `Main.GeometricMeshDecay` | Assumption 2, (30), (31) | 2 | `summable_mesh`, `sum_inv_mesh_le` |
| `Occupation.OccupationConstant` | Eq. (7) c_d | 1 | `eq_inv_integral` |
| `Smooth.HasQuadraticVariation` | Section 3 Q^π(ℝ^d) | 1 | `tendsto_cross` |
| `Smooth.PathOscillation` | Eq. (6) | 1 | `vanishes_of_mesh` |
| `Sobolev.Lemma22` | Lemma 2.2 | 1 | `lemma_2_2` |
| `Sobolev.Theorem21` | Theorem 2.1 | 2 | `theorem_2_1_first`, `theorem_2_1_second` |
| `Sobolev.Theorem23` | Theorem 2.3 | 2 | `theorem_2_3_first`, `theorem_2_3_second` |

## All modules by section

### Preliminaries

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Basic.ContDiffBounded` | C^k_b | 0 |  |
| open | `Basic.FunctionOscillation` | Section 4 osc(φ,δ) | 1 |  |
| done | `Basic.Partition` | Section 3 (partitions) | 0 |  |
| done | `Basic.Rd` |  | 0 |  |
| done | `Basic.SmoothHessian` |  | 0 |  |

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
| blocked | `Bessel.BesselCapacity` | Definition 2.7 | 4 | `Bessel.BesselSpace` |
| open | `Bessel.BesselKernel` | Definition 2.4 | 4 |  |
| blocked | `Bessel.BesselSpace` | Definition 2.5 | 1 | `Bessel.BesselKernel` |
| open | `Bessel.CanonicalWienerSpace` | Section 2.2 Wiener space | 1 |  |
| blocked | `Bessel.IsBrownianPolar` | Definition 2.8 | 2 | `Bessel.BesselCapacity`, `Bessel.CanonicalWienerSpace` |
| blocked | `Bessel.Theorem26` | Theorem 2.6 | 1 | `Bessel.BesselSpace` |
| blocked | `Bessel.Theorem29` | Theorem 2.9 | 1 | `Bessel.BesselCapacity` |

### §3 Smooth change of variable

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| blocked | `Smooth.Corollary32` | Corollary 3.2 | 1 | `Smooth.HasQuadraticVariation`, `Smooth.PathOscillation` |
| done | `Smooth.DiscreteQuadraticVariation` | Eq. (5) sums | 0 |  |
| done | `Smooth.FollmerIntegral` | Corollary 3.2 integral | 0 |  |
| blocked | `Smooth.FollmerItoFormula` | [Föl81] Itô formula | 1 | `Smooth.HasQuadraticVariation`, `Smooth.PathOscillation` |
| open | `Smooth.HasQuadraticVariation` | Section 3 Q^π(ℝ^d) | 1 |  |
| done | `Smooth.HasScalarQuadraticVariation` | Eq. (5) | 0 |  |
| open | `Smooth.PathOscillation` | Eq. (6) | 1 |  |
| done | `Smooth.PathwiseCovariation` | Proposition 3.1 covariation | 0 |  |
| blocked | `Smooth.Proposition31` | Proposition 3.1 | 1 | `Smooth.HasQuadraticVariation`, `Smooth.PathOscillation` |

### §4 Occupation measures and 𝓦²_{ω,π}

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| blocked | `Occupation.ApproximatingSequence` | Eq. (8) | 0 | `Occupation.OccupationSeminorm` |
| blocked | `Occupation.DiscreteOccupationDensity` | Eq. (7) | 4 | `Occupation.OccupationConstant` |
| done | `Occupation.DiscreteSeminorm` | Section 4.2 ‖h‖_{n,p,ω} | 0 |  |
| done | `Occupation.IncrementBall` | Eq. (7) Q^n_i | 0 |  |
| blocked | `Occupation.Lemma42` | Lemma 4.2 | 1 | `Occupation.DiscreteOccupationDensity`, `Occupation.WeightedOccupationMeasure`, `Smooth.PathOscillation` |
| done | `Occupation.NormalizedQuadraticDensity` | Eq. (28) | 0 |  |
| open | `Occupation.OccupationConstant` | Eq. (7) c_d | 1 |  |
| blocked | `Occupation.OccupationSeminorm` | Section 4.2 seminorm, (10), (11) | 3 | `Occupation.DiscreteOccupationDensity`, `Smooth.PathOscillation` |
| blocked | `Occupation.PathwiseSobolevSpace` | Definition 4.3 | 1 | `Occupation.ApproximatingSequence` |
| blocked | `Occupation.Remark44` | Remark 4.4 | 1 | `Occupation.PathwiseSobolevSpace`, `Smooth.HasQuadraticVariation` |
| blocked | `Occupation.WeightedOccupationMeasure` | Lemma 4.2 μ^T_ω | 1 | `Smooth.HasQuadraticVariation` |

### §5 Main results

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Main.BalancedPartitions` | Assumption 1 | 0 |  |
| open | `Main.GeometricMeshDecay` | Assumption 2, (30), (31) | 2 |  |
| blocked | `Main.IsItoIntegral` | Itô integral | 0 | `Bessel.CanonicalWienerSpace` |
| blocked | `Main.Proposition53` | Proposition 5.3 | 1 | `Main.IsItoIntegral`, `Main.Theorem52`, `Main.WeakCovariation`, `Main.WeakPathwiseIntegral` |
| blocked | `Main.Theorem51` | Theorem 5.1 | 3 | `Main.WeakCovariation`, `Main.WeakPathwiseIntegral`, `Smooth.HasQuadraticVariation`, `Smooth.PathOscillation` |
| blocked | `Main.Theorem52` | Theorem 5.2 | 2 | `Bessel.IsBrownianPolar`, `Main.GeometricMeshDecay`, `Occupation.PathwiseSobolevSpace` |
| blocked | `Main.WeakCovariation` | Eq. (15) | 0 | `Occupation.ApproximatingSequence` |
| blocked | `Main.WeakPathwiseIntegral` | Eq. (16) | 0 | `Occupation.ApproximatingSequence` |

### Appendices A–B

| Status | Module | Paper | `sorry` | Blocked by |
|---|---|---|---|---|
| done | `Appendix.GaussianMoment` | Lemma A.1 c_{q,d} | 0 |  |
| blocked | `Appendix.HeatKernel` | Eqs. (32), (34), (35) | 3 | `Main.GeometricMeshDecay` |
| blocked | `Appendix.LemmaA1` | Lemma A.1 | 2 | `Bessel.CanonicalWienerSpace` |
| blocked | `Appendix.LemmaB1` | Lemma B.1 | 1 | `Bessel.IsBrownianPolar` |
| blocked | `Appendix.LemmaB2` | Lemma B.2 | 1 | `Bessel.IsBrownianPolar`, `Main.GeometricMeshDecay` |
| done | `Appendix.PotentialProfile` | Eq. (33) | 0 |  |

