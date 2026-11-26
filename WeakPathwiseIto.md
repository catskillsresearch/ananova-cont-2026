---
title: "WeakPathwiseIto: a Lean 4 blueprint of a pathwise Itô formula for weakly differentiable functions"
author: "Lars Warren Ericson"
date: "2026"
---

# Abstract

This report accompanies a Lean 4 / Mathlib formalization, at blueprint stage, of
A. Ananova and R. Cont, *A pathwise Ito formula for weakly differentiable functions*,
arXiv:2608.07365v2. Every definition of the paper is a Lean `def` or `structure`, each in its
own file; every numbered result is a Lean `theorem` whose proof is currently `sorry`. The
live proof-hole board is `holes.html` (`python3 scripts/build_holes.py`).

# The paper in one paragraph

For a continuous path $\omega$ with finite quadratic variation along a sequence of
partitions $\pi = (\pi_n)$, the paper introduces discrete weighted occupation densities
$\mathcal L^{\pi_n}_\omega$ (eq. (7)), the seminorm
$\|f\|_{\mathcal W^0_{\omega,\pi}} = \limsup_n \int |f|\,\mathcal L^{\pi_n}_\omega$, and the
path-dependent Sobolev space $\mathcal W^2_{\omega,\pi} \subset W^{2,1}(\mathbb R^d)$
(Definition 4.3). For $F \in \mathcal W^2_{\omega,\pi}$ it constructs the pathwise integral
$\int \nabla F(\omega)\,d^\pi\omega$ and the covariation $[\nabla F(\omega),\omega]_\pi$ and
proves $F(\omega(t)) - F(\omega(0)) = \int_0^t \nabla F(\omega)\,d^\pi\omega +
\tfrac12 [\nabla F(\omega),\omega]_\pi(t)$ (Theorem 5.1). For Brownian paths,
$W^{2+,p} \cap W^{2,1} \subset \mathcal W^2_{B,\pi}$ almost surely outside a polar set of
starting points (Theorem 5.2), and the pathwise integral agrees with the Itô integral
(Proposition 5.3).

# Map from the paper to Lean

| Paper | Lean declaration | File |
|---|---|---|
| Partitions, mesh | `Partition`, `Partition.mesh`, `Partition.minGap` | `Basic/Partition.lean` |
| $C^k_b$ | `ContDiffBounded` | `Basic/ContDiffBounded.lean` |
| Weak derivative, $W^{k,p}$, $W^{k,p}_{loc}$ | `IsWeakDerivative`, `MemW`, `MemWLoc` | `Sobolev/` |
| Weak gradient / Hessian | `IsWeakGradient`, `IsWeakHessian` | `Sobolev/` |
| $W^{2+s,p}$, $W^{2+,p}$ | `MemW2PlusS`, `MemW2Plus` | `Sobolev/` |
| Eq. (3) precise representative | `preciseRepresentative` | `Sobolev/PreciseRepresentative.lean` |
| Maximal function $M_R f$ | `localMaximalFunction` | `Sobolev/LocalMaximalFunction.lean` |
| Theorem 2.1, Lemma 2.2, Theorem 2.3 | `theorem_2_1_first/second`, `lemma_2_2`, `theorem_2_3_first/second` | `Sobolev/` |
| Definitions 2.4, 2.5, 2.7, 2.8 | `besselKernel`, `BesselSpace`, `besselCapacity`, `IsBrownianPolar` | `Bessel/` |
| Canonical Wiener space | `CanonicalWienerSpace` | `Bessel/CanonicalWienerSpace.lean` |
| Theorems 2.6, 2.9 | `theorem_2_6`, `theorem_2_9` | `Bessel/` |
| Eq. (5), $Q^\pi$ | `discreteQuadraticVariation`, `HasScalarQuadraticVariation`, `HasQuadraticVariation` | `Smooth/` |
| Eq. (6) | `pathOscillation`, `pathOscillation.Vanishes` | `Smooth/PathOscillation.lean` |
| Föllmer integral, covariation | `follmerIntegral`, `pathwiseCovariation` | `Smooth/` |
| Proposition 3.1, Corollary 3.2 | `proposition_3_1`, `corollary_3_2` (and `follmer_ito_formula`, [Föl81]) | `Smooth/` |
| Eq. (7) | `occupationConstant`, `incrementBall`, `discreteOccupationDensity` | `Occupation/` |
| Lemma 4.2 | `weightedOccupationMeasure`, `lemma_4_2` | `Occupation/` |
| Seminorm, (10), (11) | `occupationSeminorm` (+ `lintegral_le_maximal`, `le_limsup_discreteSeminorm`) | `Occupation/OccupationSeminorm.lean` |
| Eq. (8), Definition 4.3 | `ApproximatingSequence`, `PathwiseSobolevSpace` | `Occupation/` |
| Remark 4.4 | `remark_4_4` | `Occupation/Remark44.lean` |
| Eqs. (15), (16) | `weakCovariation`, `weakPathwiseIntegral` | `Main/` |
| Theorem 5.1 | `theorem_5_1`, `theorem_5_1_tendsto`, `theorem_5_1_unique` | `Main/Theorem51.lean` |
| Assumptions 1, 2 | `BalancedPartitions`, `GeometricMeshDecay` | `Main/` |
| Theorem 5.2 | `theorem_5_2`, `theorem_5_2_deterministic` | `Main/Theorem52.lean` |
| Itô integral | `IsItoIntegral` | `Main/IsItoIntegral.lean` |
| Proposition 5.3 | `proposition_5_3` | `Main/Proposition53.lean` |
| Eq. (28), Lemma A.1 | `normalizedQuadraticDensity`, `gaussianMoment`, `lemma_A_1` | `Occupation/`, `Appendix/` |
| Eqs. (32)–(35), Lemmas B.1, B.2 | `heatKernel`, `potentialProfile`, `lemma_B_1`, `lemma_B_2` | `Appendix/` |

# Modelling choices

* $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; Hessians are maps `ℝ^d →L[ℝ] ℝ^d`, with the
  operator norm in the seminorm.
* Sobolev spaces are defined from weak derivatives against smooth compactly supported test
  functions. The Bessel kernel is defined by Stein's subordination integral; the Fourier
  characterisation of Definition 2.4 is the lemma `besselKernel.fourier_eq`.
* Quadratic covariation is obtained by polarization from the scalar quadratic variations of
  $\omega^i$ and $\omega^i + \omega^j$, exactly as in Section 3.
* The Itô integral in Proposition 5.3 is characterised as the limit in probability of
  elementary predictable integrals (`IsItoIntegral`).
* In Lemma B.2 the norm $\|h\|_{n,1,B}$ is read as the Riemann sum
  $\sum_i (|h(B(t_i))| + |h(B(t_{i+1}))|)(t_{i+1}-t_i)$ (the displayed $\int_0^T$ is taken to
  be a typo); it is the $p = 1$ case of the seminorm $\|h\|_{n,p,\omega}$ of Section 4.2.

# Main statements (Lean)
