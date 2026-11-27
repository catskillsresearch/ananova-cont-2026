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
| Partitions, mesh, reversed partition | `Partition`, `Partition.mesh`, `Partition.minGap`, `Partition.reverse` | `Basic/Partition.lean` |
| Cube or ball $Q$ (Section 2.1) | `IsCubeOrBall` | `Basic/IsCubeOrBall.lean` |
| Weak / weak-* $L^r$ convergence | `WeakLpTendsto` | `Basic/WeakLpTendsto.lean` |
| $C^k_b$ | `ContDiffBounded` | `Basic/ContDiffBounded.lean` |
| Weak derivative, $W^{k,p}$ (and its norm), $W^{k,p}_{loc}$ | `IsWeakDerivative`, `MemW`, `MemW.norm`, `MemWLoc` | `Sobolev/` |
| Weak gradient / Hessian | `IsWeakGradient`, `IsWeakHessian` | `Sobolev/` |
| $W^{2+s,p}$, $W^{2+,p}$ | `MemW2PlusS`, `MemW2Plus` | `Sobolev/` |
| Eq. (3) precise representative | `preciseRepresentative` | `Sobolev/PreciseRepresentative.lean` |
| Maximal function $M_R f$ | `localMaximalFunction` | `Sobolev/LocalMaximalFunction.lean` |
| Theorem 2.1, Lemma 2.2, Theorem 2.3 | `theorem_2_1_first/second`, `lemma_2_2`, `theorem_2_3_first/second` | `Sobolev/` |
| Definitions 2.4, 2.5, 2.7, 2.8 | `besselKernel`, `BesselSpace`, `besselCapacity`, `IsBrownianPolar` | `Bessel/` |
| Canonical Wiener space $(\Omega, B, \mathbb P_x)$ | `CanonicalWienerSpace`, `.B`, `.path`, `.IsLaw`, `.P` (existence proved in `WienerLawExists`) | `Bessel/` |
| Theorems 2.6, 2.9 | `theorem_2_6`, `theorem_2_9` | `Bessel/` |
| Eq. (5), $Q^\pi$ | `discreteQuadraticVariation`, `HasScalarQuadraticVariation`, `HasQuadraticVariation` | `Smooth/` |
| Eq. (6) | `pathOscillation`, `pathOscillation.Vanishes` | `Smooth/PathOscillation.lean` |
| Föllmer integral, covariation | `follmerIntegral`, `pathwiseCovariation` | `Smooth/` |
| Proposition 3.1, Corollary 3.2 | `proposition_3_1`, `corollary_3_2` (and `follmer_ito_formula`, [Föl81]) | `Smooth/` |
| Eq. (7) | `occupationConstant`, `incrementBall`, `discreteOccupationDensity` | `Occupation/` |
| Lemma 4.2 | `weightedOccupationMeasure`, `lemma_4_2` | `Occupation/` |
| Seminorm, (10), (11) | `occupationSeminorm` (+ `lintegral_le_maximal`, `le_limsup_discreteSeminorm`) | `Occupation/OccupationSeminorm.lean` |
| Eq. (8), Definition 4.3 | `ApproximatingSequence`, `PathwiseSobolevSpace` | `Occupation/` |
| Remark 4.4 | `remark_4_4_density`, `remark_4_4_seminorm`, `remark_4_4` | `Occupation/Remark44.lean` |
| Remark 4.5 | `discreteLocalTime` [DOS18]; `remark_4_5_identity`, `_seminorm`, `_subset`, `_bounded`, `_local_time` | `Occupation/` |
| Eqs. (15), (16) | `weakCovariation`, `weakPathwiseIntegral` | `Main/` |
| Theorem 5.1 | `theorem_5_1`, `theorem_5_1_tendsto`, `theorem_5_1_unique` | `Main/Theorem51.lean` |
| Assumptions 1, 2 | `BalancedPartitions`, `GeometricMeshDecay` | `Main/` |
| Theorem 5.2 | `theorem_5_2`, `theorem_5_2_deterministic` | `Main/Theorem52.lean` |
| Itô integral | `IsItoIntegral` | `Main/IsItoIntegral.lean` |
| Proposition 5.3 | `proposition_5_3` | `Main/Proposition53.lean` |
| Remark 5.4 | `remark_5_4_dim_one`, `_not_implied`, `_sufficient`, `_two_le` | `Main/Remark54.lean` |
| Eq. (28), Lemma A.1 | `normalizedQuadraticDensity`, `gaussianMoment`, `lemma_A_1` | `Occupation/`, `Appendix/` |
| Eqs. (32)–(35), Lemmas B.1, B.2 | `heatKernel`, `potentialProfile`, `lemma_B_1`, `lemma_B_2` (+ `lemma_B_2_literal`) | `Appendix/` |

# Modelling choices

Statements are meant to have exactly the strength of the paper's: no hypothesis is added or
dropped and no conclusion weakened, except where noted below and justified from the paper's
own text.

* $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; Hessians are maps `ℝ^d →L[ℝ] ℝ^d`, with the
  operator norm in the seminorm. For $d = 1$ (Remarks 4.5, 5.4) $\mathbb R$ is identified with
  $\mathbb R^1$ through the coordinate.
* Sobolev spaces are defined from weak derivatives against smooth compactly supported test
  functions; $\|f\|_{W^{k,p}} = \sum_{|\alpha|\le k}\|D^\alpha f\|_{L^p}$ (any of the standard
  equivalent norms gives the same Theorem 2.6). The Bessel kernel is defined by Stein's
  subordination integral; the Fourier characterisation of Definition 2.4 is
  `besselKernel.fourier_eq`.
* **Theorem 2.1 / Lemma 2.2** quantify over every $Q$ that is a cube or a ball, as in the
  paper (`IsCubeOrBall`: open or closed Euclidean balls and open or closed axis-parallel cubes).
* **Theorem 2.1: Lebesgue-point hypotheses.** Both estimates additionally assume that $x, y$ are
  Lebesgue points of $f$ (`IsLebesguePoint`, the notion of [BH93, §1]), and the second estimate
  that $x$ is a Lebesgue point of every component of $\nabla f$. The paper cites the estimates
  as a special case of [BH93, Thm. 1]; there (and in [BH93, Thm. 2], the two-point form) $Q$ is
  an open cube, so the averages (4) over $B(x,r)$ eventually lie in $Q$. Our `IsCubeOrBall` also
  admits closed $Q$ with $x \in \partial Q$ — the case the paper uses in Theorem 5.1 (the ball with
  diameter $[\omega(t_i),\omega(t_{i+1})]$) — and there the estimate fails without the
  hypothesis: e.g. for $d = 2$, $Q = [0,1]^2$, $x = 0$, $f(z) = h(\arg z)\chi(|z|)$ with
  $h \ge 0$ smooth, $h = 0$ on $[0,\pi/2]$, one has $f \in W^{1,1}$,
  $\tilde f(0) = \bar h > 0 = \tilde f(\tfrac12,\tfrac12)$ while $\nabla f = 0$ on $Q$ (similarly for
  the second estimate with $d = 3$). At a Lebesgue point the averages over $Q \cap B(x,r)$ also
  converge to $\tilde f(x)$, which restores the argument; for the $C^2$ functions to which
  Theorem 5.1 applies it, every point is a Lebesgue point.
* **Theorem 2.1: second estimate (departure from the paper).** The paper's second estimate,
  $|\tilde f(y)-\tilde f(x)-\nabla\tilde f(x)(y-x)| \le C_d(I^2_Q(|\nabla^2 f|)(x)+I^2_Q(|\nabla^2 f|)(y))$
  with $I^k_Q(g)(x)=\int_Q g(z)|x-z|^{k-d}\,dz$, is false for $d \ge 2$ even for smooth $f$:
  for $d = 3$, $Q = B(0,1)$, $x = 0$, $y = (\tfrac12,0,0)$ and $f(z) = z_1\varphi(|z|/\varepsilon)$
  with $\varphi$ a smooth cutoff ($\varphi = 1$ near $0$, $\varphi = 0$ on $[1,\infty)$), the left
  side is $|0 - 0 - \tfrac12| = \tfrac12$ while $|\nabla^2 f| = O(\varepsilon^{-1})$ is supported in
  $B(0,\varepsilon)$, so the right side is $O(\varepsilon)$. We therefore state it as
  [BH93, Thm. 2] with $m = 2$, which has the extra term $\operatorname{diam} Q \cdot
  I^1_Q(|\nabla^2 f|)(x)$ (`Metric.ediam Q * ∫⁻ z in Q, ‖H z‖ₑ / edist x z ^ (d - 1)`), keeping the
  Lebesgue-point hypotheses above. The paper uses this estimate only in the proof of (18) in
  Theorem 5.1; that step is replaced by a direct proof for $C^2_b$ functions (see "Theorem 5.1:
  proof of (18)").
* **Theorem 5.1: proof of (18) (departure from the paper).** The paper obtains (18),
  $|[\nabla H(\omega),\omega]_\pi(t)| \le C_d \|\nabla^2 H\|_{W^0_{\omega,\pi}}$ for
  $H \in C^2_b \cap W^{2,1}$, by applying the second estimate of Theorem 2.1 to each increment;
  as stated that estimate is false (see above), and the per-increment bound
  $|(\nabla H(b)-\nabla H(a))\cdot(b-a)| \le C_d\int|\nabla^2H|\,\mathcal L^{n,i}_\omega$ fails in
  general. (18) itself holds and is proved directly (`Main/Eq18.lean`, `theorem_5_1.eq_18`):
  by (6) and uniform continuity of $\nabla^2 H$ near the compact set $\omega([0,T])$,
  $\nabla^2 H$ varies by at most $\varepsilon$ on each increment ball $Q^n_i$ for large $n$, so
  $|(\nabla H(b)-\nabla H(a))\cdot(b-a)| \le (|\nabla^2H(a)|+\varepsilon)|b-a|^2
  \le \int|\nabla^2H|\,\mathcal L^{n,i}_\omega + 2\varepsilon|b-a|^2$ using
  $\int\mathcal L^{n,i}_\omega = |b-a|^2$ and $\operatorname{supp}\mathcal L^{n,i}_\omega \subset Q^n_i$;
  summing, using finite quadratic variation and letting $\varepsilon \to 0$ gives (18) (with
  $C_d = 1$). The rest of the proof ((19)–(25)) follows the paper.
* **Theorem 2.6** states both the equality of spaces and the equivalence of the norms.
* **Quadratic variation** (eq. (5)): the limit exists for every $t \in [0,T]$ and
  $t \mapsto [x]_\pi(t)$ is continuous and increasing **on $[0,T]$** (`ContinuousOn`,
  `MonotoneOn`), as in the paper; the Stieltjes measure uses the constant extension
  `qvExt`. Covariation is obtained by polarization exactly as in Section 3.
* **Indexing.** Partitions $(\pi_n)_{n\ge1}$ and approximating sequences $(F_m)_{m\ge1}$ are
  Lean sequences on $\mathbb N$ whose entry at $0$ is unconstrained: Assumptions 1 and 2,
  eq. (31), the summability of Lemma A.1 and the conditions in eq. (8), Theorem 5.2 and
  Lemma B.2 are imposed for $n, m \ge 1$ only; limits along `atTop` ignore the $0$-th entry.
* **Corollary 3.2** carries hypothesis (6). This is not an addition: Section 3 states
  "in the sequel we will fix a sequence of partitions $\pi$ and assume that (6)", so (6) is a
  standing assumption of Proposition 3.1 and Corollary 3.2.
* **Section 4.2 seminorm helpers** (`occupationSeminorm.add_le`, estimates (10) and (11)) carry
  the paper's standing assumptions explicitly: `add_le` assumes `f, g` a.e.-strongly measurable
  (the seminorm is only applied to Hessians of Sobolev functions; for non-measurable integrands
  Lean's `∫⁻` is merely superadditive, and Bernstein-set indicators give a counterexample), and
  (10), (11) assume `ω` continuous on $[0,T]$ (Section 4.1 takes $\omega\in C[0,T]$; without it the
  oscillation `iSup` can vanish vacuously and (10) fails).
* **Canonical Wiener space.** $\Omega = C([0,T],\mathbb R^d)$ (Borel), $B$ the coordinate
  process, and $\mathbb P_x$ the law of $d$-dimensional Brownian motion from $x$
  (`CanonicalWienerSpace.P`, chosen by `Classical.epsilon` among the laws `IsLaw x`, i.e.
  images of $d$ independent Mathlib `IsBrownianReal` motions). Its existence
  (`exists_isLaw`) is **proved** from the vendored `BrownianMotion` construction
  (`brownian`, `gaussianLimit`) — this proof lives outside the Challenge closure because the
  Challenge must import Mathlib only. Polar sets (Definition 2.8) refer to times $t\in(0,T]$
  of this $\Omega$.
* **Itô integral (Proposition 5.3): custom, documented.** The vendored MathFin integral
  (`ItoIntegralCLM`, `localItoIntegral`, `predItoIntegral`) integrates scalar integrands
  against one real Brownian motion, adapted to *that* motion's natural filtration, and needs
  integrands that are bounded or have (a.s.) continuous paths. The paper's
  $\int_0^t\nabla F(B(s))\cdot dB(s)$ is a $d$-dimensional integral, adapted to the joint
  filtration of $B$, of an integrand $\nabla F(B)$ that for $F \in W^{1,2}_{loc}$ is only
  locally square integrable (not continuous). No vendored definition matches, so
  `IsItoIntegral` is our own: $I$ is the limit in probability of elementary predictable
  integrals $\int H_n\,dB$ with $\int_0^t|H_n - \nabla F(B)|^2 ds \to 0$ in probability (the
  standard $L^2_{loc}$ Itô integral, [KS91, §3.2.D], [RY99, IV.2]). The Brownian motion itself
  is Mathlib's `IsBrownianReal`.
* **Lemma B.2 typo.** The paper prints
  $\|h\|_{n,1,B} := \int_0^T \sum_i (|h(B(t_i))| + |h(B(t_{i+1}))|)(t_{i+1}-t_i)$. The
  integrand does not depend on the integration variable, so the literal reading is $T$ times
  the Riemann sum. We state `lemma_B_2` with the Riemann sum (the $p = 1$ case of
  $\|h\|_{n,p,\omega}$ of Section 4.2, which is how Appendix C uses it), and prove
  `lemma_B_2_literal` (the literal reading) from it; for $T > 0$ the two conclusions are
  equivalent, so the typo does not change the strength of the lemma.
* **Remark 4.4** is stated for $r \in (1,\infty]$ (weak-* for $r = \infty$, `WeakLpTendsto`):
  the density identity, the explicit seminorm and the inclusion. Its last paragraph ("does not
  in general characterise all of $\mathcal W^2_{\omega,\pi}$") is an informal comment and is
  not formalised.
* **Remark 4.5** ($d = 1$): the identity $L^{\pi_n}_\omega = \tfrac12(\lambda^{n,+}_T +
  \lambda^{n,-}_T)$ a.e. (with [DOS18]'s discrete local times as the paper describes them),
  the convergence/seminorm statement, the inclusion, the bounded local-time case
  ($\sup_n\|L^{\pi_n}_\omega\|_\infty<\infty$ and $\mathcal W^2_{\omega,\pi} = W^{2,1}(\mathbb R)$)
  and the comparison with DOS. Two readings are made explicit: $F$ is its continuous
  representative ("$W^{2,1}(\mathbb R)\subset C^1(\mathbb R)$"), and "whenever both pathwise
  constructions apply" is the hypothesis that the DOS formula holds with the same pathwise
  integral (eq. (16)).
* **Remark 5.4**: the $d = 1$ characterisation of $W^{1,2}_{loc}$, the non-implication, the
  sufficient condition $1 + s > d(1/p - 1/2)$ and the case $p \ge 2$ (proved from the
  sufficient condition). The comparison with the hypotheses of [FP00] is informal and not
  formalised.
* Section 3 defines the mesh as $\sup\{|t_{i+1}-t_i|, i = 1,\dots,m(n)-1\}$ (omitting the first
  interval), while Assumption 1 uses $\max_i$; we use $\max_i$ throughout (the Section 3 mesh
  is only used in the remark that $|\pi_n|\to 0$ implies (6)).

# Main statements (Lean)

# Literature

* [BH93]: B. Bojarski and P. Hajłasz, *Pointwise inequalities for Sobolev functions and some applications*, Studia Math. 106 (1993), 77–92, doi:10.4064/sm-106-1-77-92, <https://sites.pitt.edu/~hajlasz/OriginalPublications/BojarskiH-Pointwise-StudiaMath-106-1993-77-92.pdf>. Source of Theorem 2.1 / Lemma 2.2 (its Lemma 3) / Theorem 2.3 (its Theorem 3) and of the
  precise representative (its (1), (4)); followed for the proofs. Not redistributed here.
