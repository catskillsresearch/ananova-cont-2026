# Provenance

This repository is a standalone Lean 4 / Mathlib formalization (in progress) of Anna
Ananova and Rama Cont, *A pathwise Ito formula for weakly differentiable functions*,
arXiv:2608.07365v2. It is not a wrapper around, or reimplementation of, an independent
formalization.

**Anna Ananova and Rama Cont did not participate in, review, or endorse this
formalization.** The Lean development is produced by Lars Warren Ericson with AI-agent
assistance under his direction and review. The source paper is cited as literature only and
is not licensed under this repository's Apache-2.0 terms (see `NOTICE`).

Not yet registered with Palomar. Packaging follows the Challenge / Solution /
`comparator.json` / `formalization.yaml` pattern.

## Original to this repository

All of `WeakPathwiseIto/` (definitions and theorem statements of the paper),
`WeakPathwiseItoComparator/`, the board data (`HOLES.md`, `holes-graph.json`,
`holes-edges.txt`), `WeakPathwiseIto.md`, and the documentation files were written for
this repository. No paper-specific content (statements, prose, holes, board data,
references) from other formalizations was copied.

## Borrowed unchanged (kept in `vendor/`)

| Path | Source | Commit |
|------|--------|--------|
| `vendor/brownian-motion/` | `catskillsresearch/xodarev2026` `vendor/brownian-motion` (pruned RemyDegenne/brownian-motion `497e5e2`), with one documented rename patch (below) | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` |
| `vendor/palomar-policy/`, `vendor/PALOMAR_POLICY_PIN` | `catskillsresearch/xodarev2026` `vendor/` (PalomarRegistry/PalomarPolicy `5bd35cddcfc940532bb5f55e399d68b49b0986a5`) | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` |

Details: `vendor/SOURCES`.

**Patch to `vendor/brownian-motion` (2026-11-27).** Like the existing pruning of the copy (items
removed, e.g. those with `sorry`), the copy carries one rename so that it can be
loaded together with the Carleson project: `ENNReal.one_le_toReal` (`p ≠ ⊤` form) is renamed
`ENNReal.one_le_toReal_of_ne_top` at its declaration `BrownianMotion/Auxiliary/ENNReal.lean:29`
and its two uses `BrownianMotion/Auxiliary/ENNReal.lean:35` and
`BrownianMotion/Auxiliary/Jensen.lean:47`. Carleson's
`Carleson/ToMathlib/RealInterpolation/InterpolatedExponents.lean:45` declares
`ENNReal.one_le_toReal` (`a < ⊤` form); Lean rejects two declarations with one name in one
environment. Nothing else in the copy changed; it is still an independent Lake package, so it
stays in `vendor/` rather than being moved into the main body.

**Carleson project** (`fpvandoorn/carleson` @ `f7487cc9da4d1e73f009dc0280cd5b958f3e2c78`,
Apache-2.0, F. van Doorn et al. and contributors) is a Lake git dependency, not copied:
`Sobolev/HardyLittlewood.lean` imports `Carleson.ToMathlib.HardyLittlewood` and uses
`globalMaximalFunction`, `laverage_le_globalMaximalFunction`, `hasStrongType_maximalFunction_one`,
`CMB_eq_of_one_lt_q`, `measurable_maximalFunction`.

formal-mathfin (an earlier xodarev2026 copy at `c47908e` was never imported and was removed on
2026-11-27) is vendored again, unchanged, as `vendor/formal-mathfin/` at upstream `9f1c0ab`
(import closure of `MathFin/Probability/Brownian/Ito`, 94 modules, Apache-2.0; see
`vendor/FROZEN.txt`), as the base for the Itô integral needed by Proposition 5.3.

### Where vendored and upstream code is used

| Use | Source | How |
|---|---|---|
| Brownian motion predicate in `CanonicalWienerSpace.IsLaw` | Mathlib `ProbabilityTheory.IsBrownianReal` (upstreamed from RemyDegenne/brownian-motion) | imported from Mathlib |
| Proof of `CanonicalWienerSpace.exists_isLaw` (`Bessel/WienerLawExists.lean`) | `vendor/brownian-motion`: `ProbabilityTheory.brownian`, `gaussianLimit`, `isBrownianReal_brownian`, `continuous_brownian`, `measurable_brownian` | imported unchanged by the library (`Solution.lean`); the Mathlib-only Challenge does not need it |
| Hardy–Littlewood maximal theorem (`Sobolev/HardyLittlewood.lean`) | Carleson project `Carleson/ToMathlib/HardyLittlewood.lean` @ `f7487cc` | imported unchanged (Lake dependency); our file only bridges the paper's `M_1` to `globalMaximalFunction` |
| Itô integral (planned, Proposition 5.3) | `vendor/formal-mathfin` @ `9f1c0ab`: one-dimensional L² Itô integral (`ItoIntegralCLM`), isometry, continuous modification, Itô formula | vendored unchanged (lean_lib `MathFin`); not yet imported. It is scalar (one Brownian motion); Proposition 5.3 needs a d-dimensional integral of an `L²_loc` integrand, to be built on it in the main body |

## Borrowed unchanged tooling (kept at the path the tooling requires)

These generic Palomar-check scripts resolve the project root as `$(dirname $0)/..`, so they
must live in `scripts/`; they are byte-for-byte copies of
`catskillsresearch/xodarev2026` `scripts/` at `0e1f1f3b0739fdf472511da2207599ab11085660`:
`check-lean-sources.py`, `check_module_name_clash.py`,
`compare_challenge_solution_strict.sh`, `compare_challenge_solution_types.sh`,
`StrictCompare.lean.in`. Also verbatim: `LICENSE` (Apache-2.0 text) and
`.github/workflows/build.yml` (from xodarev2026 at `0e1f1f3b0739fdf472511da2207599ab11085660`).

## Derived (modified) material, in the main body

| File | Derived from |
|------|--------------|
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` (structure; toolchain and Mathlib pin since moved to the Carleson project's, formal-mathfin dropped, Carleson added; renamed package) |
| `scripts/build_holes.py`, `holes.html`, `scripts/serve_holes.sh` | Board design of xodarev2026 `scripts/build_holes.py` / `holes.html` / `scripts/serve_holes.sh` at `0e1f1f3b0739fdf472511da2207599ab11085660` (same goal status rules, file formats and embed marker; code rewritten, no data copied). The subgoal axiom check (`scripts/axioms_check.py`, `holes-axioms.json`) is new in this project |
| `scripts/gen_challenge.py` | Technique of xodarev2026 `scripts/gen_challenge.py` at `0e1f1f3b0739fdf472511da2207599ab11085660` (verbatim flattening, per-module `auxLemmasExt` reset); code rewritten |
| `scripts/palomar_preflight.sh` | `catskillsresearch/palomar-preflight` `examples/project-wrapper.sh` at `cd89b1336ad1f189f44dd6facd2634ce8a9a4447`, and lyasoff2016 `scripts/palomar_preflight.sh` at `3376bd2b8c18cab4322ca5b1db46d7fc477eed1a` |
| `AGENTS.md`, `README.md`, `NOTICE`, `COMPARATOR.md`, `formalization.yaml`, `.gitignore` | Structure of the xodarev2026 files at `0e1f1f3b0739fdf472511da2207599ab11085660`; content rewritten for this paper |

## Literature followed for proofs

- B. Bojarski and P. Hajłasz, *Pointwise inequalities for Sobolev functions and some applications*, Studia Math. 106 (1993), 77–92, doi:10.4064/sm-106-1-77-92, <https://sites.pitt.edu/~hajlasz/OriginalPublications/BojarskiH-Pointwise-StudiaMath-106-1993-77-92.pdf> — Theorems 1–3 and Lemmas 2–3, followed for Theorem 2.1, Lemma 2.2 and Theorem 2.3 (cited by the paper as [BH93]). Kept locally at `sources/BojarskiHajlasz1993.pdf` (git-ignored, not redistributed).
