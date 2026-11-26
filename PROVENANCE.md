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
| `vendor/brownian-motion/` | `catskillsresearch/xodarev2026` `vendor/brownian-motion` (pruned RemyDegenne/brownian-motion `497e5e2`) | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` |
| `vendor/formal-mathfin/` | `catskillsresearch/xodarev2026` `vendor/formal-mathfin` (formal-applied-math/formal-mathfin `c47908e`) | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` |
| `vendor/palomar-policy/`, `vendor/PALOMAR_POLICY_PIN` | `catskillsresearch/xodarev2026` `vendor/` (PalomarRegistry/PalomarPolicy `5bd35cddcfc940532bb5f55e399d68b49b0986a5`) | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` |

Details: `vendor/SOURCES`.

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
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | xodarev2026 `0e1f1f3b0739fdf472511da2207599ab11085660` (same toolchain, Mathlib pin and vendored path deps; renamed package) |
| `scripts/build_holes.py`, `holes.html`, `scripts/serve_holes.sh` | Board design of xodarev2026 `scripts/build_holes.py` / `holes.html` / `scripts/serve_holes.sh` at `0e1f1f3b0739fdf472511da2207599ab11085660` (same status rules, file formats and embed marker; code rewritten, no data copied) |
| `scripts/gen_challenge.py` | Technique of xodarev2026 `scripts/gen_challenge.py` at `0e1f1f3b0739fdf472511da2207599ab11085660` (verbatim flattening, per-module `auxLemmasExt` reset); code rewritten |
| `scripts/palomar_preflight.sh` | `catskillsresearch/palomar-preflight` `examples/project-wrapper.sh` at `cd89b1336ad1f189f44dd6facd2634ce8a9a4447`, and lyasoff2016 `scripts/palomar_preflight.sh` at `3376bd2b8c18cab4322ca5b1db46d7fc477eed1a` |
| `AGENTS.md`, `README.md`, `NOTICE`, `COMPARATOR.md`, `formalization.yaml`, `.gitignore` | Structure of the xodarev2026 files at `0e1f1f3b0739fdf472511da2207599ab11085660`; content rewritten for this paper |
