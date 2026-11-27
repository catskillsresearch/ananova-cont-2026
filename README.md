[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/ananova-cont-2026/build.yml?label=Lean%204)](https://github.com/catskillsresearch/ananova-cont-2026/actions/workflows/build.yml)

# WeakPathwiseIto: a pathwise Itô formula for weakly differentiable functions in Lean 4

Formalization (in progress) of Anna Ananova and Rama Cont,
*A pathwise Ito formula for weakly differentiable functions*,
arXiv:2608.07365v2 (<https://arxiv.org/abs/2608.07365v2>).

Status: **blueprint**. Every paper definition is a Lean `def` / `structure`; every numbered
result is a Lean `theorem` with a `sorry` proof. See [`HOLES.md`](HOLES.md) and the live board
[`holes.html`](holes.html).

## Build

```bash
lake exe cache get   # optional, after lake update
lake build
```

Toolchain: Lean `v4.36.0-rc1` (see `lean-toolchain`), Mathlib pin in `lakefile.toml`
(the Carleson project's pin; see `vendor/SOURCES`).

## Layout

| Path | Content |
|------|---------|
| `sources/` | Source paper (PDF) |
| `WeakPathwiseIto/Basic/` | `ℝ^d`, partitions, `C^k_b`, Hessian, oscillation |
| `WeakPathwiseIto/Sobolev/` | §2.1: weak derivatives, `W^{k,p}`, `W^{2+s,p}`, precise representatives, maximal functions; Thm 2.1, Lemma 2.2, Thm 2.3 |
| `WeakPathwiseIto/Bessel/` | §2.2: Bessel kernel / space / capacity, Wiener space, polar sets; Thm 2.6, Thm 2.9 |
| `WeakPathwiseIto/Smooth/` | §3: quadratic variation along partitions, Föllmer integral, covariation; Prop 3.1, Cor 3.2 |
| `WeakPathwiseIto/Occupation/` | §4: discrete occupation densities, seminorm, `𝓦²_{ω,π}` (Def 4.3); Lemma 4.2, Remark 4.4 |
| `WeakPathwiseIto/Main/` | §5: weak pathwise integral and covariation, Assumptions 1–2, Itô integral; Thm 5.1, Thm 5.2, Prop 5.3 |
| `WeakPathwiseIto/Appendix/` | Lemma A.1, Lemma B.1, Lemma B.2 and the kernel estimates (32)–(35) |
| `WeakPathwiseItoComparator/` | Palomar Challenge (generated) and Solution |
| `vendor/` | brownian-motion (one documented rename), Palomar policy (see `vendor/SOURCES`); Carleson is a Lake git dependency |
| `scripts/` | Board, Challenge generator, Palomar checks |

## Conventions

* Each paper definition `XXX` is a `def` or `structure` in its own file `XXX.lean`; related
  items `XXX_YYY` (lemmas, auxiliary defs) are `YYY` inside `namespace XXX` in that file.
* Paper theorems, propositions, lemmas and corollaries are `theorem` / `lemma`
  declarations (never `axiom`), one file per numbered result (`Theorem51.lean`, …).

## Board

```bash
python3 scripts/axioms_check.py  # after lake build: #print axioms per subgoal -> holes-axioms.json
python3 scripts/build_holes.py   # refresh HOLES.md, holes-graph.json, holes-edges.txt, holes.html
scripts/serve_holes.sh           # http://127.0.0.1:8770/holes.html
```

## Writeup

[`WeakPathwiseIto.md`](WeakPathwiseIto.md) → [`WeakPathwiseIto.pdf`](WeakPathwiseIto.pdf)
(`bash scripts/build_pdf.sh`).

## Palomar packaging

| File | Role |
|------|------|
| [`WeakPathwiseItoComparator/Challenge.lean`](WeakPathwiseItoComparator/Challenge.lean) | statement of record: Mathlib + vendored `BrownianMotion` (`python3 scripts/gen_challenge.py`) |
| [`WeakPathwiseItoComparator/Solution.lean`](WeakPathwiseItoComparator/Solution.lean) | Imports the library |
| [`comparator.json`](comparator.json) | Compared theorems (Theorem 5.1, Theorem 5.2, Proposition 5.3) |
| [`formalization.yaml`](formalization.yaml) | Palomar project metadata |
| [`PROVENANCE.md`](PROVENANCE.md) | Provenance |

Not yet registered with Palomar.
