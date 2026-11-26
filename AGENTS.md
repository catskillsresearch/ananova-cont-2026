# Agent notes (ananova-cont-2026 / WeakPathwiseIto)

## Conventions (binding)

* Every paper definition is a Lean `def` or `structure` (never `axiom`, `opaque` or
  notation only), each in its **own** `.lean` file named after it.
* Related items `XXX_YYY` of a definition `XXX` (lemmas, auxiliary defs, instances) go in
  `XXX`'s file as `YYY` inside `namespace XXX` (referenced as `XXX.YYY`).
* Paper theorems / propositions / lemmas / corollaries are `theorem` or `lemma`
  declarations with proofs (`sorry` while open), never `axiom`. One file per numbered result.
* Reuse: code borrowed whole from another repository stays unchanged in `vendor/`; anything
  modified moves into the main body with its origin recorded in `PROVENANCE.md`.
* No paper-specific content from other formalizations (statements, prose, board data).

## After a successful `lake build` of a module

In the **same turn**:

1. **Shake** the file: drop unused `open` / `open scoped` / redundant imports; keep the
   minimal preamble that still builds cleanly (no new errors/warnings).
2. Re-run `lake build` on that module if the shake changed anything.
3. Add its short id to `VERIFIED` in `scripts/build_holes.py`.
4. Run `python3 scripts/build_holes.py`.
5. If the module is in the comparator closure, run `python3 scripts/gen_challenge.py`,
   `lake build`, and `bash scripts/compare_challenge_solution_types.sh`.

Do not mark verified on a failed or incomplete build.

## Holes board vs imports

One node per file under `WeakPathwiseIto/`, edges from **direct**
`import WeakPathwiseIto…` only (the root barrel `WeakPathwiseIto.lean` is not in the graph).
The HTML graph transitively reduces edges for layout; open/blocked status uses every direct
import. Keep a direct `import` for any dependency you want shown on the board.
