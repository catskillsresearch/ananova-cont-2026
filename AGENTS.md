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
4. Run `python3 scripts/axioms_check.py`, then `python3 scripts/build_holes.py`.
5. If the module is in the comparator closure, run `python3 scripts/gen_challenge.py`,
   `lake build`, and `bash scripts/compare_challenge_solution_types.sh`.

Do not mark verified on a failed or incomplete build.

## Subgoals (binding)

Any helper a goal depends on (a lemma or auxiliary def used in a proof or a statement) must be
labelled and on the board:

* name it clearly and open its docstring with `**Subgoal** (<paper item>)`, e.g.
  `/-- **Subgoal** (Lemma 4.2 trace measure): ... -/`;
* `scripts/build_holes.py` turns every helper `theorem`/`lemma` (docstring not opening with a
  bold paper label such as `**Theorem 5.1**`) and every `**Subgoal**`-tagged `def` into a node
  `Module::Name` with an edge into its parent goal; untagged helpers still appear and are
  printed as warnings — fix those before committing.

## Holes board vs imports

One node per file under `WeakPathwiseIto/`, edges from **direct**
`import WeakPathwiseIto…` only (the root barrel `WeakPathwiseIto.lean` is not in the graph).
The HTML graph transitively reduces edges for layout; a goal's open/blocked status uses every
direct import. Keep a direct `import` for any dependency you want shown on the board.

Subgoal status comes from the **axiom check**: after `lake build`, run
`python3 scripts/axioms_check.py`. It runs `#print axioms` on every subgoal (via
`lake env lean` on a generated file under `.lake/axioms/`) and writes `holes-axioms.json`.
A subgoal is **done** exactly when `sorryAx` is not among its axioms; **open** when it uses
`sorry` and its own body contains `sorry`; **blocked** when it uses `sorry` only through a lemma
it cites. Commit `holes-axioms.json` with the board files.
