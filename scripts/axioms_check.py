#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Released under Apache-2.0 license as described in file LICENSE.
"""Axiom check for the holes board: which subgoals really depend on `sorry`.

Run after a successful `lake build`. For every subgoal that `scripts/build_holes.py` puts on the
board, this writes a `#print axioms` command into `.lake/axioms/Axioms.lean`, runs it with
`lake env lean`, and records the axioms Lean reports in `holes-axioms.json`:

    {"generated": ..., "axioms": {"Module::Name": ["propext", "sorryAx", ...], ...}}

`build_holes.py` then marks a subgoal done exactly when `sorryAx` is not among its axioms. A
subgoal Lean could not resolve is left out of the file, and the board falls back to the
module-import rule for it.

    python3 scripts/axioms_check.py
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_holes as bh  # noqa: E402

ROOT = bh.ROOT
OUT = ROOT / "holes-axioms.json"
LEAN_FILE = ROOT / ".lake" / "axioms" / "Axioms.lean"
# `'Foo.bar' depends on axioms: [a, b]` / `'Foo.bar' does not depend on any axioms`
DEP_RE = re.compile(r"^'(.+?)' depends on axioms: \[([^\]]*)\]", re.M)
NONE_RE = re.compile(r"^'(.+?)' does not depend on any axioms", re.M)


def subgoal_names():
    """(board id, fully qualified Lean name) for every subgoal on the board."""
    nodes, _, _ = bh.discover()
    out = []
    for sid, n in sorted(nodes.items()):
        if n["kind"] != "subgoal":
            continue
        name = sid.split("::", 1)[1]
        out.append((sid, f"{bh.LIB}.{name}"))
    return out


def main():
    subs = subgoal_names()
    LEAN_FILE.parent.mkdir(parents=True, exist_ok=True)
    lines = [f"import {bh.LIB}", ""]
    lines += [f"#print axioms {full}" for _, full in subs]
    LEAN_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    res = subprocess.run(["lake", "env", "lean", str(LEAN_FILE)], cwd=ROOT,
                         capture_output=True, text=True)
    text = res.stdout + res.stderr
    found: dict[str, list[str]] = {}
    for m in DEP_RE.finditer(text):
        found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in NONE_RE.finditer(text):
        found[m.group(1)] = []
    axioms = {sid: found[full] for sid, full in subs if full in found}
    missing = [sid for sid, full in subs if full not in found]
    OUT.write_text(json.dumps({
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "axioms": axioms,
    }, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    clean = sum(1 for a in axioms.values() if "sorryAx" not in a)
    print(f"axioms: {len(axioms)}/{len(subs)} subgoals checked, {clean} sorry-free, "
          f"{len(missing)} unresolved")
    for sid in missing:
        print(f"  unresolved: {sid}", file=sys.stderr)


if __name__ == "__main__":
    main()
