#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Released under Apache-2.0 license as described in file LICENSE.
"""Build the proof-hole board for the WeakPathwiseIto (Ananova–Cont 2026) formalization.

One node per `.lean` module under `WeakPathwiseIto/` (the root barrel `WeakPathwiseIto.lean` is
omitted). A hard edge `B -> A` means module `A` directly imports module `B`.

Subgoals. Every helper `theorem`/`lemma` (one whose docstring does not open with a bold paper
label such as `**Theorem 5.1**`) and every `def`/`structure` whose docstring opens with
`**Subgoal**` becomes its own node `Module::Name`, with a `subgoal` edge into the module that
declares it (the parent goal depends on it). Label a subgoal by opening its docstring with
`**Subgoal** (<paper item>)`; untagged helpers are still put on the board (labelled from their
module) and listed as warnings, so nothing a goal depends on is ever missing from the board.

Status rules for goals (modules):
  * done    = listed in VERIFIED, file has no `sorry`, and every direct import is done;
  * open    = not done, and every direct import is done (work on it next);
  * blocked = some direct import is not done.
Any `sorry` forces open/blocked regardless of VERIFIED.

Status rules for subgoals, from the axiom check (`scripts/axioms_check.py`, run after
`lake build`; it records `#print axioms` for every subgoal in `holes-axioms.json`):
  * done    = `sorryAx` is not among the subgoal's axioms (its proof uses no `sorry`, directly
              or through any lemma it cites);
  * open    = `sorryAx` is among its axioms and its own body contains `sorry`;
  * blocked = `sorryAx` is among its axioms only through lemmas it cites.
A subgoal missing from `holes-axioms.json` falls back to the goal rules above.

Outputs: HOLES.md, holes-graph.json, holes-edges.txt, and the JSON embedded into holes.html.

    python3 scripts/build_holes.py
"""
from __future__ import annotations

import json
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = "WeakPathwiseIto"
LEAN_ROOT = ROOT / LIB
OUT_JSON = ROOT / "holes-graph.json"
OUT_HTML = ROOT / "holes.html"
OUT_MD = ROOT / "HOLES.md"
OUT_EDGES = ROOT / "holes-edges.txt"
AXIOMS_JSON = ROOT / "holes-axioms.json"
HTML_EMBED_MARKER = "/*HOLES_GRAPH_JSON*/"

IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+)*import\s+" + LIB + r"\.([A-Za-z0-9_.]+)", re.M)
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|instance|class)\s+([^\s:({\[]+)", re.M)

# Short module ids (relative to WeakPathwiseIto/) that have been built, shaken and checked.
# See AGENTS.md: add an id only after a successful `lake build` of that module.
VERIFIED: set[str] = {
    "Sobolev.Theorem21First",
    "Sobolev.Theorem21Second",
    "Sobolev.Theorem21",
    "Sobolev.Theorem23Steps",
    "Sobolev.Theorem23",
    "Bessel.Young",
    "Bessel.BesselSpace",
    "Sobolev.HardyLittlewood",
    "Main.Theorem51",
    "Main.Theorem51Steps",
    "Main.SmoothItoAt",
    "Main.Eq18",
    "Sobolev.Lemma22",
    "Occupation.PathwiseSobolevSpace",
    "Occupation.OccupationSeminorm",
    "Smooth.Corollary32",
    "Smooth.FollmerItoFormula",
    "Smooth.Proposition31",
    "Occupation.Lemma42",
    "Occupation.DiscreteOccupationDensity",
    "Occupation.OccupationConstant",
    "Basic.Rd",
    "Basic.Partition",
    "Basic.ContDiffBounded",
    "Basic.SmoothHessian",
    "Sobolev.IsWeakDerivative",
    "Sobolev.MemW",
    "Sobolev.MemWLoc",
    "Sobolev.IsWeakGradient",
    "Sobolev.IsWeakHessian",
    "Sobolev.MemW2PlusS",
    "Sobolev.MemW2Plus",
    "Sobolev.PreciseRepresentative",
    "Sobolev.LocalMaximalFunction",
    "Sobolev.IsLebesguePoint",
    "Smooth.DiscreteQuadraticVariation",
    "Smooth.HasScalarQuadraticVariation",
    "Smooth.FollmerIntegral",
    "Smooth.PathwiseCovariation",
    "Occupation.IncrementBall",
    "Occupation.NormalizedQuadraticDensity",
    "Occupation.DiscreteSeminorm",
    "Occupation.ApproximatingSequence",
    "Main.WeakPathwiseIntegral",
    "Main.WeakCovariation",
    "Main.BalancedPartitions",
    "Main.IsItoIntegral",
    "Appendix.GaussianMoment",
    "Appendix.PotentialProfile",
    "Basic.IsCubeOrBall",
    "Basic.WeakLpTendsto",
    "Bessel.CanonicalWienerSpace",
    "Occupation.DiscreteLocalTime",
    "Basic.FunctionOscillation",
    "Smooth.PathOscillation",
    "Main.GeometricMeshDecay",
    "Smooth.HasQuadraticVariation",
    "Occupation.WeightedOccupationMeasure",
    "Appendix.HeatKernel",
    "Appendix.LemmaA1",
    "Bessel.WienerLawExists",
    "Bessel.BesselKernel",
}

# Paper labels for modules that carry a numbered result or definition.
PAPER_LABEL: dict[str, str] = {
    "Basic.Partition": "Section 3 (partitions)",
    "Basic.ContDiffBounded": "C^k_b",
    "Basic.FunctionOscillation": "Section 4 osc(φ,δ)",
    "Sobolev.IsWeakDerivative": "Section 2.1 weak derivative",
    "Sobolev.MemW": "Section 2.1 W^{k,p}",
    "Sobolev.MemWLoc": "W^{1,2}_loc",
    "Sobolev.MemW2PlusS": "Section 5.2 W^{2+s,p}",
    "Sobolev.MemW2Plus": "Section 2.1 W^{2+,p}",
    "Sobolev.PreciseRepresentative": "Eq. (3)",
    "Sobolev.LocalMaximalFunction": "Section 2.1 M_R f",
    "Sobolev.Theorem21": "Theorem 2.1",
    "Sobolev.Lemma22": "Lemma 2.2",
    "Sobolev.Theorem23": "Theorem 2.3",
    "Bessel.BesselKernel": "Definition 2.4",
    "Bessel.BesselSpace": "Definition 2.5",
    "Bessel.Theorem26": "Theorem 2.6",
    "Bessel.BesselCapacity": "Definition 2.7",
    "Bessel.CanonicalWienerSpace": "Section 2.2 Wiener space",
    "Bessel.IsBrownianPolar": "Definition 2.8",
    "Bessel.Theorem29": "Theorem 2.9",
    "Smooth.DiscreteQuadraticVariation": "Eq. (5) sums",
    "Smooth.HasScalarQuadraticVariation": "Eq. (5)",
    "Smooth.HasQuadraticVariation": "Section 3 Q^π(ℝ^d)",
    "Smooth.PathOscillation": "Eq. (6)",
    "Smooth.FollmerIntegral": "Corollary 3.2 integral",
    "Smooth.PathwiseCovariation": "Proposition 3.1 covariation",
    "Smooth.FollmerItoFormula": "[Föl81] Itô formula",
    "Smooth.Proposition31": "Proposition 3.1",
    "Smooth.Corollary32": "Corollary 3.2",
    "Occupation.OccupationConstant": "Eq. (7) c_d",
    "Occupation.IncrementBall": "Eq. (7) Q^n_i",
    "Occupation.DiscreteOccupationDensity": "Eq. (7)",
    "Occupation.WeightedOccupationMeasure": "Lemma 4.2 μ^T_ω",
    "Occupation.Lemma42": "Lemma 4.2",
    "Occupation.NormalizedQuadraticDensity": "Eq. (28)",
    "Occupation.DiscreteSeminorm": "Section 4.2 ‖h‖_{n,p,ω}",
    "Occupation.OccupationSeminorm": "Section 4.2 seminorm, (10), (11)",
    "Occupation.ApproximatingSequence": "Eq. (8)",
    "Occupation.PathwiseSobolevSpace": "Definition 4.3",
    "Occupation.Remark44": "Remark 4.4",
    "Main.WeakCovariation": "Eq. (15)",
    "Main.WeakPathwiseIntegral": "Eq. (16)",
    "Main.Theorem51": "Theorem 5.1",
    "Main.BalancedPartitions": "Assumption 1",
    "Main.GeometricMeshDecay": "Assumption 2, (30), (31)",
    "Main.Theorem52": "Theorem 5.2",
    "Sobolev.HardyLittlewood": "Hardy–Littlewood bound for M_1 (Appendix C; bridge to Carleson project)",
    "Main.IsItoIntegral": "Itô integral",
    "Main.Proposition53": "Proposition 5.3",
    "Appendix.GaussianMoment": "Lemma A.1 c_{q,d}",
    "Appendix.LemmaA1": "Lemma A.1",
    "Appendix.PotentialProfile": "Eq. (33)",
    "Appendix.HeatKernel": "Eqs. (32), (34), (35)",
    "Appendix.LemmaB1": "Lemma B.1",
    "Appendix.LemmaB2": "Lemma B.2",
    "Basic.IsCubeOrBall": "Section 2.1 cube or ball Q",
    "Basic.WeakLpTendsto": "Remarks 4.4/4.5 weak L^r convergence",
    "Bessel.WienerLawExists": "Section 2.2 ℙ_x exists (subgoals)",
    "Occupation.DiscreteLocalTime": "Remark 4.5 λ^{n,±}_T [DOS18]",
    "Occupation.Remark45": "Remark 4.5",
    "Main.Remark54": "Remark 5.4",
}

SECTIONS = {
    "Basic": "Preliminaries",
    "Sobolev": "§2.1 Sobolev spaces",
    "Bessel": "§2.2 Bessel potentials, capacity, polar sets",
    "Smooth": "§3 Smooth change of variable",
    "Occupation": "§4 Occupation measures and 𝓦²_{ω,π}",
    "Main": "§5 Main results",
    "Appendix": "Appendices A–B",
}

# Main results of the paper (shown highlighted; compared in comparator.json).
PAPER_GOALS = ["Main.Theorem51", "Main.Theorem52", "Main.Proposition53"]


def strip_lean_comments(text: str) -> str:
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def sorry_decls(code: str) -> list[str]:
    """Names of declarations whose body contains `sorry` (by position)."""
    decls = [(m.start(), m.group(2)) for m in DECL_RE.finditer(code)]
    names = []
    for m in SORRY_RE.finditer(code):
        owner = None
        for pos, name in decls:
            if pos <= m.start():
                owner = name
        if owner and owner not in names:
            names.append(owner)
    return names


PAPER_BOLD_RE = re.compile(r"^\*\*(Theorem|Lemma|Proposition|Corollary|Remark|Assumption|Definition|Eq)")
SUBGOAL_RE = re.compile(r"^\*\*Subgoal\*\*\s*(?:\(([^)]*)\))?")
DOC_DECL_RE = re.compile(
    r"(?:/--(?P<doc>(?:(?!-/).)*?)-/\s*)?(?:set_option[^\n]*\bin\s*\n\s*)?(?:open scoped[^\n]*\bin\s*\n\s*)?"
    r"(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure)\s+(?P<name>[^\s:({\[]+)", re.S)
NS_RE = re.compile(r"^(namespace|end)\s+([A-Za-z0-9_.']+)\s*$", re.M)


def declarations(raw: str):
    """(kind, full name, docstring, body) for each top-level declaration of a module."""
    ns_events = [(m.start(), m.group(1), m.group(2)) for m in NS_RE.finditer(raw)]
    found = list(DOC_DECL_RE.finditer(raw))
    out = []
    for k, m in enumerate(found):
        start = m.start("kind")
        end = found[k + 1].start() if k + 1 < len(found) else len(raw)
        stack = []
        for pos, ev, name in ns_events:
            if pos > start:
                break
            if ev == "namespace":
                stack.append(name)
            elif stack and stack[-1] == name:
                stack.pop()
        prefix = ".".join(x for x in stack if x != LIB)
        full = f"{prefix}.{m.group('name')}" if prefix else m.group("name")
        doc = " ".join((m.group("doc") or "").split())
        out.append((m.group("kind"), full, doc, strip_lean_comments(raw[start:end])))
    return out


def subgoals_of(mod: str, raw: str):
    subs = []
    for kind, name, doc, body in declarations(raw):
        tag = SUBGOAL_RE.match(doc)
        if kind in ("theorem", "lemma"):
            if PAPER_BOLD_RE.match(doc) and not tag:
                continue
        elif not tag:
            continue
        parent = (tag.group(1) if tag and tag.group(1) else None)
        subs.append({"name": name, "kind": kind, "parentLabel": parent, "tagged": bool(tag),
                     "sorryCount": len(SORRY_RE.findall(body)), "doc": doc})
    return subs


def discover():
    nodes, edges = {}, []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        mod = ".".join(path.relative_to(LEAN_ROOT).with_suffix("").parts)
        raw = path.read_text(encoding="utf-8")
        code = strip_lean_comments(raw)
        kinds = defaultdict(int)
        for m in DECL_RE.finditer(code):
            kinds[m.group(1)] += 1
        nodes[mod] = {
            "id": mod,
            "label": mod.split(".")[-1],
            "section": mod.split(".")[0],
            "sectionTitle": SECTIONS.get(mod.split(".")[0], mod.split(".")[0]),
            "paper": PAPER_LABEL.get(mod),
            "file": f"{LIB}/{path.relative_to(LEAN_ROOT).as_posix()}",
            "sorryCount": len(SORRY_RE.findall(code)),
            "holes": sorry_decls(code),
            "declKinds": dict(kinds),
            "paperGoal": mod in PAPER_GOALS,
            "verified": mod in VERIFIED,
        }
        for dep in IMPORT_RE.findall(raw):
            edges.append((dep, mod))
        nodes[mod]["subgoals"] = subgoals_of(mod, raw)
    edges = [(a, b) for a, b in edges if a in nodes and b in nodes]
    sub_edges = []
    for mod in list(nodes):
        n = nodes[mod]
        n["kind"] = "goal"
        for sg in n.pop("subgoals"):
            sid = f"{mod}::{sg['name']}"
            parent = sg["parentLabel"] or n["paper"] or mod
            nodes[sid] = {
                "id": sid, "label": sg["name"].split(".")[-1], "kind": "subgoal",
                "section": n["section"], "sectionTitle": n["sectionTitle"],
                "paper": f"subgoal of {parent}", "parentGoal": mod, "tagged": sg["tagged"],
                "file": n["file"], "sorryCount": sg["sorryCount"],
                "holes": [sg["name"]] if sg["sorryCount"] else [], "declKinds": {sg["kind"]: 1},
                "paperGoal": False, "verified": True, "doc": sg["doc"],
            }
            sub_edges.append((sid, mod))
            for a, b in edges:
                if b == mod:
                    sub_edges.append((a, sid))
    return nodes, sorted(set(edges)), sorted(set(sub_edges))


def transitive_reduction(nodes, edges):
    succ = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)

    def reach(src, skip):
        seen, stack = set(), [x for x in succ[src] if x != skip]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(succ[x])
        return seen

    return [(a, b) for a, b in edges if b not in reach(a, b)]


def build():
    nodes, edges, sub_edges = discover()
    edges = sorted(set(edges) | set(sub_edges))
    deps = defaultdict(set)
    for a, b in edges:
        deps[b].add(a)
    status: dict[str, str] = {}
    axioms: dict[str, list[str]] = {}
    if AXIOMS_JSON.exists():
        axioms = json.loads(AXIOMS_JSON.read_text(encoding="utf-8")).get("axioms", {})
    for m, n in nodes.items():
        if n["kind"] == "subgoal" and m in axioms:
            n["axioms"] = axioms[m]
            if "sorryAx" not in axioms[m]:
                status[m] = "done"
            else:
                status[m] = "open" if n["sorryCount"] else "blocked"

    def done(m, stack=()):
        if m in status:
            return status[m] == "done"
        ok = (nodes[m]["verified"] and nodes[m]["sorryCount"] == 0
              and all(done(d, stack + (m,)) for d in deps[m] if d not in stack))
        status[m] = "done" if ok else "?"
        return ok

    for m in nodes:
        done(m)
    for m in nodes:
        if status[m] == "?":
            status[m] = "open" if all(status[d] == "done" for d in deps[m]) else "blocked"
    for m, n in nodes.items():
        n["status"] = status[m]
        n["deps"] = sorted(deps[m])
        n["blockers"] = ([] if status[m] == "done" else
                         sorted(d for d in deps[m] if status[d] != "done"))
        if n["kind"] == "subgoal":
            n["detail"] = (("sorry: " if n["sorryCount"] else "proved: ") + n["id"].split("::")[1]
                           + f" — {n['paper']} (in {n['parentGoal']})"
                           + ("" if n["tagged"] else " [UNTAGGED: add **Subgoal** (…) to its docstring]")
                           + ("" if "axioms" not in n else
                              " · axioms: " + (", ".join(n["axioms"]) or "none")))
        elif n["sorryCount"]:
            n["detail"] = f"{n['sorryCount']} sorry: " + ", ".join(n["holes"])
        elif not n["verified"]:
            n["detail"] = "No sorry; not yet in VERIFIED (build + review, then add)."
        else:
            n["detail"] = "Verified (builds, no sorry)."
    red = transitive_reduction(nodes, edges)
    total = sum(n["sorryCount"] for n in nodes.values() if n["kind"] == "goal")
    counts = {s: sum(1 for n in nodes.values() if n["status"] == s) for s in ("open", "blocked", "done")}
    goal_counts = {s: sum(1 for n in nodes.values() if n["kind"] == "goal" and n["status"] == s)
                   for s in ("open", "blocked", "done")}
    sub_counts = {s: sum(1 for n in nodes.values() if n["kind"] == "subgoal" and n["status"] == s)
                  for s in ("open", "blocked", "done")}
    return {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "paper": "A. Ananova and R. Cont, A pathwise Ito formula for weakly differentiable "
                 "functions, arXiv:2608.07365v2",
        "sorryCount": total,
        "counts": counts,
        "goalCounts": goal_counts,
        "subgoalCounts": sub_counts,
        "untagged": sorted(n["id"] for n in nodes.values() if n["kind"] == "subgoal" and not n["tagged"]),
        "legend": {
            "open": "All imported modules done — prove / verify next",
            "blocked": "Waiting on unfinished imported modules (subgoals: proof cites a lemma "
                       "that still uses sorry)",
            "done": "Verified (goals: listed in VERIFIED, no sorry, deps done; subgoals: "
                    "sorryAx not among its #print axioms)",
        },
        "notes": [
            "Goals: one node per WeakPathwiseIto .lean module (root barrel omitted). Subgoals: one "
            "node per helper lemma/def (Module::Name), with a dashed outline and an edge into "
            "the goal that depends on it.",
            "Hard edge B→A: A directly imports B. Drawn edges are transitively reduced; "
            "goal status uses all direct imports.",
            "Subgoal status comes from the axiom check (scripts/axioms_check.py → "
            "holes-axioms.json): done exactly when sorryAx is not among its #print axioms.",
            "Paper goals: " + ", ".join(PAPER_GOALS) + ".",
            "Regenerate with: python3 scripts/axioms_check.py && python3 scripts/build_holes.py",
        ],
        "paperGoals": PAPER_GOALS,
        "nodes": [nodes[m] for m in sorted(nodes)],
        "edges": [{"from": a, "to": b, "kind": "subgoal" if "::" in a and b in nodes and "::" not in b
                   and nodes[a].get("parentGoal") == b else "hard"} for a, b in edges],
        "drawEdges": [{"from": a, "to": b} for a, b in red],
    }


def write_md(data):
    nodes = data["nodes"]
    c = data["counts"]
    L = [
        "# Proof holes (Ananova–Cont 2026 / WeakPathwiseIto)",
        "",
        "File-level inventory of Lean modules. A module is **done** only if it is listed in "
        "`VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file "
        "contains no `sorry`. A subgoal is **done** exactly when `sorryAx` is not among its "
        "`#print axioms` (recorded by `scripts/axioms_check.py` in `holes-axioms.json`); it is "
        "**open** if its own body has `sorry`, and **blocked** if it uses `sorry` only through "
        "lemmas it cites.",
        "",
        f"**Updated:** {data['updated']}  ",
        f"**`sorry` occurrences:** {data['sorryCount']} · {c['open']} open · {c['blocked']} blocked · "
        f"{c['done']} done (goals + subgoals) · goals {data['goalCounts']} · subgoals {data['subgoalCounts']} · "
        f"{sum(1 for n in nodes if n['sorryCount'] and n['kind'] == 'goal')} file(s) with `sorry`.",
        "",
        "**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).",
        "",
        "```bash",
        "python3 scripts/axioms_check.py  # after lake build: #print axioms per subgoal -> holes-axioms.json",
        "python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, holes-edges.txt, holes.html",
        "scripts/serve_holes.sh           # http://127.0.0.1:8770/holes.html",
        "```",
        "",
        "## Paper goals",
        "",
        "| Status | Module | Paper | `sorry` | Holes |",
        "|---|---|---|---|---|",
    ]
    by = {n["id"]: n for n in nodes}
    for g in data["paperGoals"]:
        n = by[g]
        L.append(f"| {n['status']} | `{g}` | {n['paper'] or ''} | {n['sorryCount']} | "
                 f"{', '.join('`'+h+'`' for h in n['holes'])} |")
    L += ["", "## Open now", ""]
    opens = [n for n in nodes if n["status"] == "open" and n["kind"] == "goal"]
    if opens:
        L += ["| Module | Paper | `sorry` | Holes |", "|---|---|---|---|"]
        for n in opens:
            L.append(f"| `{n['id']}` | {n['paper'] or ''} | {n['sorryCount']} | "
                     f"{', '.join('`'+h+'`' for h in n['holes']) or '(review → VERIFIED)'} |")
    else:
        L.append("_None._")
    L += ["", "## Subgoals (helper lemmas/defs)", "",
          "Each helper a goal depends on is its own board node `Module::Name`. Label it by opening "
          "its docstring with `**Subgoal** (<paper item>)`.", "",
          "| Status | Subgoal | Label | `sorry` |", "|---|---|---|---|"]
    for n in nodes:
        if n["kind"] == "subgoal":
            L.append(f"| {n['status']} | `{n['id']}` | {n['paper']}{'' if n['tagged'] else ' (untagged)'} | "
                     f"{n['sorryCount']} |")
    L += ["", "## All modules by section", ""]
    for sec, title in SECTIONS.items():
        mods = [n for n in nodes if n["section"] == sec and n["kind"] == "goal"]
        if not mods:
            continue
        L += [f"### {title}", "", "| Status | Module | Paper | `sorry` | Blocked by |", "|---|---|---|---|---|"]
        for n in mods:
            L.append(f"| {n['status']} | `{n['id']}` | {n['paper'] or ''} | {n['sorryCount']} | "
                     f"{', '.join('`'+b+'`' for b in n['blockers'])} |")
        L.append("")
    OUT_MD.write_text("\n".join(L) + "\n", encoding="utf-8")


def write_edges(data):
    L = ["# Direct import WeakPathwiseIto deps (for blocking / build order)"]
    L += [f"{e['from']} -hard-> {e['to']}" for e in data["edges"]]
    OUT_EDGES.write_text("\n".join(L) + "\n", encoding="utf-8")


def embed_html(data):
    if not OUT_HTML.exists():
        return
    html = OUT_HTML.read_text(encoding="utf-8")
    pat = re.compile(r"const EMBEDDED_HOLES_GRAPH = .*?; " + re.escape(HTML_EMBED_MARKER), re.S)
    blob = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    new = f"const EMBEDDED_HOLES_GRAPH = {blob}; {HTML_EMBED_MARKER}"
    html, k = pat.subn(lambda _m: new, html)
    if k != 1:
        raise SystemExit("holes.html: embed marker not found")
    OUT_HTML.write_text(html, encoding="utf-8")


def main():
    data = build()
    OUT_JSON.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    write_md(data)
    write_edges(data)
    embed_html(data)
    c = data["counts"]
    g = data["goalCounts"]; sc = data["subgoalCounts"]
    print(f"{sum(1 for n in data['nodes'] if n['kind'] == 'goal')} modules, "
          f"{sum(1 for n in data['nodes'] if n['kind'] == 'subgoal')} subgoals, {data['sorryCount']} sorry; "
          f"goals {g['open']} open / {g['blocked']} blocked / {g['done']} done; "
          f"subgoals {sc['open']} open / {sc['blocked']} blocked / {sc['done']} done")
    for u in data["untagged"]:
        print("warning: untagged subgoal", u)


if __name__ == "__main__":
    main()
