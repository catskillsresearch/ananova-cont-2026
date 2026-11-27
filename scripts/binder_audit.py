import re, pathlib, sys
B60 = ["∫⁻ ", "∫ ", "⨆ ", "⨅ ", "⨍⁻ ", "⨍ ", "⋃ ", "⋂ "]
B67 = ["∑ ", "∏ "]
OPEN, CLOSE = "([{⟨⟪", ")]}⟩⟫"
STOP = [":=", " ≤ ", " < ", " = ", " ≠ ", " ↔ ", " → ", " ∧ ", " ∨ ", " ≥ ", " > ", "∂", " | ", " ∈ ", " ⊆ ", "\n\n"]
KW = re.compile(r"^(theorem|lemma|def|abbrev|structure|instance|noncomputable def|private theorem|protected theorem)\b", re.M)
def chunks(text):
    starts = [m.start() for m in KW.finditer(text)] + [len(text)]
    for a, b in zip(starts, starts[1:]):
        c = text[a:b]
        kw = c.split()[0]
        if kw in ("theorem", "lemma", "private", "protected"):
            # signature up to first := at depth 0
            d = 0
            for i in range(len(c)):
                ch = c[i]
                if ch in OPEN: d += 1
                elif ch in CLOSE: d -= 1
                elif d == 0 and c.startswith(":=", i):
                    c = c[:i]; break
        else:
            c = re.split(r"\n/--|\n(?:end|namespace|section|variable|open) ", c)[0]
        yield a, c
def depths(c):
    """depth before each char; bars ‖ and | treated as brackets by heuristic."""
    d = 0; out = []; stack = []; lastbar = {}
    for i, ch in enumerate(c):
        if ch in "‖|":
            prev = c[i-1] if i else " "
            closing = False
            if stack and stack[-1] == ch:
                if prev == ch: closing = lastbar.get(ch) == "close"
                elif not prev.isspace() and prev not in "([{⟨,=<>≤≥+-*/•^:": closing = True
            if closing:
                d -= 1; stack.pop(); lastbar[ch] = "close"; out.append(d); continue
            if ch == "|" and c[i-1:i+2] == " | ": out.append(d); continue
            out.append(d); d += 1; stack.append(ch); lastbar[ch] = "open"; continue
        if ch in OPEN: out.append(d); d += 1; stack.append(ch); continue
        if ch in CLOSE:
            d -= 1; out.append(d)
            if stack: stack.pop()
            continue
        out.append(d)
    return out
def body_end(c, j, extra):
    D = depths(c); base = D[j]; i = j
    while i < len(c):
        d = D[i] - base
        if d < 0: return i, None
        if d == 0 and c[i] not in OPEN + "‖|":
            if c.startswith(", ", i) and not inbinder(c, j, i): return i, None
            for s in STOP + extra:
                if c.startswith(s, i): return i, s
        i += 1
    return i, None
def inbinder(c, j, i): return False
def binder_comma(c, k):
    d = 0
    for i in range(k, len(c)):
        ch = c[i]
        if ch in OPEN: d += 1
        elif ch in CLOSE: d -= 1
        elif d == 0 and c.startswith(", ", i): return i + 2
    return None
def toplevel_ops(s):
    D = depths(s); out = []
    for i in range(len(s)):
        if D[i] == 0 and s[i:i+3] in (" + ", " - "): out.append(i)
    return out
hits = []
files = sorted(pathlib.Path("WeakPathwiseIto").rglob("*.lean")) + [pathlib.Path("WeakPathwiseIto.lean")] + sorted(pathlib.Path("WeakPathwiseItoComparator").glob("*.lean"))
for f in files:
    text = f.read_text()
    for a, c in chunks(text):
        c = re.sub(r'\s+', ' ', c)
        for toks, kind in ((B60, 60), (B67, 67)):
            for t in toks:
                for m in re.finditer(re.escape(t), c):
                    k = m.start()
                    if t == "∫ " and c[k-1:k] == "⁻": continue
                    j = binder_comma(c, k + len(t))
                    if j is None: continue
                    # nested 'fun ... =>' inside body absorbs all; treat as body anyway
                    if kind == 60:
                        e, _ = body_end(c, j, [])
                        body = c[j:e]
                        # skip ops inside nested fun bodies: crude: cut at ' => '
                        ops = toplevel_ops(body)
                        if ops:
                            line = text[:a].count("\n") + 1
                            hits.append((str(f), line, kind, c[k:e].replace("\n", " ")[:220]))
                    else:
                        e, s = body_end(c, j, [" + ", " - "])
                        if s in (" + ", " - "):
                            line = text[:a].count("\n") + 1
                            hits.append((str(f), line, kind, c[k:min(len(c), e + 60)].replace("\n", " ")[:220]))
seen = set()
for h in hits:
    key = (h[0], h[1], h[3][:40])
    if key in seen: continue
    seen.add(key)
    print(f"{h[0]}:{h[1]} [{h[2]}] {re.sub(' +',' ',h[3])}")
