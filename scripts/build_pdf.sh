#!/usr/bin/env bash
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# WeakPathwiseIto.md (+ Lean statements of the main results) → WeakPathwiseIto.pdf via pandoc/xelatex.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
cp WeakPathwiseIto.md "$tmp/doc.md"
for f in Main/Theorem51 Main/Theorem52 Main/Proposition53; do
  { echo; echo "## \`WeakPathwiseIto/$f.lean\`"; echo; echo '```'; \
    sed -n '/^namespace WeakPathwiseIto/,/^end WeakPathwiseIto/p' "WeakPathwiseIto/$f.lean"; echo '```'; } >> "$tmp/doc.md"
done
pandoc "$tmp/doc.md" -o WeakPathwiseIto.pdf --pdf-engine=lualatex \
  -V geometry:margin=2.2cm -V mainfont="DejaVu Serif" -V monofont="DejaVu Sans Mono" -V fontsize=10pt -V "mainfontfallback=STIX Two Math:" -V "monofontfallback=STIX Two Math:" -V "monofontfallback=DejaVu Sans:"
echo "wrote WeakPathwiseIto.pdf"
