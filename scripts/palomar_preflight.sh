#!/usr/bin/env bash
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Palomar preflight wrapper (derived from ../palomar-preflight/examples/project-wrapper.sh
# and ../lyasoff2016/scripts/palomar_preflight.sh). Runs the shared sibling toolkit
# ../palomar-preflight against this project.
#
#   bash scripts/palomar_preflight.sh --mechanical-only   # CI-style mechanical checks
#   bash scripts/palomar_preflight.sh                     # full, before Palomar submission
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$(dirname "$root")/palomar-preflight" \
    "$root/palomar-preflight"; do
    [[ -n "$d" && -f "$d/palomar_preflight.sh" ]] && {
      cd "$d" && pwd
      return 0
    }
  done
  echo "error: palomar-preflight not found; set PALOMAR_PREFLIGHT_ROOT or checkout toolkit" >&2
  return 1
}

# --- project-specific ---
PROJECT_SORRY_PATHS="WeakPathwiseIto WeakPathwiseItoComparator/Solution.lean"
PROJECT_FORBIDDEN_PREFIXES=()
# --- end project-specific ---

TOOLKIT="$(find_toolkit "$ROOT")"
args=(--project-root "$ROOT" --sorry-paths "$PROJECT_SORRY_PATHS")
for prefix in "${PROJECT_FORBIDDEN_PREFIXES[@]}"; do
  args+=(--forbidden-prefix "$prefix")
done
exec bash "$TOOLKIT/palomar_preflight.sh" "${args[@]}" "$@"
