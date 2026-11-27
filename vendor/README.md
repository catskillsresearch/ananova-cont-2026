# Vendored / pinned dependencies

Everything here is an **unchanged** copy (borrowed whole), except one documented rename in
`brownian-motion/` (see `SOURCES` and `PROVENANCE.md`). Anything modified from another
repository lives in the main body of this repository instead, with its origin recorded in
`PROVENANCE.md`. Pins and upstream SHAs: `SOURCES`; frozen revisions, copy dates and every in-tree edit: `FROZEN.txt`.

- `brownian-motion/`: compiled as this package's `lean_lib BrownianMotion`
  (`srcDir = "vendor/brownian-motion"`), not as a Lake path dependency, following the
  `catskillsresearch/scott_models` layout: Comparator's landrun sandbox may write only under
  `.lake/`, and a path package would write `vendor/brownian-motion/.lake`. Its own Lake
  requirement `kolmogorov_extension4` is a pinned root `require`. Copy of
  `../xodarev2026/vendor/brownian-motion` (itself lyasoff2016's pruned pin of
  RemyDegenne/brownian-motion). Import concrete modules only; do **not**
  `lake build BrownianMotion` as an umbrella.
- `palomar-policy/` + `PALOMAR_POLICY_PIN`: the Palomar editorial policy snapshot
  (PalomarRegistry/PalomarPolicy), copied from `../xodarev2026/vendor/`.
