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
- `formal-mathfin/`: compiled as this package's `lean_lib MathFin`
  (`srcDir = "vendor/formal-mathfin"`), same layout. Unchanged copy of the import closure of
  `MathFin/Probability/Brownian/Ito` (94 modules) from formal-applied-math/formal-mathfin
  `9f1c0ab` (Apache-2.0): the sorry-free one-dimensional Itô integral, isometry and Itô formula
  built on the same brownian-motion revision we vendor.
- `palomar-policy/` + `PALOMAR_POLICY_PIN`: the Palomar editorial policy snapshot
  (PalomarRegistry/PalomarPolicy), copied from `../xodarev2026/vendor/`.
