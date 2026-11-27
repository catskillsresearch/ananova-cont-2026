# Vendored / pinned dependencies

Everything here is an **unchanged** copy (borrowed whole), except one documented rename in
`brownian-motion/` (see `SOURCES` and `PROVENANCE.md`). Anything modified from another
repository lives in the main body of this repository instead, with its origin recorded in
`PROVENANCE.md`. Pins and upstream SHAs: `SOURCES`.

- `brownian-motion/`: **Lake path dependency** (`BrownianMotion`). Copy of
  `../xodarev2026/vendor/brownian-motion` (itself lyasoff2016's pruned pin of
  RemyDegenne/brownian-motion). Import concrete modules only; do **not**
  `lake build BrownianMotion` as an umbrella.
- `palomar-policy/` + `PALOMAR_POLICY_PIN`: the Palomar editorial policy snapshot
  (PalomarRegistry/PalomarPolicy), copied from `../xodarev2026/vendor/`.
