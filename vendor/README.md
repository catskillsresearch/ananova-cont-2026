# Vendored / pinned dependencies

Everything here is an **unchanged** copy (borrowed whole). Anything modified from another
repository lives in the main body of this repository instead, with its origin recorded in
`PROVENANCE.md`. Pins and upstream SHAs: `SOURCES`.

- `brownian-motion/`: **Lake path dependency** (`BrownianMotion`). Byte-for-byte copy of
  `../xodarev2026/vendor/brownian-motion` (itself lyasoff2016's pruned pin of
  RemyDegenne/brownian-motion). Import concrete modules only; do **not**
  `lake build BrownianMotion` as an umbrella.
- `formal-mathfin/`: **Lake path dependency** (`MathFin`). Byte-for-byte copy of
  `../xodarev2026/vendor/formal-mathfin` (Brownian motion, quadratic variation, Itô
  integral / Itô formula, Riemann–Stieltjes along partitions). Candidate infrastructure for
  the Brownian part (Lemma A.1, Proposition 5.3); not yet imported by `WeakPathwiseIto`.
- `palomar-policy/` + `PALOMAR_POLICY_PIN`: the Palomar editorial policy snapshot
  (PalomarRegistry/PalomarPolicy), copied from `../xodarev2026/vendor/`.
