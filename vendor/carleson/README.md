# Carleson project (reference copy, not built)

Unchanged copy of `Carleson/ToMathlib/HardyLittlewood.lean` from the Carleson project
(formalization of a generalized Carleson's theorem; F. van Doorn et al. and contributors).

- upstream: https://github.com/fpvandoorn/carleson
- commit:   f7487cc9da4d1e73f009dc0280cd5b958f3e2c78 (2026-11-17)
- toolchain upstream: leanprover/lean4:v4.36.0-rc1, Mathlib 560d7e113c7d4233f9cf90db54ac04bb3fb0b4d6
- licence:  Apache-2.0 (`LICENSE` in this directory, copied unchanged)

This file is NOT compiled here: it imports 34 further Carleson modules (about 14.6k lines,
including the real interpolation theorem) and targets a newer Lean/Mathlib. The Vitali-type
covering lemmas `measure_biUnion_le_lintegral_aux` / `measure_biUnion_le_lintegral` were
adapted to our pin (Lebesgue measure on `ℝ^d`, doubling constant `2^d` in place of
`IsDoubling`, the auxiliary `def tr` inlined) in `WeakPathwiseIto/Sobolev/HardyLittlewood.lean`,
which carries a provenance header. The `L^p` bound is proved there by truncation and the
layer-cake formula instead of Carleson's real interpolation theorem.
