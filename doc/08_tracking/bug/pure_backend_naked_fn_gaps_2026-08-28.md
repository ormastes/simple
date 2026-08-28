# Pure backend @naked gaps: alloca suppression + E-NAKED validation seed-only; ~{memory} default delta

**Filed:** 2026-08-28 (HAL impl A Opus verification, D1/D2)
**Status:** OPEN

## D1 — latent miscompile: pure backend @naked emits allocas
`E-NAKED-BODY`/`E-NAKED-CLOBBER` validation and alloca suppression exist only in
the Rust seed. The pure-Simple backend only stamps `naked noinline` and turns
`Ret` into `unreachable`; a pure-compiled `@naked` fn with any local still emits
allocas inside a `naked` define — invalid prologue-free code. Current specs
hand-build an empty body and do not cover this.

**Fix:** port the seed's E-NAKED-BODY/E-NAKED-CLOBBER checks and alloca
suppression to the pure backend; add a spec with a local in a @naked fn
(must error, not emit alloca). Record as a dual-run pair until parity.

## D2 — three-way `~{memory}` clobber-default delta
Seed impl A, seed impl B (landed), and the pure backend disagree on whether
`~{memory}` is implied for raw asm without explicit clobbers. Needs one
documented default + dual-run record.

Source: $SCRATCHPAD/hal/VERIFY_impl_A.md (commit 644292b2e6a).
