# Seed: a 1500-arm value `match` chain stalls (no output in 300 s)

**Date:** 2026-11-27
**Status:** OPEN, cause unknown (pre-existing; not fixed in the dict-index/match-join lane)
**Component:** Rust seed (`src/compiler_rust`), JIT/run path

## Symptom

A value-position `match` with ~1500 arms (`[]` arms, final arm `xs`) produces
no output within 300 s on BOTH seed `simple-local-20261127m.exe` and
`...127p.exe`. The same shape with 100 / 300 / 700 arms runs in ~160-220 ms,
so growth is not linear in that range: something goes superlinear (or loops)
between 700 and 1500 arms. Not caused by the weak-empty join change (seed m
stalls identically).

## Probes

`long*.spl` in the reviewer scratch dir
`C:\Users\yoon\AppData\Local\Temp\claude\07e8ec21a8a8dcf3\1357817b-c723-4b2e-821a-ee9cf4f2a43c\scratchpad\mt2\`.

## Suspects (unverified)

`lower_match_arms` (hir/lower/expr/control.rs) recurses once per arm and now
also walks the else chain in `hir_value_is_concrete` per level (quadratic in
arm count; but m, without that walk, stalls too, so the stall predates it).
Needs a profile before any fix.
