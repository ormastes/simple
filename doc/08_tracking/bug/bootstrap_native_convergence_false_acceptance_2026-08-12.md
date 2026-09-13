# Bootstrap native convergence accepted unequal compiler artifacts
**Status:** OPEN (unverified 2026-09-12)

**Filed/fixed:** 2026-08-12
**Severity:** critical — release/bootstrap authority

## Defect

`src/os/port/bootstrap_native_verify.spl` represented both byte equality and a
first-byte mismatch as `Ok(0)`. Its public verifier also returned `Ok(())` for
unequal files whenever selected ELF symbol-prefix counts matched. The duplicate
integration specs were environment-gated constant assertions and never invoked
the verifier.

## Fix and acceptance contract

Comparison now returns `NativeByteComparison.Equal`, `Mismatch(offset)`, or
`Error(message)`. Any unequal byte fails convergence; symbol counts are retained
only in the error diagnostic. Both integration-spec locations invoke the real
verifier over temporary retained blobs and cover identity, mismatch at byte
zero, mismatch later in the file, and unequal ELF-shaped inputs with equal
symbol counts.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.
