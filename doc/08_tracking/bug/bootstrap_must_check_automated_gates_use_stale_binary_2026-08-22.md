# Bootstrap must-check automated gates can use a stale binary

Status: RESOLVED — `codex/session-01a023a8`

## Failure

`check-bootstrap-must-pass.shs --record-bootstrap-success` verifies the exact
`--stage4-binary` and adjacent provenance, but `run_automated_gate` launches
every automated gate without exporting that binary as `SIMPLE_BINARY`.
Checkers therefore fall back to `bin/simple`, which may be stale, absent, or a
different compiler than the admitted Stage 4 candidate.

The isolated reproducer supplied a phase validator, an executable fake Stage 4
candidate, and a gate runner that required `SIMPLE_BINARY` to equal that exact
candidate. The current implementation returned 1 with:

`bootstrap-must-check: FAIL — one or more automated gates failed`

## Required fix

Bind every automated gate in record-bootstrap mode to the already validated
Stage 4 candidate. Preserve the existing self-test-only runner override and add
an adjacent regression proving a conflicting ambient `SIMPLE_BINARY` cannot
replace the candidate. The bootstrap runner remains the sole producer; the
lightweight push consumer remains read-only.

## Resolution

The recorder now canonicalizes the validated Stage 4 path only after all four
phase proofs pass and supplies it as both `SIMPLE_BINARY` and the established
`SIMPLE_BIN` compatibility variable to every automated gate. The focused
self-test sets conflicting ambient values and passed with the gate runner
observing the candidate path. Shell syntax and the focused contract both passed
on 2026-08-22. The existing engine-differential wrapper, which consumes
`SIMPLE_BIN`, is now an automated bootstrap row rather than an inert TODO.
