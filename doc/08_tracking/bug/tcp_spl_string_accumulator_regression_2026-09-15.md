# tcp.spl regained a whole-buffer string accumulator
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/io/stream_reader_append_shape_spec.spl
  (2 of 4 its fail)

## Observed
src/lib/nogc_sync_mut/io/tcp.spl:828 contains `buf = buf + chunk!` (and
:847 `out = out + chunk`), the exact whole-buffer rebuild pattern the spec
was written to keep out of the sync io readers. This looks like a
regression reintroduced on top of the append-shape refactor.

## Unblock condition
Replace the accumulator with the append-based reader shape, then re-run the
spec.

