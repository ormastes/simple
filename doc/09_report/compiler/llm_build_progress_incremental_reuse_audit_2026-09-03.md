# LLM Build Progress and Incremental Reuse Audit

**Date:** 2026-09-03
**Baseline:** `53c00707567feb7be9fdcbadba5cdd5fd74b6176`

## Finding

`log_build_progress` already carried durable `done`, `total`, `remaining`,
`failed`, and `cached` fields, but its always-visible stdout line omitted the
last three and the terminal state. An LLM or operator watching an ordinary
build log therefore could not distinguish compilation from cache reuse, tell
whether work remained, or identify a failed/complete phase without reading and
reconstructing a separate event file.

## Implemented Slice

- Emit one key/value stdout record containing phase state, unit kind, done,
  total, remaining, succeeded, cached, failed, task progress, elapsed time,
  delta time, and current unit.
- Add `succeeded` to the durable event record.
- Derive `succeeded = max(done - cached, 0)` and
  `remaining = max(total - done, 0)` with `-1` preserving unknown cardinality.
- Keep the existing flush-before-optional-file ordering.

## Measured Rationale

For the representative incremental state `done=90`, `total=100`, and
`cached=70`, the old stdout exposed only `90/100`; the new record exposes
`remaining=10`, `succeeded=20`, and `cached=70` directly. Inspection changes
from log-history reconstruction to one-line parsing.

The projection is bounded O(1): two integer subtractions, clamps, and no new
collection, scan, persistent index, or cache entry. It does not alter compile
selection, cache admission, object generation, or binary contents.

## Evidence

- `build_progress_summary_spec.spl`: 3 scenarios passed.
- `non_tty_build_progress_flush_contract_spec.spl`: preserves immediate
  stdout flush and optional durable append ordering.
- The optimizer command on the admitted runtime exited 133 without output;
  no optimizer claim is made.
