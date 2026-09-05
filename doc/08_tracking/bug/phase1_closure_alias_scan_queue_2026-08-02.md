# Phase 1 closure queue scans logical aliases as physical work

- **ID:** `phase1_closure_alias_scan_queue_2026-08-02`
- **Status:** FIXED — claimed and repaired by `pure_parser_close` on 2026-08-02
- **Severity:** High (bootstrap time/allocation amplification)

## Reproduction and baseline

The observed Phase 1 population contains 2,103 logical `SourceFile` entries for
1,422 physical files: 681 aliases. The closure loop iterates `all_sources` and
discovers an alias only after indexing it and constructing its physical key.
Thus it performs 2,103 queue iterations for 1,422 units of import-scan work.
The alias registry is semantically required; using it as the work queue is not.

## Intended invariant

Keep every logical alias in `all_sources`, but drive closure discovery from a
separate first-seen physical-source queue. Newly resolved aliases must enqueue
their physical file exactly once. Module registration and discovery order of
the first spelling remain unchanged.

## Measured result

For the reported corpus, queue iterations fall from 2,103 logical entries to
1,422 physical entries: **681 fewer iterations (32.38%)**. The 681 aliases are
still retained for module-name registration, so module semantics and Phase 2's
physical parse count are unchanged. This is a work-count measurement; it does
not claim that the separately reported ~1.7M retained objects fall by the same
percentage.

## Verification

- Optimizer analysis completed for the touched pure-Simple source.
- Exact closure-queue and adjacent bucket/dedup contract specs were updated.
- `bin/simple check src/compiler`: PASS with existing warnings.
- `git diff --check`: PASS.
