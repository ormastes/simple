# Multi-spec coverage output is overwritten by child processes

**Status:** OPEN (unverified 2026-09-12)

When `simple test` receives several spec files with one
`SIMPLE_COVERAGE_OUTPUT`, each child writes that same path. The final artifact
contains only the last spec rather than a union of decisions. A five-spec
Engine3D command therefore ended with the pipeline spec's 0/1 decision result
despite earlier font/drawing/geometry/texture execution.

Required fix: derive a collision-free artifact per child and merge only after
checking schema, source revision, runtime/backend identity, static denominator,
and duplicate decision consistency. Until then, multi-spec CSV output is not
admissible aggregate coverage evidence.

## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
