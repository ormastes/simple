# Executable checker failed-only retry peak RSS — 2026-08-02

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Observation

A bounded four-worker retry of exactly 414 previously failing files reported a
maximum RSS of 40,646,272 KiB under `/usr/bin/time -v`. One input,
`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`, also reached the
120-second per-file timeout. The checker build itself used only 228,528 KiB.

## Risk

Even if the GNU time figure reflects the process-tree high-water mark rather
than simultaneous resident memory, this is too large for a routine diagnostic
retry and can destabilize shared build hosts.

## Required follow-up

Measure per-child and aggregate RSS on the timeout input and a representative
passing/failing sample at worker counts 1, 2, and 4. Determine whether memory is
retained parser/compiler state, dynload material, or concurrent process-tree
accounting. Add a production memory ceiling and preserve the per-file timeout
and process isolation while fixing the peak.

Evidence is recorded in
`build/mini_builds/stage4-failed-only-retry/retry.time` and the associated
durable per-file results.
