# Executable checker failed-only retry peak RSS — 2026-08-02
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## 2026-11-10 p2fix-interp lane (work/p2fix-interp-20261110, base d8c0a761988c)

Owner recovered. The exact retry driver is
`scripts/check/compiled-check-tree.py` (per
doc/09_report/stage4_failed_only_checker_retry_2026-08-02.md): resumable
batches over a native `simple-check` checker, `--workers 4 --batch-size 32
--timeout 120`, per-batch GNU-time metrics; the 40,646,272 KiB figure was the
OUTER /usr/bin/time on the 4-worker python orchestrator, not a per-checker
measurement (per-child per-batch max_rss_kb is recorded separately in the
batch .metrics). The retained retry.time artifact itself no longer exists in
any reachable build/ tree; the report doc + script source are the recovered
binding. Fix landed in the orchestrator: `--max-rss-kib N` (0=off, default
unchanged) samples the checker process TREE between wait slices and kills the
process group on exceed, marking the batch rss_ceiling_exceeded; every file
in such a batch is isolated per-file and classified `rss_ceiling`
(fail-closed, like timeout); per-file timeout and killpg isolation unchanged;
per-batch `rss_tree_peak_kib` recorded in batch-results.jsonl. Sampler is
Linux /proc-only and records `rss_sampler=unsupported` elsewhere — it never
claims enforcement where it cannot measure. `SIMPLE_CHECK_TIME_BIN` env
override added for hosts without /usr/bin/time. Extended
test/01_unit/scripts/compiled_check_tree_test.shs with a /proc-gated ceiling
phase (Linux CI; py_compile + function-level validation done on Windows).
Bounded measurement here: the recorded timeout input
src/lib/nogc_sync_mut/js/engine/interpreter_native.spl now FAILS CLOSED in
~1.5s under `simple check` (no admitted self-hosted check worker on this
host), seed peak RSS 216,004 KiB (PowerShell PeakWorkingSet64, deployed
release seed) vs the historical 228,528 KiB checker build. REMAINING:
workers 1/2/4 measured matrix with the native checker on a Linux build host
(the per-batch tree-peak fields now needed for it are recorded by the fixed
orchestrator); the timeout input's historical 120s behavior belongs to the
old native checker build and was not reproduced on current binaries.
