# Windows source snapshot performance

Status: OPEN (P1)
TODO ID: 347

TODO: [compiler][P1] Reduce source snapshot admission and materialization cost while preserving dependency invalidation and immutable source identity; diagnose pseudo-snapshot startup and workaround Git 30-second timeout

Hello compiles one 65-byte module but its snapshot contains 16,357 files.
The measured cold Cranelift invocation-to-snapshot-publication interval is about
295 seconds; this timestamp interval includes surrounding work and is not an
exclusive snapshot CPU measurement. End-to-end compilation took 361.635 seconds.
LLVM reused the snapshot but took 141.597 seconds and still missed frontend and
HIR caches. The performance defect is open; its precise internal cost breakdown
and a completed fix are not established.

Evidence and the sub-0.1-second compilation target:
[latency bug](../bug/windows_hello_compile_latency_2026-10-05.md).
Research: [snapshot alternatives](../../01_research/domain/windows_source_snapshot_latency.md).

Acceptance:

- Attribute enumeration, hashing, copying, validation and publication costs with
  elapsed time, bytes, file counts and memory observations.
- Reduce work for unchanged snapshots and small dependency closures without
  stale hits after source, import-resolution, configuration or toolchain changes.
- Cover changed and deleted inputs, newly introduced import candidates, malformed
  caches, concurrent edits/publication, and interrupted operations with real tests.
- Check output correctness, peak and retained memory, and cold/warm performance
  for both backends; report whether the requested compilation target is met.
- Preserve live bootstrap sources and caches; do not restart the current run for
  this repair. Continue through Phase 4 and apply fixes in a later generation.

Owner: Astra performance lane, with parallel research and regression-test support.

## Scoped startup follow-up (2026-10-05)

This TODO also tracks the remaining pseudo/source-snapshot startup work; that
label does not authorize bypassing admitted inventory, immutable content hashes,
dependency selection, or parent/child source authority checks. The broad snapshot
redesign remains unselected. Existing SCV digest-reuse candidate `60a32d045e8`
is already in the `102acf` producer source and is not duplicated here.

New producer `0aec27aa6ea5f6877ad2aa4a020171ed095ab70ea433463c46633d0edbc5b29b`
completed cold and warm Hello compilation in 406.019 s / 115.180 s, with process
tree peak RSS 11,265,392 KiB / 9,732,868 KiB. Both emitted a workaround Git
30-second timeout. These are whole-build observations, not exclusive SCV timings
or proof of a regression against the older, differently configured producer.
Evidence: `qualification-102acf-cold-warm-hello20` under the Windows restart
packet root; a third occurrence is in `executable-batch20-p2102-sourcefix1`.

Source inspection found that `workaround_store.spl` requested whole-tree Git
status before discarding unsupported suffixes, vendored code and three bundled
runtime headers. The candidate applies that same selection as explicit Git
pathspecs to status and full reconciliation, retaining reader-side validation.
Git runs without optional index writes. Non-default global Git pathspec modes
retain the original unscoped query to prevent silent selection changes.
The existing 30-second/16-MiB process bounds, writer lock, HEAD recheck, linked
file rereads, source validation and atomic publication remain intact.

One read-only host experiment on the idle full `a1b1b200700` source returned
81.412 s / 83,838 output bytes for unscoped status, then 12.625 s / 13,530 bytes
for scoped status. Both contained exactly 279 eligible paths, with no missing
or additional paths. The ordered pair may benefit from filesystem warming;
it is diagnostic mechanism evidence, not a matched p50/p95 benchmark.
Peak/retained RSS was not measured for this pair. Native Simple regressions,
matched alternating performance/RSS qualification and the original startup
workload remain UNRUN. This TODO stays OPEN.

Regression coverage added to `bug_workaround_store_spec.spl` compares actual Git
discovery for repository-root source files, staged cross-suffix renames, deleted
files, untracked files, spaces/brackets, ignored files, vendor exclusions and
full-reconciliation membership. Existing corruption, lock, WAL and index-byte
preservation cases remain required. No source-snapshot identity shortcut or
successful native test execution is claimed.

`test/05_perf/app/bug/workaround_git_discovery_workload.spl` provides the native
paired workload. Each fresh process selects `baseline` or `scoped` through
`SIMPLE_WORKAROUND_PROFILE_MODE`, reads the same private fixture root from
`SIMPLE_WORKAROUND_PROFILE_ROOT`, and writes exact eligible membership to a
distinct `SIMPLE_WORKAROUND_PROFILE_PATHS` output. Both modes use the same
300-second diagnostic Git budget so the known >30-second baseline can finish;
this does not change production policy. The external owner must pin Git and the
compiled binary, alternate order, check each complete membership set and stable
fixture identity, and collect process-tree peak/retained RSS plus p50/p95 times.
No benchmark is accepted from timing/count output without these checks.
