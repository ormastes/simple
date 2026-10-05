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

A separate real-Git host oracle passed both status and fullscan parity for
eligible-to-ineligible and reverse renames, eligible-to-vendor and reverse
renames, case-sensitive suffix selection, root-level source and dirty/deleted/
untracked files. It observed 12 eligible status paths and 10 fullscan paths.
Exact retained sets and the original full-source comparison are recorded in
`doc/09_report/workaround_git_selection_host_2026-10-05.json`. This host oracle
does not execute the Simple implementation and does not replace its native tests.

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

## Remaining full-source materialization cost (2026-10-05)

The source materializer is a separate orchestration cost from the Simple
workaround Git query. The root-owned `61e26` repair candidate required 496.7 s
to extract/authenticate 141,505 regular Git blobs despite only 18 selected
repair commits. The observation near alias creation was about 487 s elapsed
and 465 CPU seconds. The generic regression source `c6378ac0581` required
541.7 s on its successful preparation attempt for 141,913 regular blobs and
65 aliases; archive normalization restored 534 omitted paths and repaired
734 transformed files. These are preparation receipts, not compiler timings
or matched before/after benchmarks. The failed first c637 preparation and its
rename-related diagnosis are retained separately; none of its partial output
was admitted without subsequent full target authentication.

Evidence owners: `source-materialization-p2-repairs61e26` and
`source-materialization-generic-c637` beneath the Windows restart packet root.
The c637 ready receipt and `physical-git-blobs-final.tsv` identify its actual
accepted source. The scoped Git-query repair does not address this cost and
does not close TODO347.

### Incremental preparation proposal — not selected or implemented

An incremental materializer could consume an already authenticated immutable
base plus an exact `git diff-tree --no-renames` change set. Its target manifest
must still come from the complete target Git tree, including file mode and
alias semantics. Deleted and renamed-away base paths must be absent; changed
and added paths must be read from exact target blobs. Comparing final manifest
membership must reject missing, extra, case-colliding or escaping paths.

Skipping byte revalidation of unchanged paths requires a separately proven
immutable backing-store contract. A previous hash, unchanged mtime, unchanged
HEAD, or a content-addressed filename is insufficient. Shared mutable
hardlinks between running sources and a new candidate are prohibited.
An implementation may use independently writable copy-on-write files only
after proving isolation for the actual host/filesystem. Without that
capability it must retain copy-and-hash authentication, even if slower.
Authority publication occurs only after the complete target passes; no input
to a running compiler is patched and no existing authority is relabeled.

Required acceptance experiments before adoption:

- Exact target parity for additions, deletions, both sides of renames,
  executable-mode changes, aliases, case collisions and formerly omitted
  archive paths. An injected stale/extra base file must fail admission.
- Mutating either candidate must leave the base and other admitted candidates
  unchanged. Tampered base bytes/receipts, interrupted copying and crashed
  publishers must never produce an accepted partial authority.
- Concurrent consumers retain their original immutable generation. A second
  publisher cannot replace an admitted generation or reuse a stale lease.
- Alternate full and incremental preparations on identical target manifests;
  record elapsed/CPU time, bytes read/written, peak/retained process-tree RSS
  and integrity parity. Cold and warm results remain separate. A speedup
  without memory and correctness evidence is not acceptance.

This proposal requires a reviewed host capability and ownership design before
implementation. Existing full authentication remains the fallback and all
currently running source generations remain unchanged.
