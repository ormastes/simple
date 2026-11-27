# HIR shard timeout double-wait falsely blocks the ledger

**Status:** confirmed diagnosis; implementation pending the terminate-and-wait API design.

## Symptom

The Phase 2 full-CLI build in attempt 15 stopped during HIR. Its aggregate reported
`worker could not be reaped`, marked the active HIR owner `BLOCKED`, and refused
final worker/artifact publication. This did not identify a source module error.

## Exact attempt and first failure

- Attempt: `/tmp/simple-release-1.0.0-phase2-runner-attempt15-20261030`
- Source revision frozen by the attempt: `afbc6276617f2e99de01c4e3334c64c0c0894db1`
- Producer SHA-256: `2ec06bb53fd2c1c40dc975c6bd6e667e6ef8af9557af221d94d0c83439432266`
- Target/backend: `aarch64-unknown-linux-gnu` / Cranelift
- Hosted runtime library SHA-256: `51e785743bd63ab284acf0b377bf35ae7c47f6cb2920733908e12a2e2b45da2e`
- Evidence directory: `stage2-compiler-tests/aarch64-unknown-linux-gnu/verification`
- Effective native worker timeout: 1800 seconds (`summary.env:native_internal_timeout_seconds`); the campaign timeout was 7200 seconds and task timeout 3600 seconds.
- `compiler_cli_build.max-rss-kib`: 38,139,400 KiB. The process-tree receipt records a 38,954,764 KiB peak against a 50,331,648 KiB cap. OOM kills are recorded as zero; no PSI/swap evidence establishes memory pressure, so RSS alone is not treated as its cause.

The last completed progress record was HIR `done=2778 total=3026 remaining=248 succeeded=2778 cached=0 failed=0` at `elapsed_ms=1790739`, with `compiler.mir._MirLowering.declaration_default_bindings_v1` current. The next logged event began imports for `compiler.mir._MirLowering.declaration_default_rewrite_v1`; no completion for that module is recorded. The final ledger output was:

```text
[hir-shard] owner=0/1@0 status=BLOCKED exit=-2 claimed=2779 sealed=-1 finished=false
[hir-shard] inventory incomplete rows=-1 policy_fail_fast=false
[hir-shard] completed_workers=0 failed_workers=2 failed_modules=0 unfinished=-1
error: HIR aggregate failure; final worker and artifact publication blocked
```

The recorded `exit=-2` is the coordinator's worker timeout sentinel, not an
observed exit status from the child. The per-unit evidence reports zero failed
modules. The live owner exceeded the configured 1800-second deadline while the
queue continued to show HIR progress. The attempt log SHA-256 is
`90b0f06b8be28f938a7714f1568c16d8b495a5fa913d447e96c2ae9a1432e339`
(`verification/logs/compiler_cli_build.log`).

## Cause

`src/app/cli/native_build_main.spl` detects the HIR worker deadline, calls
`process_kill(pid)`, discards its result, then calls `process_wait(pid, 5000)`.
The attempt's hosted Rust runtime provider removes the child from its registry,
kills it, and waits for it inside `rt_process_kill`. A second wait therefore sees
an unknown handle and returns an error sentinel. The coordinator ignores the
kill result and requires this second wait to return an exit status before it can
prove the owner stopped. It therefore cannot establish reap proof, writes
`worker could not be reaped`, and globally blocks the queue. This is a fail-closed
result under an insufficient API contract, not evidence that the child remained
alive after successful termination.

This diagnosis is tied to the attempt's runtime provider and the code contract.
It does not establish that every provider's existing `process_kill` reaps its
child. Runtime implementations differ, so callers must not infer quiescence from
a generic kill boolean or from `process_is_running == false`.

## Preserved work and scope

The failure did not erase the completed HIR cache:

- The queue contains 2,778 terminal rows; every row is `PASS` with
  `CACHE_STORED`.
- The matching `.by-source` index contains 2,778 entries; all point to nonempty
  HIR blobs (2,778 blobs, 1,064,075,769 bytes in total).
- The queue marker is only `worker could not be reaped`; it does not erase those
  per-file cache entries. The cache count/index audit proves retention, not that
  every HIR blob is admissible for a later producer/source; normal identity,
  header, and dependency validation is still required before reuse.
- The active owner had claimed 2,779 rows. Its unfinished work was not sealed,
  so the remaining inventory is not proven complete.

No full-CLI retry or source edit was performed from this diagnosis. The prior `p2_add` output check used the same producer hash but a different
source revision and fixture scope; it is not evidence for this full-CLI
attempt's completion.

## Required correction

Add a separate owned-child termination operation with a completion receipt; do
not redefine the existing potentially nonblocking `process_kill` API. The
receipt must distinguish a proven quiescent/reaped owner from timeout and
uncertain ownership. A failed or unknown handle must remain fail-closed. A
successful cleanup still records the original worker timeout as a failure; it
must never turn that worker into a passing row.

Structured attempt evidence is recorded in
`doc/08_tracking/bug/hir_shard_timeout_double_wait_blocks_ledger_2026-10-30.sdn`.
See `doc/05_design/hir_worker_terminate_and_reap.md` for the proposed contract
and acceptance cases. No implementation or executable regression has yet been
run for this issue.
