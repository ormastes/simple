# RC1 macOS Stage 2 positional frontend smoke times out

**Status:** Open. The RC1 Stage 2 compiler links, but bootstrap admission fails.
**Candidate source:** `141711525226a29e498262d37da1b92ada90c06b` on the stacked RC1 fixes.
**Platform:** `aarch64-apple-darwin`, LLVM 18, `--full-bootstrap --stop-after-stage2`.

## Retained evidence

The third bootstrap attempt built a Stage 2 binary (`3 compiled, 767 cached, 0 failed`) and reached compiler sanity. The prior Mach-O runtime-owner rejection did not recur. The sanity receipt reports `status=fail`, `frontend_smoke_status=1`, and `frontend_smoke_bootstrap_mode_status=0`; its candidate SHA-256 is `ba9d59ee142e44408ab2eb58d0f7b6a43325a8be1035b182cb8de61ed9e9da3c`. The preserved frontend log contains:

> candidate_frontend_smoke: candidate HUNG (timeout) native-building a two-line hello world with a positional entry

This is the first smoke pass (`SIMPLE_BOOTSTRAP=0`); the second pass was not reached. The admission helper deleted its probe directory, including `build.log`, so the timeout phase cannot be reconstructed from that run. The full frontend log is retained at `build/bootstrap/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log` in the isolated admission worktree.

Standalone invocations of the rejected binary against the same source revision did not reproduce the timeout: a mode-0 invocation returned an MC/DC budget configuration error, while a mode-1 invocation reached MIR and returned `E-SFFI-016: missing return in non-unit function 'main'`. Those invocations did not reproduce every inherited environment variable of the bootstrap wrapper and do not establish the timeout's cause.

## Next diagnostic boundary

Commit `4554484a116` makes the RC1 helper append at most the last 4,096 bytes of the positional build log to its failure output before deleting the probe directory. The outer sanity function now retains that output beside its receipt. On a later permitted admission run, compare the captured phase and exact inherited environment with a standalone reproduction; keep the timeout and clean failure distinct. The three full bootstrap verify/fix cycles for this session are exhausted, so this log-capture change has not received another full admission run.

Bootstrap remains unadmitted. Neither the linked binary nor the focused codec regression is evidence of a successful macOS bootstrap.

## 2026-09-27 follow-up: reproducible path-local timeout

The paragraph above describes the earlier `141711525226` attempt. Commit
`e982d794bdfa` subsequently passed the full Stage 2 trust-root admission, then
Stage 3 exposed a separate memory-snapshot text ABI defect. The ABI/provider
repair is committed as `c0bcb0ea25f` and shared in draft PR #1784.

On `c0bcb0ea25f`, Stage 2 first passed in a separate admission output with
candidate SHA-256 `f60c9a8f9cfd77143fd8c55638fb9d031c40b7eeff0897c27bd0e9d09886a572`.
The Stage 3 planner requires the output under the same source worktree, so the
cache was cloned into that worktree and Stage 2 was rerun there. Both path-local
runs failed the first frontend smoke's positional hello-world build at the fixed
60-second timeout. Their candidate SHA-256 was
`e77a84e147986e747d17bf112f488bd4c5a88b0ca625506681c6f7ca7110231c`.
The retained log stops at `native_compile 0/1` after roughly two seconds of
frontend work; the helper reports `candidate HUNG (timeout)`. The second run
occurred after concurrent Rust compiler processes had cleared. The evidence
does not yet distinguish a path-dependent compiler fault from a slow or hung
native compilation. The gate was not relaxed, and no Stage 3 admission was run
for this commit. The three-cycle verification cap is exhausted for this session.

Next investigation: retain the native compiler subprocess command and timing
for this exact positional fixture, then compare the two candidate binaries and
runtime authority paths before another admission session.

## 2026-09-28 diagnosis: native MIR traversal grows a range

A clean-environment positional build with the previously admitted Stage 2
compiler also timed out in the fix worktree at `native_compile 0/1`.
`sample` captured 2,103 main-thread samples under
`lower_mir_storage_project_fields_v1 -> rt_range -> rt_array_push_grow`;
physical footprint reached 3.4 GB. The sampled call site is the nested
function/block/instruction traversal, before any typed storage projection is
needed for the two-line fixture. The disassembly passes a tagged register value
as the `rt_range` end bound. This is evidence of an unbounded native loop,
rather than a slow external linker invocation.

The focused repair replaces the nested `for` traversal in that MIR lowering
owner with index loops bounded by each source collection's length. Keep the
original fail-closed behavior for logical projections without site bindings.
The current installed self-hosted test runner cannot parse the repository's
newer storage-layout source, so the required verification is a fresh Stage 2
candidate, its positional sanity fixture, and then Stage 3 admission.
