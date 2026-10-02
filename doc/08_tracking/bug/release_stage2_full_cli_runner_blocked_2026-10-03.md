# Release Stage 2 full CLI and test runner remain blocked

**Date:** 2026-10-03
**Status:** OPEN
**Target:** `release/1.0`, AArch64 Linux, LLVM and Cranelift Stage 2 backends

## Observed result

Both backends produced admitted Stage 2 compiler binaries. Admission is only a
bootstrap compiler result: neither backend has a successful full CLI or native
test runner build, so there are no result-bearing compiler, interpreter, or
loader test receipts for these candidates.

| Backend | Admitted compiler SHA-256 | Full-tool result |
| --- | --- | --- |
| LLVM | `e7c2f7a824dcf7d3d57bebfae93ce2f6c2b48d937cf6526ef95aa4976800a73e` | CLI and runner each exit 88 at the enforced RSS cap; the CLI log also records HIR fatal groups. |
| Cranelift | `47d7ebd2131414898559d8c3bb7582b4b233dbfc5fb59900f1fb5be4a4013fc3` | The later full verifier exceeds the legal RSS cap before a test result. |

The legal process-tree RSS cap was **6,835,937 KiB**. The LLVM verifier
summary records CLI `FAIL`, status 88, GNU-time max RSS 6,845,832 KiB, and
runner `FAIL`, status 88, max RSS 6,844,840 KiB. Their containment records
report sampled peaks 6,843,592 KiB and 6,841,676 KiB, respectively, and
`rss-cap-exceeded`. The Cranelift final outer verifier reports
`rss-cap-exceeded`, exit 88, sampled peak 6,840,368 KiB at the same cap; it
stopped before a final full-tool summary. An earlier Cranelift CLI attempt used
a lower inherited cap of 5,859,375 KiB and exited 88 at GNU-time max RSS
5,949,420 KiB; this is not evidence that the legal-cap attempt passed.

The LLVM CLI log also contains independent HIR fatal examples:
`src/app/cli/_CliMain/main_and_help.spl` unresolved `cli_run_caret`, and
`src/lib/io_runtime.spl` unresolved `MemSnapshot`, `MemPhaseSnapshot`, and
`MemDiff`. These examples were captured from the candidate built before the
later release fixes. PRs #2249, #2274, and #2275 are already merged into
`release/1.0`; this record tracks the remaining full-tool and test evidence,
not a claim that those fixes were ineffective. A new candidate must be built
from the current release head to determine which HIR groups remain.

## Reproduction and evidence

Use an isolated checkout at the current `release/1.0` head. Build and admit
Stage 2 with `--backend=llvm` and `--backend=cranelift` separately, then run
`scripts/bootstrap/bootstrap-phase-verification.shs --phase=stage2
--strategy=full` against each exact admitted binary and its SHA-256. Set
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0` for in-process verification and keep the
enforced 6,835,937 KiB process-tree limit. Record the verifier `summary.env`,
containment `.rss.env`, tool build logs, published tool hashes, and each test
row. Do not substitute a bootstrap-only binary for the full CLI or runner.

Archived local evidence (scratch paths, not release artifacts):

- LLVM: `/dev/shm/simple-release10-llvm-fresh-20261003/output/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env` and `/dev/shm/simple-release10-llvm-fresh-20261003/output/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/` (`summary.env`, `logs/compiler_cli_build.log` with HIR diagnostics, `logs/test_runner_build.log`).
- Cranelift: `/dev/shm/simple-release10-cranelift-2249-20261003/output/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env`, `/dev/shm/simple-release10-cranelift-2249-20261003/output/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.max-rss-kib`, and `/dev/shm/simple-release10-cranelift-2249-20261003/full-verifier-cap-final.rss.env`.

## Acceptance criteria

1. For each backend, build a fresh Stage 2 candidate from the current release
   head and preserve its exact admission hash and immutable source snapshot.
2. Under the legal enforced RSS cap, publish a full CLI and native test runner
   from that candidate, with successful producer receipts and matching hashes.
3. Resolve any remaining HIR fatal groups on the current source; attach
   precise diagnostics if one still blocks publication.
4. Run compiler, interpreter, and loader suites through the published runner
   for **both** backends. Preserve actual `Results:` counts and test receipts;
   only then mark this bug resolved. A version check or Stage 2 sanity pass
   alone does not satisfy this criterion.
