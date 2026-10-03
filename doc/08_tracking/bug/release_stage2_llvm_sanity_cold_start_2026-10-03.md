# Release Stage 2 LLVM sanity cold start takes over 16 minutes

**Date:** 2026-10-03
**Status:** OPEN
**Source:** `release/1.0` at `4c8a20414ca8b0c3b2a105727dbd065825897f2d`
**Host/backend:** AArch64 Linux, LLVM 23, 20 native build jobs

## Observed result

The current-release Stage 2 bootstrap reached its first compiler sanity build
and published the `p2_add` artifact successfully. The sanity child log was
created at **06:57:51.430 +0900** and its bounded completion receipt was
written at **07:14:04.584 +0900**: about **16m 13s** wall time. The native
build's own progress log reports `elapsed_ms=55015` through successful link.
The difference is about **15m 18s** outside the reported native build phase
clocks. The child log contains two progress sequences, each starting at
`elapsed_ms=0`; it does not timestamp their boundaries or locate the gap.
The SCV `compile-events/refresh.lock` was created at
**06:57:52.866 +0900**, near the start of that interval. These timestamps
locate the delay; they do not establish which operation consumed it.

The bounded receipt says `status=complete`, `reason=child-exit`, and
`raw_status=0`; the native log says `[native-build] Artifact published`.
This is a performance bug, not a failed sanity result.

## Reproduction and evidence

From a clean checkout of the source above, run
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
--stop-after-stage2 --backend=llvm --jobs=20
--jobs-memory-policy=explicit-count --strategy=full --no-mcp`, with a fresh
output directory and frontend cache. The captured run used
`/dev/shm/simple-release10-llvm-current-20261003/output` for output; its
remaining environment is not fully retained here. Compare the creation time
of the first
`stage2-sanity.env.frontend-bootstrap-0.log`, the completion time of its
`.bounded.env` receipt, and the final `elapsed_ms` in the child log.

Evidence from this run (local scratch paths, not release artifacts):

- `/dev/shm/simple-release10-llvm-current-20261003/output/bootstrap-preflight.env`:
  records `git_head=4c8a20414ca8b0c3b2a105727dbd065825897f2d`.
- `/dev/shm/simple-release10-llvm-current-20261003/logs/bootstrap.log`:
  records the LLVM backend, full strategy, 20 jobs, and the transition to
  Stage 2 sanity.
- `/dev/shm/simple-release10-llvm-current-20261003/output/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.log`:
  file birth **06:57:51.430 +0900**; successful link at `elapsed_ms=55015`
  and artifact publication.
- The adjacent `.log.bounded.env`: file modification **07:14:04.584 +0900**,
  `raw_status=0`, and `log_sha256=4ca8cd7ba5b731e968493aa0bde46d2fe85b882c0f521f9b79ced67228971718`.
- `/home/yoon/dev/simple-release-stage2-current-20261003/build/scv/compile-events/refresh.lock`:
  file birth **06:57:52.866 +0900**.

## Expected result and impact

A one-file compiler sanity build should expose where its wall time is spent
across the whole child lifecycle. In this run, about 15 minutes have no
corresponding phase progress account, slowing LLVM test qualification.
Cranelift has not been measured for this specific gap.

## Resolution criteria

1. Timestamp the whole child lifecycle and both native build progress
   sequences on a fresh current-release candidate; attribute the unaccounted
   wall time without assuming where it occurs.
2. Remove or bound the responsible delay, then retain before/after timestamps
   and the successful bounded receipt for the same one-file sanity case.
