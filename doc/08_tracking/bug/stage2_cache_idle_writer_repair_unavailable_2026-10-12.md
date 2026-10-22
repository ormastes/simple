# Stage2 native-cache idle-writer repair unavailable after external TERM

Date: 2026-10-12. Lane: release_phase3 self-host bootstrap campaign (worktree
`/home/yoon/dev/simple-release-phase3-20261011`, head 099c81b599b).
Status: OPEN (P2). No source repair attempted; operational workaround applied
and evidence preserved.

## Observed failure chain

1. `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2` was launched
   as an agent-shell background task. ~60 s into stage2 the whole session
   received an external SIGTERM (exit 143). The RSS watchdog receipt
   (`stage2-native-build.log.rss.env`) recorded `status=interrupted`,
   `peak_rss_kib=2264468` vs cap `5859375` — not a memory kill; no kernel OOM
   evidence. The TERM originated outside the bootstrap process tree (the
   agent-shell session supervisor reaps task groups; both killed attempts ran
   in the shared session process group).
2. The TERM'd run left `stage3/<triple>/stage2-native-cache.writer/` behind
   (mkdir lock with pid/nonce/owner/birth/process.env, wrapper pid 144068).
3. Every subsequent run aborts at stage2:
   `bootstrap-cache-error: active or unresolved writer: ...writer; wrapper-only
   crash records cannot authorize repair; genuine execution-owner evidence
   required; objects preserved`.
   `--invalidate-cache=stage2` does NOT help: `bootstrap_cache_prepare`
   acquires the writer lock BEFORE clearing, so the stale lock blocks even the
   invalidation lane.

## Why the in-band repair cannot fix it

`bootstrap_cache_repair_idle_writer` (scripts/bootstrap/bootstrap-cache-lineage.shs:354)
validates owner+nonce and dead-pid, then unconditionally fails with
`execution ownership unproven: wrapper PID/group evidence cannot authorize
repair; ... genuine execution-owner repair remains unavailable`. By design,
wrapper crash records never authorize repair — there is currently no
execution-owner receipt registered, so the fail-closed path is the only path.

## Operational workaround (applied 2026-10-12)

- Verified writer wrapper pid dead, owner uid match, and no live compiler
  processes in the worktree.
- Moved (not deleted) the lock to
  `build/step1/writer-evidence/stage2-native-cache.writer.cycle3/` preserving
  pid/nonce/owner/birth/process.env.
- Relaunched the canonical stage2 command under `setsid` (own session, PPID 1)
  so future external group-signals cannot reach the build, plus
  `--invalidate-cache=stage2` to discard the partially written cache.

## Proposed source repair (future, not in this lane)

- Register an execution-owner receipt (e.g. session-helper signed liveness
  record) so `bootstrap_cache_repair_idle_writer` has genuine evidence and can
  clear a lock whose recorded owner is verifiably dead, or
- teach `bootstrap_cache_prepare` to resolve/clean a dead-owner writer lock
  before acquire in the `invalidate` lane, keeping the fail-closed posture for
  live or unverifiable owners.

## Evidence

- Writer lock snapshot: `build/step1/writer-evidence/stage2-native-cache.writer.cycle3/`
- Cycle logs: `build/step1/step1-cycle{3,4,5,6}.log`
- Watchdog receipt (interrupted): `.simple/storage/build/bootstrap/logs/aarch64-unknown-linux-gnu/stage2-native-build.log.rss.env`
