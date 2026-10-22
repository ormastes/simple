# Session-escape check flags the campaign's own nested tool builds (cycles 28/29/30)

Date: 2026-10-13. Lane: release_phase3 campaign. Status: MECHANISM PARTIALLY
UNDERSTOOD; NO THIRD PATCH LANDED (evidence contradictory; see bottom).

## Failure

Cycles 28/29/30 (28/29 before, 30 after 208ac41704e) die ~10 min into the
stage2 compiler-test phase with status 90 `bootstrap-session-escaped`; the
campaign receipt records `unexpected_session_pids=<two pids>`. Cycle 30
receipt (verification/campaign.VnGgqt/process.env): session_mode=new,
root_pid=session_id=3725734, peak 6.39 GB, helper sha cb74021b... == current
tree's compiled helper (so the patched perl WAS live).

## What is established

1. The flagged pids are the two TOOL BUILDS' nested-session identities: both
   pids appear as `session_id=` in the cli/runner tool workers' nested
   `bootstrap-session-exec.admission.env` files (one per worker).
2. 208ac41704e added `sid_contract_authorized` to the two
   `%unexpected_sid` recording sites in process-tree-rss-watchdog.pl: admit a
   foreign-sid member whose /proc/<pid>/environ carries
   SIMPLE_BOOTSTRAP_SESSION_ID == its own sid. A 3-level replay (outer new ->
   inherit guard -> unset (418a3968f67 shape) -> nested new watchdog)
   PASSED: contract-carrying subtrees admitted, contractless setsid daemons
   still flagged (status 90), both pinned tests green.
3. LIVE PROBE of the exact real shape (run-process-group-timeout.shs with the
   contract unset around `$candidate native-build p2_add.spl`, the cycle-30
   watchdog perl): the nested session leader (pid == sid) had
   SIMPLE_BOOTSTRAP_SESSION_ID=<its sid> IN /proc/<pid>/environ. So the
   208ac41704e check should have admitted it -- yet cycle 30 flagged exactly
   those pids. CONTRADICTION unresolved.
4. A second foreign-session shape EXISTS inside a real build: a build-internal
   spawn (observed live: pid != sid, sid = a third session, NO contract var in
   the member's environ) -- some in-candidate spawn scrubs the contract and
   takes process_ops' `setsid -w` branch (src/lib/nogc_sync_mut/io/
   process_ops.spl sid_fn contract-absent path). Not yet attributed to a
   specific call site. 208ac41704e flags this shape (member and leader both
   lack the var).

## Why no third patch

The safe relaxations were evaluated against the pinned escape test
(test/01_unit/scripts/bootstrap_session_guard_test.shs: a child that setsid
and sleeps MUST be flagged and killed -- its environ carries a STALE contract,
so the stale/absent distinction and any ancestry rule that admits descendants
of contract-carrying ancestors both break it). A leader-environ fallback
(member unreadable/no-contract -> check /proc/<sid>/environ) was implemented
and verified safe (fixture escape: sid==pid, no fallback path, still flagged;
both tests green) but is UNPROVEN against the unexplained cycle-30 flagging
of contract-carrying leaders, so it was NOT committed (reverted; scratch copy
with the change: build/repro-stage2-fix/sescratch/process-tree-rss-watchdog.pl
-- note: scratch dir also holds replay scripts level0-2.sh + probe/audit.sh).

## Candidate next steps (cycle 31+)

- Reproduce the cycle-30 flag with the SEDBG-instrumented watchdog inside a
  REAL verifier-shaped run (not the simplified replay): add eprint of the
  flagged pid's environ presence + read errno inside sid_contract_authorized
  itself, run one tool build under a fake campaign session, read the truth
  from the trace.
- Identify the scrub call site (decode --internal-environment-variant-policy
  handoff chain in native_build_worker / parse_shard_main; check whether the
  worker exec rebuilds a canonical env that drops ad-hoc vars).
- Alternative architecture: drop 418a3968f67 session isolation and instead
  scope the per-build watchdog's members() to the leader's group in inherit
  mode (root cause of the ratchet never fully attributed either -- cycle-27
  mcp receipt peaked at cap+476 KiB with a 2.07 GiB own tree; the 8+ GiB
  co-member was never identified).

Evidence: cycle-30 receipt .simple/storage/build/bootstrap/stage2-compiler-tests/
aarch64-unknown-linux-gnu/verification/campaign.VnGgqt/{process.env,result.env};
tool-worker admission envs under verification/stage2-tool-workers/{cli,runner}/
tmp/simple-rss-session-*/; live-probe logs build/repro-stage2-fix/sescratch/live/.

## Addendum: architecture change (same day)

Campaign decision: abandoned the new-session isolation approach entirely
(418a3968f67 and 208ac41704e reverted in bfec2ec5d9c). Replacement: per-task
GROUP SCOPING in the inherit-mode watchdog -- run_task's stage2/3 native-build
branch exports SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP=1, run-process-group-timeout.shs
passes --scope-group=1, and members() then measures/kills only the leader's
process group (fork children share the group, so the whole build is covered).
The top-level campaign watchdog never sets the flag and keeps whole-tree
accounting + the session-escape check. Replay: 3 GiB same-session sibling +
scoped build under the real scripts -> BUILD-OK, per-task receipt
scope_group=1 peak_rss_kib=8504 (sibling excluded); campaign watchdog
unaffected. Caveat recorded: the cycle-27 ratchet's actual co-member was
never identified (the 2.07 GiB figure was the wrapper's per-process %M, not
the tree sum), so whether group-scoping alone prevents the 88s is an
empirical question for cycle 31.
