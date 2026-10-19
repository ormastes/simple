# A slow completed RSS observation cancels a separately memory-bounded build

Status: opt-in diagnostic control implemented; live bootstrap unchanged; real
kernel qualification pending. Compiler Phase 3/link/Hello World remain unverified.

## Evidence and scope

A prior bounded bootstrap ended with watchdog exit 89 after an approximately
55-second RSS observation. Telemetry improvement PR #3752 (merged as
`6f7dd86eceb`) retains first-failure phase and CPU/elapsed evidence; it does not
establish why that observation was delayed or remove its cost. The live later
source-439 producer uses enforced outer and inner watchdogs. Neither supports
runtime configuration reload; HUP is cancellation. No live process, source,
cache or existing cgroup limit was modified by this change.

The existing cgroup root-run layout caps only the worker leaf. Its outer
watchdog runs in the sibling supervisor leaf, so a worker-only proof cannot
justify waiving the outer watchdog's measurement latency failure.

## Selected control

Add explicit root-run `--bound-supervisor` to place the same configured maximum
on the new private common parent before any child starts, with parent group-OOM
enforcement and unchanged worker limit. The root provisioner stays outside and
retains post-cleanup parent OOM counters. A positive OOM-kill delta prevents a
zero leader exit from becoming success; the actual child wait result stays in
the JSON evidence.

Both future watchdog invocations may select
`--observation-failure-mode=diagnostic --independent-cgroup=PARENT`. The default
remains fail-closed. A waiver applies only to completed validated Linux samples,
after direct verification of the bounded root-controlled common ancestor and
member scope. Unreadable/malformed samples, modified helpers, session escape,
observed RSS breaches and timeouts retain failure behavior. Child nonzero and
signal results remain real. No fake zero RSS or complete measurement receipt is
introduced. Timing-waived ordinary completion is `diagnostic-incomplete` with
`measurement_budget_complete=0`; no phase PASS follows from it.

This is instrumentation control, not a fix to compiler logic or proof of the
performance regression's cause. Cache identities and failed-object resumption
are unchanged. No restart of an active build is needed to land the future
option, and no current check is claimed to have been disabled.

## Verification contract

The focused shell fixture covers production prelaunch refusal; real proof-policy
decisions with private filesystem stand-ins; real short child exit 0, exit 7 and
SIGSEGV; timeout, RSS breach, session escape, partial observation, proof mutation;
and truthful parent OOM result handling. Injection exists only in temporary
copies. No compiler/seed/native build is involved.

At initial handoff, privileged parent provisioning, actual kernel OOM and
end-to-end nested qualification were UNRUN. Later kernel evidence below
supersedes that initial status. Independent review must accept the exact diff
and fixture evidence before landing. No new unqualified option is silently
enabled in existing bootstrap wrappers.

The focused fixture ran once on 2026-10-19 in the isolated
`simple-watchdog-observation-diagnostics-20261019` worktree: all listed cases
PASS. The retained output is
`build/native_probe/watchdog-bounded-diagnostics-20261019/cycle1.log`.
`git diff --check` passed. These are instrumentation fixture results, not a
bootstrap or compiler verification PASS.

Independent review returned ACCEPT_STATIC with no P0/P1 findings after examining
the exact source, test and cycle-1 log. Reviewed executable SHA-256 values:

- Watchdog: `c25e18fe8312d0627506e7294cafe40c78103d005d3aa65f9f444c6f2ea57811`
- Cgroup helper: `166cf0888364a45a22b890146efa9ea5ac87999f95499c24589c83eda1467a64`
- Focused test: `6c3e7188b6f9b64e90bad3943272a97787a7fe7d4c137f6949f4314106d3910b`

The review does not waive the UNRUN kernel/nested qualification above.

## Kernel qualification and root interface correction

Root-owned kernel cycle 1 retained evidence under
`build/native_probe/bounded-kernel-97_pg_fg`: containment/cleanup PASS; the OOM
fixture failed to induce OOM (real child zero, OOM delta zero); nested UNRUN.
Those receipts were preserved. Cycle 2 used an allocation gate after leader-zero
reaping, private parent swap cap zero and actual bounded OOM-counter waiting.
Its evidence under `build/native_probe/bounded-kernel-qu8ayir6` records OOM PASS:
exit 137, real leader wait zero, parent OOM-kill delta two, hard maximum 64 MiB,
swap maximum zero, both leaves empty and parent removed.

Cycle 2 nested admission refused before payload with ENOENT reading
`/sys/fs/cgroup/cgroup.type`; this was a production validator bug, not a
permission failure. [Kernel cgroup-v2 documentation](https://github.com/torvalds/linux/blob/master/Documentation/admin-guide/cgroup-v2.rst)
defines that interface on non-root cgroups only. The validator now requires
domain type on the private parent and both leaves, preserving the real root
mount identity and protected root `cgroup.procs` migration boundary. No other
missing metadata is waived. The older proof fixture incorrectly invented a
root `cgroup.type` entry; that entry was removed.

The new targeted `process_tree_rss_cgroup_root_test.shs` ran once and PASSed
using real root metadata and private subtree stand-ins. It confirms no root
type read, all private domain checks and the actual mount/migration reads.
The original 13 passing fixture cases and passing kernel cases were not rerun.
Corrected watchdog SHA-256:
`84745e7c54097dd465eb290b0885c6d1dd825071a53ff939602ca1f07510b7e7`.
Final kernel cycle 3 is reserved for nested qualification only; it remains
UNRUN until root executes the separately reviewed packet. No fourth cycle is
authorized by this bounded investigation.

Independent review accepted the exact root-interface fix, focused regression,
and nested-only cycle-3 packet with no remaining P0/P1 findings. Packet SHA-256:
`318d6f3d32beb33be9761be3708fb0f660b68aca8c7019555804a0523892e04d`.
This is static acceptance; actual nested execution is still pending.
