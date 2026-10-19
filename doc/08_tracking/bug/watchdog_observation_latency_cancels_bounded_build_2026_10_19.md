# A slow completed RSS observation cancels a separately memory-bounded build

Status: opt-in diagnostic control implemented and cumulatively kernel-qualified
in three bounded cycles. This evidence does not establish compiler Phase 3,
link or Hello World completion, or a fix for the LLVM performance hotspot.

## Evidence and scope

A prior bounded bootstrap ended with watchdog exit 89 after an approximately
55-second RSS observation. Telemetry improvement PR #3752 (merged as
`6f7dd86eceb`) retains first-failure phase and CPU/elapsed evidence; it does not
establish why that observation was delayed or remove its cost. At the incident,
the later source-439 producer used enforced outer and inner watchdogs. Neither supports
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

Initial independent review returned ACCEPT_STATIC with no P0/P1 findings after
examining the original source, test and fixture log. Historical SHA-256 values
below identify that first handoff; the corrected watchdog binding follows later:

- Watchdog: `c25e18fe8312d0627506e7294cafe40c78103d005d3aa65f9f444c6f2ea57811`
- Cgroup helper: `166cf0888364a45a22b890146efa9ea5ac87999f95499c24589c83eda1467a64`
- Focused test: `6c3e7188b6f9b64e90bad3943272a97787a7fe7d4c137f6949f4314106d3910b`

That initial static review did not waive kernel qualification; actual results
are recorded below, including the failed attempts.

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
Final kernel cycle 3 ran only the remaining nested qualification. No fourth
cycle is authorized by this bounded investigation.

Independent review accepted the exact root-interface fix, focused regression,
and nested-only cycle-3 packet with no remaining P0/P1 findings. Packet SHA-256:
`318d6f3d32beb33be9761be3708fb0f660b68aca8c7019555804a0523892e04d`.
The targeted regression SHA-256 accepted with that review is
`43ff4f26bfb038710b38d5d8b24f5c25d575f6cb5cbde0db984700a4c62e667c`.

## Final cumulative qualification and landing handoff

Root executed the exact accepted cycle-3 packet in session `69200`; the packet
terminated zero, indicating the expected child failure was preserved. Evidence
remains under the isolated worktree
`/home/yoon/dev/simple-watchdog-observation-diagnostics-20261019/`:

| Criterion | Retained evidence below that worktree | Result |
|---|---|---|
| Private parent/leaf containment and cleanup | `build/native_probe/bounded-kernel-97_pg_fg/containment/` | PASS, cycle 1, 64 MiB |
| Actual member OOM cannot conceal a zero leader result | `build/native_probe/bounded-kernel-qu8ayir6/oom-zero/` | PASS, cycle 2, wrapper 137, leader 0, parent OOM-kill delta 2 |
| Nested outer/inner latency diagnostics preserve child result | `build/native_probe/bounded-kernel-ng0tm4rp/nested/` | PASS, cycle 3, wrapper 7 and child 7 |

The final nested root receipt reports parent maximum 134,217,728 bytes (128 MiB),
OOM-kill delta zero, no cleanup errors, both leaves unpopulated and the parent
removed. Both watchdog receipts report `status=diagnostic-incomplete`,
`exit_status=7`, `measurement_budget_complete=0`, `observation_complete=1`,
`quiescent=1`, `rss_cap_enforced=1` and `independent_cgroup_checks=2`.
These are successful checks of honest diagnostic behavior: they do not turn
the deliberately late samples into complete measurement evidence or phase PASS.

The cgroup helper remained bound to SHA-256
`166cf0888364a45a22b890146efa9ea5ac87999f95499c24589c83eda1467a64`.
The final watchdog is the corrected `84745e7c...10b7e7` binding recorded above.
Each packet's `fixture-manifest.json` records its production pins, copied C
helper closure, exact private copies and intentional fixture changes. The OOM
case used a private allocation gate after the genuine leader-zero wait, a
private swap cap of zero and a bounded wait for actual kernel OOM; nested
watchdogs used private one-time 1.1-second sample delays. Those controlled
triggers are retained with the results, not hidden as production behavior.

No passing fixture/kernel case was replayed. The original OOM-induction failure
and root-interface refusal remain in their original evidence directories.
All three kernel criteria now cumulatively PASS; three cycles were consumed.
The default enforcement policy remains unchanged, and no active build was
retrofitted or claimed to have its watchdog disabled.

Root integrated the implementation as `cc80470e0dc` → `a523f78743f`, and the
root-interface correction as `aace889823e` → `ba82efa9749`. This documentation
handoff records qualification for those changes only. It neither publishes a
release nor enables the new mode in unrelated launchers.
