# Native V4 descendant retirement mechanism options

Status: awaiting user selection. No option is selected or implemented.
Baseline: origin/main `97020f7badf`; follows PR #1987 and gates #1995/#1997.
Effort estimates are engineering days including native and Pure Simple work,
focused adversarial fixtures, receipt/ACK changes, and review; they are not
delivery commitments.

## Scope decision required before mechanism selection

**All descendants:** every process created by the inspected tool must retire,
including descendants that call setsid/setpgid or change process groups. A
process-group signal cannot enforce this scope. If Stage 6A requires this,
options C and D below cannot satisfy its positive gate.

**Non-escaping process group:** only members remaining in the original owned
group are covered. This needs an explicit acceptance decision. The caller's
ProcessGroup request and packet tree-empty names alone do not establish that
escaped descendants are out of scope. Do not silently narrow the guarantee.

## Mechanism options

| Option | Pros | Cons and admission requirements | Effort |
|---|---|---|---|
| A. Linux cgroup v2 per request | Kernel populated=0 observes no live members independently of pipe closure and signal results; zombie leader can remain reserved; covers setsid/setpgid without loss of containment. | Requires exclusive pinned delegated containment, pre-exec placement, and prevented migration/escape. No current V4 authority handle exists. Same-credential writable paths are insufficient by themselves. Linux only; unavailable delegation must reject before execution. | 8–15 days |
| B. Dedicated supervisor with descendant ownership | Can isolate child adoption and lifecycle from unrelated runtime requests; an isolated supervisor could establish completion after all owned children are retired. | Must design and prove adoption/fork/escape coverage, preserve target's exact exec and wait4 evidence separately from supervisor identity, and add authenticated bounded IPC. Process-wide subreaper mutation is unsuitable. Cross-platform equivalents require separate providers; Linux subreaper alone does not provide portable containment. | 12–20 days |
| C. Cooperative non-escaping group contract | Smallest signaling surface; retains familiar POSIX process-group behavior. | Excludes escaping descendants and therefore cannot satisfy all-descendant retirement. Still needs a real admitted no-live-members mechanism; retained-leader kill(0), pipe EOF, kill success, and racing process scans are insufficient. This is a research option, not an implementable proof today. | 3–5 days investigation; implementation estimate depends on proof |
| D. Preserve fail-closed capability | Honest current behavior; no false tree proof or unsafe signal authority; #1995/#1997 remain reviewable staged work. | Positive Stage 6A pinned inspection remains blocked; does not complete native group retirement. | <1 day documentation |

Option A's kernel semantics are documented in the [cgroup v2 interfaces](https://cdn.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html).
Option B must account for the [Linux subreaper contract](https://man7.org/linux/man-pages/man2/PR_SET_CHILD_SUBREAPER.2const.html).

## Availability and fallback selection

For A or B, unsupported hosts or missing containment authority must return a
typed admission failure without spawning the target. A fallback is admissible
only if it independently provides the same selected scope and proof. Falling
back to LeaderOnly or treating group signaling as all-descendant retirement is
not an option. Supporting Linux first while rejecting other platforms is a
separate acceptable availability choice, not cross-platform proof.

## Acceptance shared by any implementation

Keep the target leader identity until retirement is independently observed;
signal only owned scope; retain bounded cleanup ownership through failure;
emit tree-empty time only from proof; preserve frozen replay and exact ACK.
Implement an executable Pure Simple V4 twin and run both against leader-first,
quiet closed-pipe descendants, TERM resistance, cancellation, deadlines,
ESRCH/EINTR, identity loss, unrelated groups, capture saturation, startup
failure, failed cleanup, wrong ACK, and valid ACK. Escaping descendants must
have explicit expected outcomes matching the selected scope.

No runtime tests have been run and no capability or Stage 6A PASS is claimed.
After user selection, delete unchosen options and write the final requirements.
