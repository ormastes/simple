# BuildRunner V4 group provider admission and population proof

Baseline: release/1.0.0 `9a8952b7211`. Date: 2026-10-28.

The native BuildRunner positive gate remains blocked. Darwin V4 reports
unavailable; Linux V4 accepts LeaderOnly and rejects ProcessGroup/Tree with
ENOTSUP before executable acquisition. The guard must remain in place.
No phase2 compiler was rebuilt for this investigation.

## Fixed population decoder defect

The separate Linux grouped broker accepted `populated 0junk`, `populated 00`,
and conflicting duplicate population lines as a tree-empty observation.
Its decoder now requires exactly one complete `populated 0` or `populated 1`
line. Embedded NULs, trailing spaces/tabs, incomplete lines, duplicates, invalid values and
missing population fields fail with EPROTO without modifying the output.
Unknown complete fields remain allowed for kernel interface extensibility.

The new fixtures reproduced the old decoder failure at `assert(!valid)`.
The fixed population fixture and the full V4 host selfcheck passed on native
Linux aarch64 in an isolated Docker container. The V4 fixture now verifies
that ProcessGroup/Tree rejection returns neither a PID nor a ticket, claims
no tree-empty time, and never acquires the executable pin. An initial x86
emulation run could not run the existing ptrace lifecycle checks; this is not
recorded as provider failure or positive evidence.

Reproduce on Linux with a C compiler and permitted ptrace:
`sh scripts/check/check-process-v4-group-admission.shs`.
The script bounds each executable with timeout and returns 77 on other hosts.
These C host checks are component evidence, not Pure Simple or SPipe admission.

## Why the existing broker cannot be promoted into V4

`runtime_linux_group_owner_impl.h` uses CLONE_INTO_CGROUP for atomic placement
and a pinned cgroup directory for population observations. These establish
initial placement and group observation, but not permanent containment.
The executed process retains the broker's credentials and access to the
cgroup filesystem. No credential boundary or equivalent mechanism prevents
migration. Closing inherited cgroup descriptors alone does not prevent the
process from opening a writable cgroup path. Thus population=0 can mean
escape rather than all descendants retiring.

Its original post-clone error path also ignored cgroup.kill failure, waited
only for the leader, ignored failed group removal, and closed ownership
descriptors. A failed start could therefore lose cleanup authority; an
unbounded waitpid could also hang. A Luna review independently confirmed
this cleanup gap. The population decoder change did not address it; the
following ownership follow-up removes that post-clone failure path.

The next provider needs an explicit exclusive containment authority: worker
credentials or another enforced boundary must deny cgroup migration, placing
the child before execution. It must retain a cleanup ticket through every
post-spawn failure and establish populated=0 before retiring ownership.
V4 also needs exact exec/wait4, bounded capture, frozen replay and exact ACK
integration, followed by escaping-descendant and failed-cleanup adversarial
fixtures. The existing mechanism options remain unselected; this change
neither narrows scope nor enables the broker as a V4 fallback.

## Start ownership follow-up (2026-10-28)

Baseline: release/1.0.0 `db3e7d235b7`. The fallible monotonic-clock read now
occurs before clone3. After successful clone3, the native start commits all
ownership handles and returns the lease without another admission failure.
No caller or start-receipt ABI change is needed: existing callers receive
the lease for every successful spawn. Linux's
[CLONE_PIDFD contract](https://man7.org/linux/man-pages/man2/clone.2.html)
allocates and stores the pidfd in parent memory as part of successful clone;
the old negative-pidfd branch and blocking best-effort reap are removed.

`sh scripts/check/check-linux-group-start-ownership.shs` compiles a focused
fault-injected C host fixture. Against the old owner, a failed clock reached
clone and blocking wait, failing the no-spawn assertion. Against the fix,
the clock failure returns EIO without launching or waiting. The fixture also
checks successful lease transfer, failed cancellation, collection while a
descendant remains, failed cgroup removal, retained ownership descriptors
and blocked parent release, followed by successful collection and descriptor
closure. Both red and green were observed on native Linux aarch64 in Docker.
Luna's independent source review found no P0/P1 issue.

The fake clone and filesystem boundaries qualify owner state transitions,
not live cgroup containment or Pure Simple/SPipe behavior. No Phase2 rebuild
or V4 capability change occurred. Migration prevention, V4 receipt/ACK
integration, and live escaping-descendant proof remain outstanding. Failures
before clone can still leave empty directory/output artifacts; broker exit
after a later cleanup failure still needs persistent ownership design.

## Pending cleanup retry follow-up (2026-10-28)

Baseline: release/1.0.0 `b9b6f3102e1`, including PR #5190's start ownership
prerequisite. A timeout latched `timed_out` before writing `cgroup.kill`.
If that write failed while the leader remained alive, subsequent polls skipped
the timeout branch and could return a normal running observation without ever
retrying cleanup. Explicit cancellation likewise retained its intent flag but
did not retry a failed write during subsequent polling.

The internal owner now tracks `kill_pending` separately from timeout and
cancellation intent. Every kill attempt sets it; only a successful write
clears it. Polling retries pending cleanup independently of the timeout latch.
Persistent write failures remain errors from both poll and collect, retaining
all ownership descriptors. Successful delivery is not tree-empty evidence:
collection still requires leader reap, population zero and group removal.
The public receipt layout and V4 capability/admission guards are unchanged.

The focused `check-linux-group-start-ownership.shs` fixture now covers timeout
and cancellation failure across three subsequent poll/collect attempts,
automatic recovery without resetting intent or sending another cancel,
nonterminal successful delivery, live leader and surviving descendant
collection refusal, final collection and descriptor closure. The regression
failed against the old owner at the repeated-error assertion, then passed
with the fix on native Linux aarch64 in an isolated Docker container. Evidence
is `/private/tmp/linux-group-cleanup-retry-20261028/` (`red.stderr`,
`green.stdout`, `green.status`). These were two verification cycles; no
Phase2 rebuild, live containment qualification or Pure Simple/SPipe admission
was attempted. Luna's independent exact-diff review found no P0/P1 blocker.

The clock-read-first polling order is preserved: a failed monotonic-clock
read returns EIO before retrying pending cleanup, retaining ownership and
pending intent. This can delay retry until the clock succeeds; it does not
claim successful cleanup. Permanent kill failure still requires an external
ownership/persistence design before broker exit can be safe. Credential
containment, V4 receipt/ACK integration and the actual BuildRunner Hello gate
remain open.


## Descendant cleanup before telemetry (2026-10-28)

Baseline: release/1.0.0 `8bae5a950dc`, after PR #5193. Polling previously
read and decoded memory.current and memory.peak before cancelling descendants
left after leader exit. A missing or malformed metric returned EIO before
cgroup.kill, leaving the group running even though the leader was reaped;
the leader timeout no longer applies once that flag is set.

Polling now sends descendant cancellation immediately after a valid populated
observation, before reading resource metrics. Metric errors still return EIO,
block collection, and retain ownership descriptors. No capability, completion,
or containment admission rule changed.

The native Linux aarch64 fault fixture reproduced the old failure at the
assertion that cgroup.kill contained `1`. The fixed owner passed all lifecycle
cases, including missing and malformed memory.current and memory.peak,
retained descriptors while collection fails, and successful collection after
metrics recover. Run `sh scripts/check/check-linux-group-start-ownership.shs`.
The population decoder and complete V4 lifecycle selfcheck also passed in
the native container, run from `/tmp` (the fixture rejects the container root
as its pinned working directory). Luna reviewed the exact source diff and
found no P0/P1 issue. This is native C
component evidence, not Pure Simple/SPipe or live descendant containment.
No Phase2 rebuild occurred. Local evidence is under
`/private/tmp/buildrunner-cleanup-telemetry-20261028`.

Review also noted a pre-existing observation consistency issue: a tree_empty
value from an earlier poll can persist in an error receipt after a later
population observation changes. Collection rejects the nonzero error before
retiring ownership; clearing stale completion fields remains separate work.

## Exact resource-control readback admission (2026-10-28)

Baseline: release/1.0.0 `8cec09d951a`, with PRs #5190, #5193 and #5194
merged. Grouped start previously accepted any memory.swap.max readback
beginning with `0` and any memory.oom.group readback beginning with `1`.
Thus `01` and `10`, malformed suffixes and overflowing values could pass
control admission before clone. Both readbacks now use the existing complete
nonnegative integer decoder and must equal the requested value, zero or one.
The unbounded-memory `max` readback path is unchanged.

The injected Linux start fixture covers twelve invalid readbacks: unequal
numeric values, junk suffixes, trailing spaces/tabs, extra lines and integer
overflow for each control. Every rejection occurs before clock/clone/wait,
leaves no active lease or stdout/stderr file, removes the new group directory,
and preserves the acquired delegation descriptors. Exact bare values reach
the intentionally failing clock; newline terminated values admit a successful
start and complete the existing retained-ownership/collection cases.

The old code failed the new rejection assertion; the fixed owner passed
`sh scripts/check/check-linux-group-start-ownership.shs` on native Linux
aarch64 in Docker. Adjacent population decoding and the complete V4 host
selfcheck also passed via `sh scripts/check/check-process-v4-group-admission.shs`.
Local logs are `/private/tmp/buildrunner-readback-{red,green,adjacent}.log`.
Luna reviewed the final diff and found no P0/P1 or remaining coverage issue
for this narrow admission fix. The pre-existing compound failure branch can
still report stale errno for a malformed value; this does not admit execution.

These checks provide injected C host component evidence only. They do not
qualify live cgroup containment, Pure Simple/SPipe or BuildRunner Hello.
V4 group rejection remains enabled and no Phase2 compiler was rebuilt.

## Darwin evidence must not report an unexecuted Linux check as passing

Baseline: release/1.0.0 `5df8d08425a`. The C V4 lifecycle selfcheck's
non-Linux entrypoint returned zero without executing any assertions. On native
Darwin arm64, the original file compiled and returned zero. It now prints
`process-observation-v4: requires Linux (not a PASS)` and returns 77. The
existing `check-process-v4-group-admission.shs` already rejects non-Linux hosts
with 77 before compiling; its Linux invocation and Linux fixture are unchanged.
The `config/check/must_check_gates.sdn` bootstrap gate invokes that wrapper.
Its shared runner currently records 77 as failure, which is conservative and
predates this change; it does not report unsupported hosts as passing. No
second direct caller was found in repository source/configuration references.

Native Darwin verification compiled the changed file with
`cc -std=c11 -Wall -Wextra -Werror`; both direct execution and the existing
wrapper returned 77. Evidence is under
`/private/tmp/buildrunner-darwin-admission-20261028/`. This validates the
unsupported result, not a process provider. Linux regression execution belongs
on the Linux host; no Docker or Phase2 rebuild was used in this follow-up.
The complete Linux branch is byte-identical to the baseline. A separate
temporary native C harness linked the current Darwin unavailable stubs and
checked unavailable capabilities, rejected start/poll/cancel/collect/ACK,
empty payload/binding and absent PID/ticket/tree-empty time. That harness
passed within a ten-second deadline; it does not exercise any child process.
Luna reviewed the exact source/documentation diff and found no P0/P1 issue.

The earlier immutable native capability probe remains
`/private/tmp/buildrunner-native-20261028/capability03/buildrunner`, SHA256
`99b8c4a6707b817bbb35d53a19d1936f201ad7b10953fe4e695eea686d826209`.
Its recorded result is `version=4 fields=8 available=0 capability_bits=0
error=45`, exit 78. It is a capability probe, not the complete BuildRunner.
The portable-core extraction and interpreter attempts there did not qualify
native BuildRunner execution and must not be promoted into Hello evidence.

The remaining Darwin implementation has two distinct ownership boundaries:

1. `process_port.spl`'s portable worker launcher calls `process_spawn_async`
   and does not consume its `digest` or `directory` arguments. A Darwin worker
   adapter must bind the admitted worker executable and working directory,
   retain ownership through launch/observation/cancellation failures, and prove
   worker retirement before slot reuse. A raw PID is not that proof.
2. `worker.spl` requires V4 ProcessGroup for the compiler. Apple's native clang
   in this investigation defines `__APPLE__` and `__MACH__`, but not
   `__unix__`; `runtime_process_owned.c` therefore selects its unavailable
   stubs. Widening that preprocessor guard cannot qualify an owner: the current
   exact start uses Linux-only process facilities and rejects grouped policy.
   A Darwin provider needs an enforced descendant boundary, exact execution
   identity, bounded output/deadlines, retained cleanup ownership, terminal
   proof and frozen-result/ACK integration before capabilities can be enabled.

Resume the existing Hello objective only after both boundaries have native
adversarial evidence: executable replacement, launch failure after child
creation, descendant escape attempts, leader exit with surviving descendants,
failed cancellation, owner interruption and duplicate/stale ACK. Then build
only the reachable manager/worker closure using the existing pinned Phase2,
stage the real Hello task from the preserved fixture, admit its task and
process receipts, verify the published executable digest, and execute it for
exact `Hello, World!` plus LF. Direct compiler output or a process-group signal
alone cannot satisfy this gate. Darwin Hello remains open; V4 is unchanged.


## Darwin worker descriptor ownership prerequisite (2026-10-28)

Baseline: release/1.0.0 `4fe34ee9f67`. The portable worker launcher reaches
`rt_process_spawn_async`; both Darwin runtime lanes called `posix_spawnp`
without file actions or attributes. Consequently a worker inherited open
non-CLOEXEC files, pipe endpoints and sockets owned by its parent. This can
retain parent resources after the parent closes them and expose unintended
handles to the worker.

Both lanes now share a Darwin helper using `POSIX_SPAWN_CLOEXEC_DEFAULT` and
explicitly inherit only open standard descriptors without `FD_CLOEXEC`.
Closed standard descriptors and their close-on-exec intent remain preserved.
The public async API has no descriptor handoff parameter; reviewed BuildRunner,
native compiler and QEMU callers do not declare an extra-descriptor handoff.
This intentionally removes ambient descriptors above stderr from Darwin async
children; an explicit handoff API would need its own contract.

Native macOS C repro failed seven descriptor cases against the old core
runtime. Both corrected core and bootstrap runtime lanes passed the expanded
existing fixture: non-CLOEXEC sentinel exclusion, unchanged parent ownership,
stdin/stdout/stderr byte transport, each standard descriptor closed and
close-on-exec separately, multithreaded launch, exit status, missing executable
and malformed argument rejection. Each executable has a ten-second deadline.
Reproduce with `sh scripts/check/check-macos-async-spawn-ownership.shs`.
Evidence is `/private/tmp/buildrunner-darwin-fd-20261028/` (`red.status` is 1;
`green-core.status` and `green-bootstrap.status` are 0). Bootstrap compilation
retains a pre-existing nested-comment warning in runtime.c.

This closes a resource inheritance defect in the real worker launch primitive.
It does not bind executable bytes/cwd or establish descendant containment,
retained cancellation ownership, tree retirement, or frozen V4 receipt/ACK.
V4 guards/capabilities and raw PID semantics are unchanged. Actual BuildRunner
Hello remains unqualified. No Docker or Phase2 rebuild was used.

Luna independently reviewed the source diff and found no P0/P1 issue. Its
compatibility note is documented at the public C API boundary: out-of-tree
Darwin callers relying on ambient descriptor handoff must change; other
platforms retain their previous inheritance policy.


## Shared SOSIX owner integration and admitted image digest (2026-10-29)

Release baseline `a538313ff6c` still used direct executable pins in both
`bootstrap_builder/worker.spl` and `test_runner_new/sdn_wrapper.spl`. The hosted
SOSIX owner existed only in an unmerged draft. Both application launch paths
now use `std.nogc_sync_mut.sosix.memory_executable_v1`; their direct pin/start
imports and calls are removed. The synchronous family matches the native
provider rather than importing a synchronous provider from the draft's async
family. Native process observation remains the lower-level provider, not a
second application launch route.

BuildRunner previously hashed `producer.exe` while checking staging, then
later pinned it and trusted the pin's own digest. A replacement between those
steps could therefore run before result admission. The shared owner's
`digest_expected(task.producer_digest)` now rejects a differing immutable
snapshot before start. The failure branch closes both directory and executable
pins. The successful start retains the same provider-owned descriptor and V4
lease, collection, cancellation and exact frozen ACK behavior.

This change does not implement Darwin execution. Memory pinning still uses the
Linux sealed static-ELF provider; there is no pathname fallback. The current
native V4 start also rejects ProcessGroup on Linux, so Linux pin support must
not be described as a working grouped runner. Both runner clients retain their
ProcessGroup policy. None memory enforcement remains monitor-only, and tasks
requiring enforcement still reject before launch.

Diagnostic verification with the preserved P1 interpreter: the new digest
contract has 4/4 examples passing and existing worker staging/output tests have
2/2 passing. The in-development SDN wrapper suite has 5/10 passing and five
`unsupported test runner worker SDN schema` failures both before and after this
change; it is not a PASS. The native-only missing-image owner spec cannot run
through the interpreter's opaque process adapter and is kept separate. The
native Darwin C cwd/unavailable-provider selfcheck passes, but mocks executable
pinning and does not qualify the new Simple owner ABI or Hello execution.

The preserved P2 compiler has no `check` command. All diagnostic logs are under
`build/astra-sosix-owner-20261029`; successful native owner compilation/execution
and actual grouped Hello remain distinct required evidence.

Native owner ABI qualification was attempted with the preserved P2 executable
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`
and the new `test/fixtures/sosix/memory_executable_native_smoke.spl`:

- Positional entry admission collected zero sources before compilation.
- Explicit application/library roots with entry closure exceeded the sampled
  2 GiB RSS cap: exit 88, peak 2,105,024 KiB, cleanup quiescent.
- Narrowing the source root to the fixture directory, while preserving library
  import resolution through SIMPLE_LIB, also exceeded that cap: exit 88, peak
  2,121,728 KiB, cleanup quiescent.

The guard imposed a 90-second deadline and measured a 24 GiB host. No native
artifact or process success is claimed. This is a concrete remaining compiler
closure-resource qualification issue; neither increasing the budget silently
nor substituting an interpreter run would establish the owner ABI. The source
migration remains draft pending native qualification.
