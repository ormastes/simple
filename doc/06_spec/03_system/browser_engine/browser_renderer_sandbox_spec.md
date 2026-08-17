# Browser renderer jail confines a compromised renderer

Mirrored scenario manual for
`test/03_system/browser_engine/browser_renderer_sandbox_spec.spl`.

| Field | Value |
| --- | --- |
| Requirement | REQ-WEB-BROWSER-014 sandbox/broker |
| Cases | SANDBOX-N, SANDBOX-E, SANDBOX-D |
| Category | security |
| Gate | `sh scripts/check/check-browser-renderer-sandbox-seccomp.shs` |
| Executable spec | `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl` |
| Runtime status | **Not executed** — no admitted pure-Simple runtime on this host |

## Scenario: keeps allow-listed I/O working while killing a non-allow-listed syscall

A renderer process is confined before it parses any untrusted page. The
operator needs two opposite guarantees at once: the renderer must still do its
job (read the page bytes handed to it, write pixels back), and it must lose the
ability to reach anything else — no new sockets, no matter what the page does
to it. This scenario proves both halves against the real jail, plus the honest
third case where the host kernel cannot provide the jail at all.

### Steps

1. **Enter the real browser renderer jail via `rt_browser_renderer_sandbox_enter`.**
   The gate builds and runs
   `src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`, which
   forks a child that enters the real jail. The preinit contract is simulated
   faithfully: `argv[0]` is the marker, `envp` is empty, and only fds 0..3 are
   held. This is not a mock and not a source-text assertion.

2. **SANDBOX-N — allow-listed read/write on inherited pipe fds still succeed
   inside the jail.** Confinement that also breaks the renderer's own job is
   not a usable sandbox, so the normal path is asserted first.

3. **SANDBOX-E — a non-allow-listed `socket()` is killed by
   `SECCOMP_RET_KILL_PROCESS`, not merely denied.** This is the discriminating
   assertion. The pre-2026-08-15 filter was a *deny-list* defaulting to
   `SECCOMP_RET_ALLOW`, so an unlisted syscall — including any future kernel
   addition — was permitted, and a denied one merely returned `EPERM` with the
   child surviving. The allow-list contract is that the child dies with
   `SIGSYS`. A deny-list regression therefore fails this step rather than
   passing it quietly.

4. **SANDBOX-D — the namespace posture is published and matches reality.** The
   jail unshares the user, network and IPC namespaces and drops to an
   unprivileged identity, so the renderer loses its *route* to the network
   rather than relying on every socket-creating syscall staying denied. The
   posture is reported, never assumed: the self-check FAILS if
   `rt_browser_renderer_namespaces_active()` claims isolation while
   `/proc/self/ns/net` is unchanged, and equally if the namespace moved but the
   posture under-reports it. The gate prints
   `sandbox_namespaces=active|unavailable`.

5. **The verdict states how many checks actually ran.** A kernel without
   seccomp/Landlock, or a host with no C compiler, means the jail was never
   entered. The gate reports `ERROR — nothing was checked` (exit 2) in both
   cases and the spec fails. An unexercised property is never a pass.

### Why `namespaces=unavailable` is a pass, not a failure

Ubuntu 24.04 ships `kernel.apparmor_restrict_unprivileged_userns=1`: an
unconfined binary may create `CLONE_NEWUSER`, but its capabilities are stripped,
so the follow-up `CLONE_NEWNET` returns `EPERM`. Treating that as fatal would
turn a working seccomp+Landlock jail into **no jail** on every default Ubuntu
host — strictly worse security for a stricter-looking check. The jail therefore
enters the strongest layer set available and publishes which layers it obtained.
Only a *false* claim fails.

Ordering inside the jail is load-bearing and not rearrangeable: namespaces (need
`openat` and a writable `/proc`) must precede Landlock (declares
`handled_access_fs` with no allow rules, so all writes die, including
`/proc/self/uid_map`), which must precede seccomp (the allow-list contains
neither `unshare` nor `openat`). PID namespace is deliberately not unshared —
`CLONE_NEWPID` only affects children created after the unshare, and the jail
sets `RLIMIT_NPROC=0` so the worker cannot fork; claiming it would be theatre.

### Verdict contract

The gate's verdict is the last line of stdout:

| Verdict | Exit | Meaning |
| --- | --- | --- |
| `PASS — 3 check(s) verified: ...` | 0 | jail entered, both directions proven |
| `FAIL — ...` | 1 | the jail did not behave as specified |
| `ERROR — nothing was checked: ...` | 2 | jail never entered; not a pass |

## Evidence status

The gate itself was executed and reported `PASS — 4 check(s) verified`,
including a real `SIGSYS` kill on `socket()`. That is **native C-runtime
evidence for the jail**, and it is what closes the gap left when the seccomp
self-check landed on 2026-08-15 wired to no runner.

The namespace layer was proven on both sides of its posture, which is what
makes the check meaningful rather than tautological:

| Host | Posture | Net namespace |
| --- | --- | --- |
| bare host (Ubuntu 24.04, apparmor userns restriction on) | `unavailable` | `net:[4026531840]` unchanged |
| `docker run` (default) | `unavailable` | `net:[4026533421]` unchanged |
| `docker run --security-opt apparmor=unconfined` | `unavailable` | `net:[4026533421]` unchanged |
| **`docker run --privileged`** | **`active`** | **`net:[4026533421]` → `net:[4026533540]`** |

The privileged-container row is the one that proves the code path actually
isolates; the others prove it reports its own absence honestly.

QEMU was **not** used: there is no Linux x86_64 qcow2 in-tree and `curl`/`wget`
are blocked by the context-mode rules, so a VM image would have to be supplied
out of band. The privileged container exercises the same kernel property, so
this is a redundancy gap rather than a hole in the evidence.

The **SSpec scenario above has not been executed**: this host has no admitted
pure-Simple self-hosted runtime (see
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`
and the bootstrap admission blocker recorded in the lane state). Rust-seed
output is not accepted as evidence for this lane. The spec is written to
execute unchanged once a qualified runtime is deployed; until then
REQ-WEB-BROWSER-014 remains **not promoted**.

## Startup failure (added 2026-08-16)

The scenarios above all describe a jail that is already running. This one
describes what happens when it must **not** start.

Every failure path in `browser_renderer_preinit` collapses to a single
`_exit(126)`, and `rt_browser_renderer_sandbox_enter` collapses to a bare
`false`. A change that turned either into a silent success would leave a
renderer executing page script with no confinement at all, while every other
scenario on this page still passed — they only run once the jail is up.

Two assertions, neither of which can be skipped, because both are decided
before any kernel capability is consulted:

1. **A contract-violating environment is fatal.** The renderer worker is
   executed with an empty environment so it cannot inherit secrets, proxy
   settings, or `LD_*` injection. Handing it a non-empty environment must kill
   the process with exit 126. It must never continue unconfined.
2. **The jail is fail-closed without preinit.** A process whose `argv[0]` is
   not the worker marker is deliberately left alone — ordinary `simple`
   invocations must not be jailed. Asking such a process to enter the jail must
   be refused, not reported as a jail that was never built.

The gate's verdict states how many checks actually ran. That count is
accumulated as each self-check passes rather than printed as a fixed number, so
deleting a check lowers the count instead of leaving a stale claim behind.
