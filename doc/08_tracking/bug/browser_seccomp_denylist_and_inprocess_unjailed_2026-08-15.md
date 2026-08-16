# Browser jail: seccomp is a deny-list and in-process browsers are unjailed

- **Date**: 2026-08-15
- **Status**: ALL THREE PROBLEMS ADDRESSED IN CODE; runtime execution of the
  sandboxed render is blocked on the seed (problem 1 fixed 2026-08-15: seccomp
  is now an ALLOW-list; **problem 2 fixed 2026-08-16**: user/net/IPC namespaces
  + uid/gid drop with a published posture bit; **problem 3 code-complete
  2026-08-16**: `src/app/browser/sandbox_render.spl` routes page markup through
  the jailed worker and `browser_sandbox_render_route_wired()` is now `true` —
  see "Problem 3 resolution" below, including the correction of a blocker that
  was never real)
- **Area**: runtime (C), app/browser, os/hosted
- **Research**: `doc/01_research/app/browser/browser_sandbox_model_research_2026-08-15.md`

## Problems

1. **seccomp deny-list**: `rt_browser_renderer_sandbox_enter`
   (`src/runtime/runtime_process.c:2384`) installs a seccomp-BPF filter whose
   default action is `SECCOMP_RET_ALLOW` (`:2372`) with a list of denied
   syscalls. Any syscall not on the list — including future kernel additions —
   is allowed. Standard browser practice is an ALLOW-list with default
   `SECCOMP_RET_KILL_PROCESS`.
2. **No namespaces / privilege drop**: the jail sets rlimits, `no_new_privs`,
   and Landlock, but does not unshare user/net/PID namespaces or drop uid, so
   a compromised renderer retains direct network reach unless every net
   syscall stays on the deny-list.
3. **In-process browsers bypass the jail**: only the hosted renderer worker
   (`src/os/hosted/hosted_browser_renderer_worker.spl:1249`, broker
   `hosted_browser_renderer_process.spl:1595`) enters the jail. The
   in-process browsers under `src/app/browser/**` and `src/os/apps/*browser*`
   evaluate page script in the host process with no OS confinement.

## Required fix (Phase 2 of the research doc)

- Convert the seccomp filter to an ALLOW-list with `KILL_PROCESS` default;
  enumerate the worker's actual syscall set (strace under the spec suite).
- Unshare user+net (+PID where possible) namespaces before entering the jail.
- Route the in-process browsers' page-script execution through the jailed
  renderer worker instead of the host process.

## Fixed 2026-08-15 (this change)

1. **seccomp ALLOW-list (problem 1: FIXED).**
   `browser_renderer_apply_seccomp` (`src/runtime/runtime_process.c`, applied
   by `rt_browser_renderer_sandbox_enter`) is now an ALLOW-list with default
   `SECCOMP_RET_KILL_PROCESS`: only read/write/readv/writev, close,
   fstat(/64), mmap(/2)/munmap/mprotect/mremap/brk/madvise, futex(+time64),
   clocks/nanosleep/gettimeofday, exit/exit_group, rt_sigreturn/sigreturn/
   sigaltstack/rt_sigaction/rt_sigprocmask/restart_syscall, epoll*/poll/
   ppoll(+time64), getrandom, sched_yield, getpid/gettid are allowed. The
   architecture check and (on x86_64) the x32-ABI kill are kept; the preinit
   startup deny filter (fork/exec/socket) is unchanged. Any other syscall —
   including future kernel additions — kills the process.
   Proven natively by a new self-check
   (`src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`):
   a forked child enters the REAL jail via `rt_browser_renderer_sandbox_enter`
   (preinit contract simulated: argv[0]=marker, empty envp, fds 0..3 only),
   read/write on inherited pipe fds succeed, then `socket()` KILLS the child
   with SIGSYS (not the old EPERM deny-list behaviour). PASS on this host.
   Operational note discovered while testing: the jail's RLIMIT_NOFILE=4
   means the in-jail Landlock ruleset fd only allocates when the worker holds
   fds 0..3 only — a worker with a higher open fd fails `sandbox_enter`.
2. **Honest sandbox posture for the in-process browser (problem 3: partial).**
   New `src/app/browser/sandbox_status.spl`: `SIMPLE_BROWSER_SANDBOX=1`
   requests jailed rendering; `browser_sandbox_status()` reports
   requested/jailed/mode/reason fail-closed. `src/app/browser/main.spl` gained
   `--sandbox-status` and a gate: a sandbox request is REFUSED (exit 1, honest
   message) rather than served unjailed — never a silent sandboxed claim.
   Spec: `test/01_unit/app/browser/browser_sandbox_status_spec.spl`
   (3 examples, green).

## Still open (exact remainder)

- **Worker routing (problem 3 core)**: route `src/app/browser`'s page
  rendering (render_adapter/browser_engine_pixels_at) through the sandboxed
  renderer worker via the broker `hosted_browser_renderer_process.spl`
  (`HostedBrowserRendererProcess`, ~3.5k lines). When it lands, flip
  `browser_sandbox_worker_routing_available()` in
  `src/app/browser/sandbox_status.spl` (the single flip-line) and the refusal
  gate becomes the jailed path automatically. `src/os/apps/*browser*` remain
  unjailed too.
- **Namespaces / uid drop (problem 2)**: FIXED 2026-08-16 — see the section
  below. user/net/IPC unshare + uid/gid drop, posture published. PID namespace
  deliberately excluded (no fork possible under `RLIMIT_NPROC=0`).
- Verification gap noted 2026-08-15: `bin/simple test
  test/01_unit/os/hosted/hosted_browser_renderer_worker_spec.spl` times out at
  the test-daemon's 120s worker budget on this host (pre-existing; the
  deployed `bin/simple` is a prebuilt binary that does not contain this C
  change, so the timeout is unrelated to the ALLOW-list).

## Interim mitigation (landed 2026-08-15)

Engine-level capability gate: untrusted page script
(`JsRuntime.new_browser`) is denied `require("process"/"os"/…)` and
`process.exit/cwd/nextTick` at native dispatch —
`src/lib/{gc_async_mut,nogc_sync_mut}/js/engine/interpreter_native.spl`,
spec `test/01_unit/lib/js/js_native_confinement_spec.spl`.

## Landing note (2026-08-15)

The seccomp ALLOW-list conversion, honest browser sandbox surface, and the
engine2d enum alias-path comparison fixes landed in origin/main commit
`f549cda1991a442a5678a129a4ae4d70c80ea760` (11 files, all pre-push guards +
C-runtime compile verified against the committed tree). NOTE: that commit's
message text was mislabeled by a landing-script heredoc bug — it repeats the
prior commit's "strict-create enum identity, vendored rspirv repair" subject
instead of describing the seccomp/sandbox/enum work it actually contains. The
TREE is correct; only the message is wrong. Force-push is disallowed here, so
the message was not amended.

## Fixed 2026-08-16 (problem 2: namespaces / privilege drop)

`browser_renderer_enter_namespaces()` in `src/runtime/runtime_process.c`
unshares `CLONE_NEWUSER`, then writes `/proc/self/setgroups=deny`, `gid_map`
and `uid_map` (identity-mapping the caller's own uid/gid), then unshares
`CLONE_NEWNET | CLONE_NEWIPC`. It runs from `browser_renderer_preinit` and the
ordering is load-bearing and not rearrangeable:

    namespaces -> landlock -> seccomp

Namespaces need `openat` and a writable `/proc`; the Landlock ruleset declares
`handled_access_fs` with **no allow rules**, so every write dies the moment it
applies — including `/proc/self/uid_map`; and the seccomp allow-list contains
neither `unshare` nor `openat`. Any other order makes the uid/gid drop
impossible.

PID namespace is deliberately NOT unshared: `CLONE_NEWPID` only takes effect
for children created after the unshare, and the jail already sets
`RLIMIT_NPROC=0` so the worker cannot fork. Claiming it would be theatre.

**Namespace loss is recorded, not fatal.** Ubuntu 24.04 ships
`kernel.apparmor_restrict_unprivileged_userns=1`, which lets an unconfined
binary create `CLONE_NEWUSER` but strips its capabilities, so `CLONE_NEWNET`
returns `EPERM`. Treating that as fatal would turn a working seccomp+Landlock
jail into NO jail on every default Ubuntu host — strictly worse security for a
stricter-looking check. `rt_browser_renderer_namespaces_active()` publishes
which layers were obtained; the gate prints
`sandbox_namespaces=active|unavailable`.

Proven by `src/runtime/test/rt_browser_renderer_namespace_selfcheck.c`, driven
by `scripts/check/check-browser-renderer-sandbox-seccomp.shs`. The check does
not trust the posture boolean: it compares `/proc/self/ns/net` before and after
and FAILS on a false claim in either direction (posture says isolated while the
namespace is unchanged, or the namespace moved while posture under-reports).

Evidence across four hosts, which is what makes the check non-tautological:

| Host | Posture | Net namespace |
| --- | --- | --- |
| bare host (Ubuntu 24.04) | `unavailable` | `net:[4026531840]` unchanged |
| `docker run` (default) | `unavailable` | `net:[4026533421]` unchanged |
| `docker run --security-opt apparmor=unconfined` | `unavailable` | `net:[4026533421]` unchanged |
| `docker run --privileged` | `active` | `net:[4026533421]` -> `net:[4026533540]` |

QEMU was not used: no Linux x86_64 qcow2 exists in-tree and `curl`/`wget` are
blocked by the context-mode rules, so a VM image must be supplied out of band.
The privileged container exercises the same kernel property.

Problem 3 remains open: the in-process browsers under `src/app/browser/**` and
`src/os/apps/*browser*` still evaluate page script in the host process without
entering this jail.

### Sabotage evidence (2026-08-16)

A gate that has never gone red proves nothing. Both arms were sabotaged in a
scratch copy of `src/runtime/` (never the working tree, to avoid racing a
pending push) and both bit:

| Arm | Sabotage | Result |
| --- | --- | --- |
| pre | none | `PASS — 4 check(s) verified` |
| 1 | `rt_browser_renderer_namespaces_active()` -> `return true` unconditionally | **FAIL** exit 1: `namespaces_active()=true but net ns unchanged (net:[4026531840]) — the jail advertises isolation it does not have` |
| 2 | seccomp default `SECCOMP_RET_KILL_PROCESS` -> `SECCOMP_RET_ALLOW` (the exact pre-2026-08-15 deny-list defect) | **FAIL** exit 1: `child survived a non-allow-listed syscall (fail-open)` + `expected SIGSYS kill on socket(), got status 0x7b00` |
| post | reverted | `PASS — 4 check(s) verified` |

Arm 2 is the important one: it replays the original defect this lane exists to
prevent, and the gate catches it. Arm 1 proves the posture bit cannot lie.

### QEMU: hard-blocked on this host (not merely "not done")

Three independent routes are closed, so this is not a matter of spending more
time:

1. no Linux x86_64 `.qcow2` / `.img` in-tree (only a riscv32 FAT image);
2. `curl`/`wget` are blocked by the context-mode rules, so no image can be
   fetched;
3. the host kernel cannot be borrowed for a `-kernel` boot: `/boot/vmlinuz-*`
   is `-rw------- root root` and `sudo -n` reports a password is required. No
   other bootable kernel is user-readable (`/sys/kernel/btf/vmlinux` is BTF
   metadata, not a bootable image).

`docker run --privileged` exercises the same kernel property and DID prove the
active path, so the QEMU gap is redundancy, not missing evidence. Resuming it
needs a VM image or kernel supplied out of band.

### Evidence gap closed (2026-08-16, self-audit)

The first version of the namespace self-check verified only the NET namespace
identity, while the fix and its docs claimed "user/net/IPC namespaces + uid/gid
drop". Three of those four claims were unverified. Closed:

- all three namespace identities are now compared (`/proc/self/ns/{net,user,ipc}`),
  and a partial unshare reported as full isolation is an explicit FAIL;
- the privilege drop is proven by an indirect oracle: the uid/gid observed
  INSIDE the jail must equal the pre-jail ids. In a fresh user namespace with
  no `uid_map` written, `getuid()` returns the overflow id (65534/nobody), so
  the original id coming back proves the identity map was actually written.
  The map cannot be read back directly — landlock denies the read by then.

Observed under `docker run --privileged`:

```
namespaces=active;
  net  net:[4026533421] -> net:[4026533540]
  user user:[4026531837] -> user:[4026533538]
  ipc  ipc:[4026533418] -> ipc:[4026533539]
  uid/gid 0/0 mapped through
```

Sabotage arm 3 (removing the `uid_map` write) bit as designed:

```
FAIL: uid/gid inside jail is 65534/0, expected 0/0 — the identity
uid_map/gid_map was not written (overflow id means an unmapped user namespace)
```

Lesson worth keeping: a check that observes the single easiest-to-see effect
will happily pass a partial implementation. Verify every claim the change
makes, or narrow the claim.

## Problem 3 resolution (2026-08-16) — and a blocker that was never real

`src/app/browser/sandbox_render.spl` now performs the route:

    broker (HostedBrowserRendererProcess)
      -> jailed worker (rt_browser_renderer_sandbox_enter)
      -> DrawIrComposition back over the pipe
      -> Engine2dCompositorBackend.render_draw_ir_composition
      -> [u32] pixels

`render_adapter.browser_engine_pixels_at` takes this route whenever a sandbox
is requested, so page parse/cascade/layout/paint and any script run in the
child. This process only rasterizes Draw IR; it never evaluates page content.

### The false blocker

This flag sat at `false` with a documented justification that was wrong:

> `HostedBrowserRendererProcess.render(...)` returns a `DrawIrComposition`, not
> `[u32]` ... the app needs a rasterization step (Engine2dCompositorBackend)
> that it does not have today.

`Engine2dCompositorBackend.render_draw_ir_composition` exists at
`src/os/compositor/compositor_engine2d.spl:364` and has 20 call sites.
`src/os/hosted/hosted_browser_render_evidence.spl:77` already ran precisely the
sequence declared impossible. The claim came from a search with the repo's
default `grep` — a `.gitignore`-honouring ugrep wrapper that returned 0 hits
where `/usr/bin/grep -rn` returns 20 — and was then quoted back as confirmation
by a later reader, including a subagent that called it "confirmed by exhaustive
grep". Rule added to `.claude/skills/spipe.md`: absence claims require
`/usr/bin/grep`, and a blocker recorded in a doc is a claim to re-verify, not a
fact to build around.

The second stated blocker was true but never applied to this flag: the worker
argv marker is dispatched only at `hosted_entry.spl:285` and must not be added
to the CLI (it would pull `os.hosted.*` into every `simple` invocation's
startup closure). It does not need to be — `begin_start`
(`hosted_browser_renderer_process.spl:1578`) takes the worker executable as a
parameter, which is exactly what the operator-supplied
`SIMPLE_BROWSER_RENDERER_WORKER` provides.

### Fail-closed contract

Every failure inside the jailed path returns `Err`, and
`browser_engine_pixels_at` converts that to an EMPTY pixel buffer. It never
falls back to an in-process render: a fallback would hand the caller good
pixels with no way to know page script had just run unconfined, which is the
precise defect this route removes. An empty buffer is never a valid render
(a real one is always `width * height`), so callers can detect it.

### Startup-failure coverage (was missing entirely)

`src/runtime/test/rt_browser_renderer_startup_failure_selfcheck.c` closes the
third acceptance row. The two older self-checks both describe a jail that is
already up; nothing asserted what happens when it must not come up, even though
every failure path in `browser_renderer_preinit` collapses to a single
`_exit(126)` and `rt_browser_renderer_sandbox_enter` collapses to a bare
`false`. Two arms, neither able to SKIP because both fire before any kernel
capability is consulted:

1. a non-empty `envp` violates the worker entry contract and must be fatal
   with exit 126 — never an inherited environment;
2. `rt_browser_renderer_sandbox_enter` must return `false` when preinit never
   ran, rather than report a jail it never built.

Both were sabotage-tested (relax the envp check; drop the preinit-active
guard) and both FAIL under sabotage, PASS clean.

### Gate count was hardcoded

`check-browser-renderer-sandbox-seccomp.shs` printed a literal
`PASS — 4 check(s) verified`, which would have kept claiming four even if a
check were deleted — the vacuous-pass shape the repo's other guards exist to
refuse. The count is now accumulated as each self-check passes, and a run that
verified nothing is an ERROR. Current verdict: `PASS — 6 check(s) verified`.

### What is still NOT proven

The sandboxed render has never executed. On the Rust seed it dies with
`unknown extern function: rt_browser_renderer_spawn_sandboxed` — the C runtime
defines it (`runtime_process.c:889,1408`), the seed's extern registry does not
(same class as `deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md`).
No admitted pure-Simple runtime exists on this host, so REQ-WEB-BROWSER-014
stays **not promoted**. What IS proven natively: the jail's syscall contract,
its namespace posture, and its startup-failure behaviour, all via the C
self-checks.

## Duplication collapsed (2026-08-16, follow-up)

The first cut of `sandbox_render.spl` re-derived the broker + raster handshake
that `hosted_browser_render_evidence.spl` already performed twice — a third
copy of the same six steps, written by the same session that had just read the
first copy to prove the rasterizer existed.

Collapsed into `src/os/hosted/hosted_browser_render_session.spl`
(`open` / `render_frame` / `rasterize` / `close`). All three call sites now go
through it. Shape chosen by reading every caller: a one-shot `html -> pixels`
helper would have broken `hosted_browser_animation_evidence`, which holds one
worker across `init` -> `begin_advance` -> poll -> a second rasterize.

Risk accepted knowingly: this rewrote verified evidence code with no runtime to
re-run it. Priced by two facts — `bin/simple check` type-checks each file
without a runtime (all three PASS), and the blast radius is a single importer
(`hosted_entry.spl:81,82,288,292`). Nothing else in the repo calls those
functions.

Not affected: the tiny browser. Verified all 37 files under
`src/lib/nogc_sync_mut/tiny/`, `src/os/apps/tiny_browser/` and
`src/os/services/tiny_wm/` import only `std.tiny.*` / `tiny_wm` /
`tiny_browser` / `std.common.*` / `std.nogc_sync_mut.*` — no path into the
large browser at all.
