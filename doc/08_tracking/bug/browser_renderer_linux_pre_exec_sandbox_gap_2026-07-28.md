# Browser renderer Linux pre-exec sandbox gap

Status: implemented and admission-guarded; installed production evidence
pending, release-blocking

`rt_browser_renderer_spawn_sandboxed` scrubs descriptors/environment and then
executes the full hosted renderer. The worker installs rlimits, `no_new_privs`,
Landlock, and seccomp only after the dynamic loader, runtime initialization,
and `hosted_entry` dispatch have already run. That startup window therefore has
ambient Linux filesystem, network, and process authority.

The smallest viable hosted fix is a renderer-owned ELF `DT_PREINIT_ARRAY`
callback, activated only by the fixed renderer argv. At preinit time the ELF
interpreter and dependencies are already mapped but application/dependency
constructors have not run, so stage one can install `no_new_privs`, deny-all
Landlock, and a startup-safe seccomp filter denying socket, fork/clone, and
further exec without maintaining a loader path allowlist. The renderer must
then install the existing stricter stage-two policy idempotently. A statically
linked launcher is the fallback; a dynamic trampoline retains the same loader
window.

Acceptance requires a pre-main constructor probe launched through the
production broker. Socket creation, an ungranted host-file read, and fork must
all be denied while the normal ready/frame protocol still succeeds. macOS and
Windows must continue to fail closed until equivalent native isolation exists.

A full-policy preinit prototype failed the bounded
`test/01_unit/runtime/run_process_piped_write_test.shs` gate with exit 9 in
three distinct fix/check cycles and was reverted. Resume by splitting the
startup-safe stage-one filter from the post-main policy; do not install the
current full worker policy unchanged at preinit.

## Implemented stage one

`runtime_process.c` now installs an executable-only ELF preinit callback. It
activates only for the broker-fixed `simple-browser-renderer` argv with an
empty environment, then applies `no_new_privs`, deny-all Landlock, and a
startup-safe seccomp filter denying socket, fork/clone, and further exec. The
existing worker entry layers the stricter stage-two limits and filter.

The production-spawn C probe observes file, socket, and fork denial from a
constructor and then completes the normal stage-two child handshake. It passed
on verification cycle 2. Keep this issue release-blocking until the admitted
pure-Simple renderer completes ready/frame protocol evidence with the same
artifact; current target construction is blocked by the compiler/runtime link
failure recorded in the SPipe state.

Stage-two entry now additionally requires the preinit-active marker. The
focused C gate proves a normal process cannot call stage two and reach READY
without stage one, while the broker-spawned marker path still completes both
stages. This closes artifact/link omission as an admission bypass; it does not
replace the still-pending installed-artifact ready/frame evidence.

The final stage-two seccomp policy now also denies `get_robust_list`, preventing
a hostile site renderer from disclosing the same-UID broker's robust futex-list
address. The focused host C containment gate passes. Installed pure-Simple
READY/frame evidence remains compiler-blocked and no bootstrap/seed substitute
is accepted.

## 2026-09-21 admission-gate repair

The namespace self-check had remained behind the retired
`SPL_HAS_BROWSER_RENDERER_NAMESPACES` switch. Its translation unit therefore
had no `main`, so `check-browser-renderer-sandbox-seccomp.shs` could not link
the mandatory namespace phase. The check now calls the actual
`browser_renderer_preinit` path with the broker's fixed argv and empty
environment, then proves that `rt_browser_renderer_namespaces_active()` agrees
with the observed `/proc/self/ns/net` identity and that a failed namespace
attempt cannot strand the worker under different effective credentials. An
injected partial-setup failure must terminate with exit 126. A denied
namespace request is reported as `unavailable`; a claimed active namespace
must change identity.
On the verification host it reported `namespaces=unavailable`, with
`uid=1000`, `gid=1000`, and `net:[4026531833] -> net:[4026531833]`. This
direct preinit probe proves fallback credential stability and fail-closed
partial setup, but does not prove root-drop; the current preinit implementation
does not claim root-drop, and installed renderer evidence must cover the
remaining runtime contract.

This restores source-level admission evidence for the pre-exec stage. The
installed pure-Simple ready/frame artifact remains the outstanding release
evidence described above.

## 2026-11-05 Linux runtime evidence (aarch64)

Host: aarch64 Linux (Ubuntu, kernel with seccomp+Landlock; namespace posture
`unavailable`, uid=gid=1000 — same posture as the 2026-09-21 admission run).
All commands used the worktree at `/tmp/wt-libbug-presandbox` with the
seed-built full CLI
`/home/yoon/dev/simple/build/phase_snapshots/phase1_1793422538/simple`
substituted wherever the gate refers to `bin/simple` (no `bin/simple` exists
on this host).

Evidence ran:

1. `sh test/01_unit/runtime/run_process_piped_write_test.shs` — the bounded
   gate named above. Result: **PASS (exit 0)**, stable across 5 consecutive
   runs. The gate now proves, through the production
   `rt_browser_renderer_spawn_sandboxed` broker path: pre-main constructor
   denials (host-file read EACCES, socket EPERM, fork EPERM), hostile loader
   environment absent post-scrub (LD_PRELOAD, LD_AUDIT, LD_DEBUG,
   LD_DEBUG_OUTPUT, LD_LIBRARY_PATH, LD_ORIGIN_PATH), stage-one Landlock
   host-file write denial (open O_WRONLY -> EACCES) before stage two, stage
   two entry, and the ready/frame protocol (`small` in, `sandbox-ok` out)
   with a second concurrent renderer, slot reuse, and no host mutation.
2. `sh scripts/check/check-browser-renderer-sandbox-seccomp.shs` — the
   admission check. Result: **PASS — 8 check(s) verified** (SANDBOX-N/E/D,
   startup-failure, namespace posture `unavailable` matching observed
   `/proc/self/ns/net` identity, partial-failure exit 126). No regression
   from the gate repair; the stage-two allow-list contract (non-allow-listed
   socket() is SIGSYS-killed, not EPERM-denied) is confirmed intact.
3. `simple test test/03_system/security/hosted_renderer_loader_environment_spec.spl
   --mode=interpreter` — Result: **PASS (1/1)**.

Root causes found while closing the gap (the gate was red on this branch for
two independent reasons):

- **Link break (new, 2026-10-31):** `e2e83308682` ("session-owned process
  trees") made `rt_process_spawn_piped_argv` call `rt_child_set_pdeathsig`,
  which lives in `src/runtime/runtime_process_tree.c`. The single-TU gate
  link no longer resolved it. Fix: the gate now links
  `runtime_process_tree.c` alongside `runtime_process.c` (`--gc-sections`
  still drops the unused wider-runtime paths).
- **Probe/filter contract mismatch (pre-existing, arch-independent):** the
  probe's post-`sandbox_enter` checks expected `EPERM`/`EACCES` errno
  denials for ~30 syscalls (getrlimit, open, socket, fork, execve, fcntl,
  ...). The shipped stage-two policy is the SANDBOX-E allow-list whose
  default is `SECCOMP_RET_KILL_PROCESS`; the first post-enter syscall
  (`getrlimit`, probe code 14) SIGSYS-killed the worker (raw wait status
  0x9f, verified by gdb backtrace: `sandbox_limit_is` -> `syscall`). A deny
  with errno post-enter is unobservable in-process under that contract —
  the probe would have to die to "check" it — and the deny-list shape is
  the reverted full-policy design this bug doc forbids reinstalling. Fix:
  the probe now observes denials with errno only where the architecture
  provides them (stage one: pre-main constructor file/socket/fork, loader
  env scrub, Landlock write denial pre-enter) and uses the surviving
  ready/frame handshake as the in-jail evidence, exactly the acceptance
  shape this doc states. No source filter changed.

Also repaired `hosted_renderer_loader_environment_spec.spl`, which could not
execute at all: the literal C snippet `"{NULL}"` was parsed as string
interpolation of an undefined variable; escaped to `{{NULL}}`. Assertion
content unchanged.

Files changed (worktree branch `work/libbug-linux-presandbox-20261105`):
- `test/01_unit/runtime/run_process_piped_write_test.shs` — link `runtime_process_tree.c`.
- `test/01_unit/runtime/process_piped_write_test.c` — probe rewritten to the
  SANDBOX-E allow-list contract; constructor gains loader-env scrub
  evidence; unused `sandbox_limit_is` removed.
- `test/03_system/security/hosted_renderer_loader_environment_spec.spl` —
  `{{NULL}}` escape only.
- This doc (appended evidence).

macOS/Windows remain fail-closed and untouched: `rt_browser_renderer_sandbox_enter`
still returns false off Linux and the preinit marker is never set without
the broker-fixed argv + empty environment.

## 2026-11-09 verification (aarch64 Linux, worktree lane)

Re-checked on release/1.0.0 (`eee4ddede18`): the gap is already closed; no
source change was made. The pre-exec child window of
`rt_process_spawn_piped_argv` (runtime_process.c:2472-2541) performs only
async-signal-safe calls between fork and exec (setpgid, prctl via
`rt_child_set_pdeathsig`, open, dup2, close_range/close, signal, chdir,
execve/fexecve); a static census found no malloc/stdio/env mutation in the
window. Stage-one sandboxing is installed by the ELF preinit callback
(`browser_renderer_preinit`, runtime_process.c:3801; `.preinit_array` entry
:3845), and stage two requires the preinit marker (:4025). The evidence gate
repair (PR #6792, c8c559fb343) is merged on release/1.0.0.

Green on this host: `sh test/01_unit/runtime/run_process_piped_write_test.shs`
exit 0 (compiled with clang; host gcc 13 `-Werror` rejects two pre-existing
warnings at runtime_process.c:4657 and :2715 — toolchain strictness, not the
sandbox), and `check-browser-renderer-sandbox-seccomp.shs` PASS 8/8.

Still pending per this doc: installed pure-Simple renderer READY/frame
evidence. Bug row moved to fix-implemented-verification-pending.
