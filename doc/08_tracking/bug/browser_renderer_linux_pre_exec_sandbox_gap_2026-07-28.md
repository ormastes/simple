# Browser renderer Linux pre-exec sandbox gap

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## 2026-08-17 verification — runtime lane

**Verdict: STILL OPEN as an EVIDENCE gap, not a code defect.**

The doc's own remaining item is un-landed *installed-production evidence*, not a
missing implementation — stage one is implemented and admission-guarded. No
source defect in `src/runtime/runtime_process.c` was identified or fixed by this
lane, and none is claimed.

**What was NOT proven.** The named reproducer
`test/01_unit/runtime/run_process_piped_write_test.shs` was not executed this
session (host reserved for a stage-3 bootstrap), so there is no `Results:` line
either way. Closing this row requires the installed-production transcript the
doc asks for; a source read cannot supply it.

## 2026-08-17 verification — runtime slice (classified by CONTENT)

**Verdict: STILL OPEN, but the open item is EVIDENCE, not code.** The pre-exec
sandbox stage is present in current source: `src/runtime/runtime_process.c`
declares `rt_browser_renderer_spawn_sandboxed` (:889, :1408) and
`rt_browser_renderer_sandbox_enter` (:896), includes `<linux/seccomp.h>` (:966),
and `proc_spawn(..., bool sandboxed_renderer)` (:1239) admission-guards the slot
(`proc_alloc`, :1003-1016), forces an absolute `cmd` (:1244), and redirects
stdout/stderr to `/dev/null` in the child (:1328-1330). Whole-tree syntax gate is
green: `PASS — 104 file(s) compiled, 0 errors` (`check-c-runtime-compiles-push.shs`).

**What was NOT proven.** The doc's actual gap — installed-production evidence from
a deployed renderer — was not collected. Nothing in `src/runtime/*.c` is reachable
from `bin/simple` (Rust seed, Rust runtime), so no interpreted probe here can be
anything but vacuous. Needs a native build + an installed-production run transcript.
