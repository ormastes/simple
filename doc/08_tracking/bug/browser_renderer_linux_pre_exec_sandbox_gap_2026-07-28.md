# Browser renderer Linux pre-exec sandbox gap

Status: open, release-blocking

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
