# Browser renderer Linux pre-exec sandbox gap

Status: open, release-blocking

`rt_browser_renderer_spawn_sandboxed` scrubs descriptors/environment and then
executes the full hosted renderer. The worker installs rlimits, `no_new_privs`,
Landlock, and seccomp only after the dynamic loader, runtime initialization,
and `hosted_entry` dispatch have already run. That startup window therefore has
ambient Linux filesystem, network, and process authority.

The shared fix belongs in `src/runtime/runtime_process.c`: launch through a
small static trampoline that installs stage-one rlimits, `no_new_privs`, a
minimal loader/runtime Landlock allowlist, and seccomp denial for network,
fork, and process control before the sole renderer `execve`. The renderer must
then install the existing stricter stage-two policy and deny further exec.

Acceptance requires a pre-main constructor probe launched through the
production broker. Socket creation, an ungranted host-file read, and fork must
all be denied while the normal ready/frame protocol still succeeds. macOS and
Windows must continue to fail closed until equivalent native isolation exists.
