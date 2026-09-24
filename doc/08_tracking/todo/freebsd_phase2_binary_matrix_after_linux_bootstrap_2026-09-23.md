# TODO(P1, bootstrap): Run the FreeBSD Phase 2 binary matrix after Linux bootstrap

Do not start this lane until the Linux bootstrap has succeeded.  Then run the
canonical FreeBSD QEMU bootstrap flow with PR #1272's verifier-environment fix
present and execute the admitted Phase 2 binaries through all three required
surfaces:

- native compiler: build and execute the module probe;
- interpreter: execute the module-import probe and its regression spec;
- loader: execute the lazy module-loader regression spec.

Keep the runner fail-closed: an exit-zero command is insufficient without one
non-empty, internally consistent PASS summary, and every command must be owned
by the admitted Phase 2 compiler/runtime receipt.  Preserve the task logs,
compiler and runtime identities, command-owner receipt, final summary receipt,
per-task wall time, total wall time, and maximum RSS.  A result is not complete
until all three surfaces pass and those receipts are retained from the same
FreeBSD QEMU run.

Blocked by: successful Linux bootstrap, then availability of the FreeBSD QEMU
phase environment.  Prerequisite: PR #1272.
