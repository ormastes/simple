# SOSIX host process and executable services

This requirement set covers the process/executable facade in
`std.nogc_async_mut.sosix`. It records only behavior backed by a real provider;
it does not qualify the separate owned-executable/V4 APIs or SimpleOS kernel
process materialization.

- **REQ-SOSIX-HOSTPROC-001 — synchronous execution:** on a host with an admitted
  provider, checked execution returns captured stdout, stderr, and the child
  exit code. Invalid C-string inputs and invalid capture bounds fail before
  launch. A missing executable is reported as an explicit not-found result.
- **REQ-SOSIX-HOSTPROC-002 — executable lookup:** checked lookup returns an
  existing executable path or explicit absence, and rejects invalid names.
- **REQ-SOSIX-HOSTPROC-003 — POSIX process lifecycle:** on macOS and Linux,
  BSD hosts whose runtime reports `freebsd` or `unix`, and illumos/Solaris
  runtimes, checked spawn returns a usable child identifier that can be
  observed while live and terminated. The test performs a bounded wait and
  requires a dead liveness result; a provider that reaps during kill may report
  the child as already absent to the later wait.
- **REQ-SOSIX-HOSTPROC-004 — honest platform boundary:** Windows exercises the
  real synchronous byte-capture and executable-lookup provider. The current
  text process and asynchronous spawn/kill paths remain unsupported there;
  their unsupported result must stay explicit. The SimpleOS syscall facade is
  tested by its QEMU system suite and is not evidence of a hosted provider.

The platform matrix is deliberately capability-specific. A passing Windows
synchronous case does not admit Windows lifecycle services, and a passing host
case does not qualify SimpleOS process-image materialization.
