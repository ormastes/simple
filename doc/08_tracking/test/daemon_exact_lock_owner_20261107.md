# Daemon exact lock owner: bounded native diagnostic

Source: `10a44295b95dab7e3f8ae7cfc8916cc78ba3bb1f`, aarch64 Linux.
The reviewed timeout-zero concern applies to code before ancestor
`6c17f814aa0782d8ccaa6f91f97c722658392db5`. Exact PR parent/base and head
already contain its nonblocking fix. Current release `37f6cb8b4066` has the
same CoreC provider blob as the PR:

- CoreC `runtime_native.c`: `9f08783b7403e53a5e78c1b764f0e8cb533119f7`.
- Hosted C `runtime_host_file_exports.c`: `8e002a9c5f6bbc6f53ba09b0635c456b38a48324`.
- Rust native `file_ops.rs`: `9a1244b2ababbcdca0c3aafaf834bb3cefec4b30`.

All three use `LOCK_NB` on POSIX and `LOCKFILE_FAIL_IMMEDIATELY` on Windows
for nonpositive timeouts. No provider edits were needed. The interpreter is
excluded because its reentrant locking cannot qualify same-process contention.

## Execution and composition

One LLVM/CoreC entry-closure build of
`test/fixtures/native_daemon_exact_lock_owner/main.spl` exited 0. Producer SHA256:
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350` (unadmitted).
Private HIR/frontend/native caches and TMPDIR, no stub fallback, one compiler
thread and a 360-second process-group timeout were used. Input hashes were
checked unchanged afterward.

The link command records `simple_rt_323213_host_runtime_native.o`; the builder
removed that temporary object, so its hash is unavailable. CoreC source SHA256:
`e53c7fbc13043da858b6498b5ee47ed788392b9050b31071f953a8654bf7a3ba`.
The published executable and link receipt agree on SHA256:
`ec6279146839361fc406dceaeda02cddd85e97cc96c3c1e5540c7cc6fa144a89`.
Its `rt_file_lock` disassembly branches on timeout <=0 to `0x24a6c`, loads
flags 6 (`LOCK_EX | LOCK_NB`) and calls `flock`. Thus the tested linked
provider is nonblocking; the compiler's age was not used as provider evidence.

One executable run under a 20-second process-group timeout exited 0 and printed
`daemon exact lock owner: PASS`: 0.40 seconds, maximum RSS 28,384 KiB.
An earlier launcher preflight exited 125 because TMPDIR was omitted; it did not
launch the executable. The actual run used the private TMPDIR. No passing test
was repeated.

The fixture checks same-PID replacement, stale receipt refusal, legacy refusal
and compatibility, held-guard acquisition/release refusal, and retained guard
path. Logs, source hashes, link command/receipt, disassembly and Sol review are
under `build/daemon-exact-lock-native/` in the isolated daemon worktree.

This reconciles the review's provider-contract concern for the exact tested
native composition. Full SSpec, runner-shutdown execution, Windows execution,
entropy-failure injection, admitted core/MCP gates and release qualification
remain NOT_RUN. The separate spool-hash failure is unchanged.
