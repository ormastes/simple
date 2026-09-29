# macOS bootstrap capsule scan and live-process portability

Date: 2026-09-21

Host: aarch64-apple-darwin

Base revision: `eb98be6f2b1`

## Capsule scan errors admitted a frozen capsule

Status: FIXED; focused macOS contract suite PASS.

Priority: P0, admission fails open.

`phase2-runtime-capsule.shs` fixed the BSD `find -perm` syntax in August but
still used `[ -z "$(find ...)" ]`. Any failed permission traversal with no
stdout was accepted as proof of immutability. The test itself also used
GNU-only `stat -c`, so it failed before reaching later negative cases on macOS.

The mode assertion now uses portable `find -perm 0500`. A negative fixture
shadows only the permission scan with a `find` that exits 42 and emits no
stdout. Before the fix it produced `FAIL: failed permission scan accepted`.
The owner now checks the traversal exit status before checking its output.

Verified once after the repair:

```sh
sh test/01_unit/scripts/phase2_runtime_capsule_contract_test.shs
# PASS: Phase2 runtime capsule is atomic, SHA-bound, complete, and fail-closed
```

This suite also covers writable leaves/directories, missing files, tampered
hashes, duplicate keys, symlink dependencies, and concurrent publication.

## Live process runner unconditionally required GNU stdbuf

Status: SOURCE FIXED; native fixture and SSpec execution PENDING.

Priority: P1, stock-macOS native-build workers fail before execution.

`src/lib/nogc_sync_mut/io/process_ops.spl` prefixed every Unix live child with
`stdbuf -oL -eL`. Stock macOS has no `stdbuf`; the existing `setsid` fallback
therefore advanced execution to another missing command. The application
module is a facade, so the fix belongs only in the canonical library owner.

The inner child shell now detects `stdbuf` using its builtin `command -v` and
execs the requested command directly if it is absent. Both branches preserve
the process-group leader and existing shell quoting. On hosts without the
utility, child buffering follows the child program's policy; output polling,
capture, exit status, and timeout behavior are unchanged.

Regressions:

- `test/02_integration/bootstrap/macos_process_live_spec.spl`: quoted argument,
  stdout/stderr, exit status, and timeout assertions with stock macOS PATH.
- `test/fixtures/macos_bootstrap_process_live/main.spl`: the same operations
  as a small native entry.
- `test/01_unit/scripts/macos_process_live_native_test.shs NATIVE_FIXTURE`:
  executes that artifact with absent `stdbuf`, then a transparent `stdbuf`
  fixture and checks both option arguments and two real invocations.

The native fixture was attempted with the freshly admitted Stage 2 SHA
`96c10a67ae86d1bcfb7e90086f8ec0a4d1a9364da417c01a6dd5d82285e62f24`, eight threads,
LLVM, `core-c-bootstrap`, no `--source`, and a private cache. The first invocation
correctly refused the missing compile-event journal. With the required
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, it was terminated after 25.4 seconds when
observed per-process RSS reached 979,808 KiB (guard threshold 950,000 KiB).
No compiler output or native artifact was produced. The Astra memory lane
independently reproduced this cold inventory growth and owns that blocker.
This is not a passing native test or a measured performance improvement.

Evidence: `build/native_probe/macos-p0/{compile,compile-cold}.log` in
`/Users/ormastes/simple-tmp/macos-bootstrap-p0-cluster`.
