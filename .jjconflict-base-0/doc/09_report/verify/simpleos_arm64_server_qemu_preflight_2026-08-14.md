# SimpleOS ARM64 server QEMU preflight — 2026-08-14

STATUS: BLOCKED

The canonical gate was invoked once, fail-fast, with both admission variables
explicitly unset. It exited before the payload builder, disk-image builder, or
QEMU. No Stage2, Rust seed, stale server ELF, x86 substitute, or marker payload
was used.

```text
schema=SimpleOsArm64ServerQemuPreflightFailureV1
started_utc=2026-08-14T08:02:11Z
finished_utc=2026-08-14T08:02:11Z
source_revision=900f9188ac50182f8f95505639072e9b1d9f7e2e
command=env -u SIMPLE_BUILD_COMPILER -u SIMPLEOS_ARM64_SERVERS_COMPILER_ADMISSION_RECEIPT sh scripts/check/check-simpleos-arm64-servers-qemu.shs
exit_status=1
stderr=simpleos-arm64-servers-qemu: FAIL: SIMPLE_BUILD_COMPILER is required; no compiler default is admitted
payload_build_attempted=false
qemu_launched=false
```

Current prerequisite state:

```text
qemu-system-aarch64=present
host_tools=present
host_ports_18080_15433=previous-read-only-preflight-free
storage_available_kib=1797065456
sysroot_crt0=present bytes=1400
sysroot_os_archive=present bytes=1044560
sysroot_cc=present bytes=331
sysroot_linker=present bytes=1957
target_runtime=present bytes=281814
SIMPLE_BUILD_COMPILER=missing
SIMPLEOS_ARM64_SERVERS_COMPILER_ADMISSION_RECEIPT=missing
```

Retained evidence is under
`build/test-artifacts/simpleos-arm64-servers-qemu-preflight/`: `state.env`,
`stdout.log`, and `stderr.log`. The state receipt binds UTC, HEAD, exact command,
exit status, no-build/no-QEMU state, and both output hashes.

The sole authoritative blocker is now the missing admitted current-source
Stage4 compiler and its matching
`simpleos-arm64-current-source-compiler-admission-v1` receipt. Once those exist,
the next permitted command is:

```sh
env SIMPLE_BUILD_COMPILER=/absolute/path/to/admitted-stage4-simple \
  SIMPLEOS_ARM64_SERVERS_COMPILER_ADMISSION_RECEIPT=/absolute/path/to/receipt.env \
  sh scripts/check/check-simpleos-arm64-servers-qemu.shs
```
