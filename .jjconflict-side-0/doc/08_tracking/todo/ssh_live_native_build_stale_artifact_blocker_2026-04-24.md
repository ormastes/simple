# SSH Live Native-Build Blocker — 2026-04-24

## Summary

The stale-artifact fallback in `src/os/qemu_runner.spl` is now closed: the live
`x64-ssh` lane deletes any prior `build/os/simpleos_ssh_live_32.elf`, writes a
per-build marker source, and refuses guest launch unless the current invocation
produces a fresh artifact.

The remaining blocker is a compiler/build issue: fresh native builds for the
live SSH kernel do not currently complete in this workspace, so the acceptance
lane cannot yet boot a newly built guest.

## Symptom

`build_os_with_backend(get_ssh_live_target(), backend)` returns `false`, and no
guest is launched.

Observed failures on 2026-04-24:

- `bin/simple native-build ... --backend cranelift` exits `3` with no fresh
  `build/os/simpleos_ssh_live_32.elf`
- `src/compiler_rust/target/bootstrap/simple native-build ... --backend cranelift`
  fails the freestanding unresolved-symbol check with 398 unexpected symbols
- LLVM-enabled live builds are unavailable in the tested compiler binaries that
  report `LLVM backend requested but 'llvm' feature not enabled`

## Reproduction

```bash
bin/simple test test/system/ssh_live_login_in_qemu_spec.spl
```

Or directly:

```bash
bin/simple native-build \
  --source src/os \
  --source src/lib \
  --source examples/simple_os \
  --source build/os/generated \
  --backend cranelift \
  --entry-closure \
  --entry examples/simple_os/arch/x86_64/ssh_live_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_ssh_live_32.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld
```

## Impact

- Invalidates live SSH acceptance if callers rely on stale kernel reuse
- Blocks verification of the real live KEX transcript on a freshly built guest
- Prevents the OpenSSH-on-QEMU acceptance lane from proving the host-key fix

## Current Status

- Runner freshness gate: fixed
- Fresh guest build: blocked by compiler/native-build behavior
- Live KEX diagnosis on fresh kernel: blocked on the build issue above
