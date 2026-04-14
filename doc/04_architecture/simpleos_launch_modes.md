# SimpleOS Launch Modes

**Status:** Active

This note separates the three launch paths that are easy to conflate:

1. packaged disk-backed app launch
2. resident-manifest fallback
3. true arbitrary x86_64 binary execution

## 1. Packaged disk-backed app launch

This is the production path for `x64-desktop-disk`.

The syscall path in `src/os/kernel/ipc/syscall.spl` resolves packaged apps from the FAT32 disk through `resolve_disk_launch_entry(path)`. The launcher then uses manifest-backed metadata from `src/os/desktop/app_manifest.spl`.

Use this lane to prove:
- FAT32 mount
- launcher registration from manifests
- packaged app execution from disk-backed paths such as `/sys/apps/hello_world`

## 2. Resident-manifest fallback

This is transitional compatibility behavior, not the target production path.

Current examples:
- `src/os/kernel/loader/builtin_binary_registry.spl` still resolves `/sys/apps/browser_demo` and other legacy paths to resident entrypoints
- `src/os/services/launcher/launcher.spl` still contains Browser Demo seeded-shortcut fallback logic
- `src/os/desktop/shell.spl` still special-cases Browser Demo window seeding when a remote Browser Demo window appears
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` still has a Browser Demo local-fallback branch for the baremetal E2E lane

This path exists so old launch surfaces keep working while the launch stack is being retired or replaced.

## 3. True arbitrary x86_64 binary execution

This is the direct `native-build` ELF path.

The kernel resolves executable bytes through `resolve_executable_bytes(path, arch)` and then creates the task through `create_user_task(...)`. This is the right proof lane for `test/system/browser_engine_in_qemu_spec.spl` and similar x86_64 baremetal ELF tests.

Use this lane to prove:
- directly built x86_64 binaries boot and run
- the browser probe / browser software smoke lane is independent of Browser Demo packaging

## Remaining blockers after the arch and task-fix work

- Browser Demo is still not a pure packaged-app launch path; it is still reachable through resident-manifest fallback and shell seeding.
- The desktop E2E Browser Demo path still carries a test-only local fallback.
- The kernel-side x86_64 ELF execution path is no longer the blocker; the remaining work is to remove Browser Demo-specific fallback dependencies and let the packaged disk-backed route stand on its own.
