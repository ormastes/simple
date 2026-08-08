# SimpleOS POSIX / Dedicated-Host Interface Discovery Index

<!-- codex-architecture -->

Use this page as the first lookup for work that crosses pure-Simple POSIX
compatibility, host file mapping, startup argv handling, SimpleOS VFS loading,
or LLVM/Clang porting. It records the current repository locations; it does
not claim that the planned single dedicated-host facade has been implemented.

## Current, reusable pieces

| Concern | Canonical owner | Current meaning |
|---|---|---|
| Pure-Simple POSIX compatibility | `src/os/posix/mod.spl` and the sibling `*_compat.spl` / `*_async.spl` modules | Existing synchronous POSIX-shaped wrappers over SOSIX/IPC and kernel-owned facades. `posix_init()` is the initialization entry. |
| POSIX facility inventory | `src/os/posix/posix_server_contract.spl` | Existing profile/facility inventory and honest backing/status descriptions. |
| Startup policy and argv normalization | `src/app/startup/launch_metadata.spl` | Existing pure policy: launch kind, one `argv[0]`, parser/cache/dynlib inclusion, and host-mmap versus SimpleOS-prewarm strategy. It does not perform I/O. |
| Host file mapping | `src/lib/gc_sync_mut/io/file_ops.spl` and the corresponding IO facade exports | Existing host file/mmap helpers used by startup and loader paths. Use the facade, not direct runtime calls. |
| SMF mapping/cache | `src/compiler/99.loader/loader/smf_cache.spl`, `smf_cache_manager.spl`, `smf_mmap_native.spl` | Existing loader-owned file mapping and eviction lifecycle. |
| SimpleOS executable warmup | `src/os/services/vfs/vfs.spl`, `vfs_init.spl`, `src/os/kernel/loader/app_registry.spl`, and `src/os/services/launcher/launcher.spl` | Existing non-POSIX equivalent: VFS read-ahead/materialization and app-registry byte caching. Hover must not map or execute code. |
| SimpleOS libc mmap ABI | `src/os/libc/simpleos_libc.c`, `src/os/kernel/ipc/syscall_spm.spl`, and VM syscall modules | Existing `mmap`/`munmap` ABI surface is primarily anonymous/private; file-backed or writable shared mappings remain fail-closed by design. Do not describe this as a complete file-map provider. |

## LLVM/Clang port relationship

The LLVM port uses the SimpleOS sysroot and C runtime boundary, not a proven
call path into `src/os/posix/mod.spl`. Relevant owners are:

- `src/os/port/llvm/build.spl`, `build.shs`, `sysroot.shs`, and `README.md`;
- `src/os/toolchain/llvm/simpleos_cross_toolchain.cmake`;
- `src/os/libc/simpleos_crt0.S`, `simpleos_crt0_aarch64.S`, and
  `simpleos_libc.c`;
- `doc/07_guide/os/simpleos_llvm_toolchain.md` and
  `doc/00_llm_process/layer_expert/llvm_toolchain_port/skill.md`.

The POSIX/dedicated-host interface is a useful future portability boundary for
LLVM/Clang-hosted tools and their SimpleOS libc/sysroot dependencies. That
consumer integration is **planned/unverified**: current source inventory does
not prove that Clang or LLVM calls the pure-Simple POSIX facade, and current
toolchain documentation must not be read as in-guest link-and-run proof.

## Startup mmap/argv status

`doc/04_architecture/startup/simple_app_startup.md` is the detailed startup
architecture. Existing policy and checks include:

- `startup_normalize_program_args(...)` for direct script launches;
- `StartupLaunchPlan` and `mmap_hint` metadata;
- host mmap/cache selection versus `simpleos_vfs_prewarm`;
- `test/02_integration/app/startup_argparse_mmap_perf_spec.spl`;
- `test/03_system/app/simple/feature/simple_app_startup_spec.spl` and the
  SimpleOS counterpart;
- `scripts/check/check-startup-size-performance-audit.shs`.

The missing/recovery target is a single dedicated-host file-map/startup
facade with two providers: a POSIX/Linux implementation and a non-POSIX
SimpleOS implementation. The provider split, pre-main execution wiring, and
cross-platform live evidence are **planned/unverified** until implementation
and tests explicitly establish them.

## Bootstrap and evidence lookup

- Bootstrap gate schema: `doc/06_spec/bootstrap_test_gate.sdn`.
- Tracked TODOs and blockers: `doc/08_tracking/todo/todo_db.sdn` and
  `doc/08_tracking/bug/` (search `startup`, `mmap`, `posix`, `clang`, or
  `simpleos`).
- Bootstrap scripts: `scripts/bootstrap/`, `scripts/check/`, and the
  SimpleOS wrapper `scripts/check-simpleos-bootstrap-qemu.shs`.
- Never promote source presence, a skipped QEMU job, or a seed-built binary to
  pure-Simple or in-guest Clang PASS. Preserve evidence class and positive
  markers in reports.

## Search recipe for future agents

```text
dedicated host / POSIX: src/os/posix, posix_server_contract, host interface
startup map / argv: src/app/startup, launch_metadata, startup_argparse_mmap
SimpleOS map: vfs.preload_file_pages, app_registry, simpleos_libc mmap
LLVM/Clang: src/os/port/llvm, simpleos_llvm_toolchain, llvm_toolchain_port
bootstrap evidence: doc/06_spec/bootstrap_test_gate, doc/08_tracking/todo
```

