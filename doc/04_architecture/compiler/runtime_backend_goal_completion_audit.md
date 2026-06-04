# Runtime Backend Goal Completion Audit

Updated: 2026-05-15

## Objective

Refactor Simple libraries toward an async/no-GC backend architecture:

1. Libraries depend on async/no-GC backend libraries where behavior permits.
2. Sync and GC variants exist where needed and are backed by async/no-GC or lower no-GC backend owners instead of duplicating runtime hooks.
3. SimpleOS and portable library layers do not depend on POSIX except explicit platform/Linux/POSIX compatibility layers.
4. The production architecture is documented and guarded by repeatable checks.

## Prompt-to-Artifact Checklist

| Requirement | Artifact or command | Evidence |
| --- | --- | --- |
| Async/GC compatibility surfaces depend on no-GC backends where behavior permits | `scripts/audit/runtime_backend_boundaries.py`; `doc/04_architecture/compiler/runtime_backend_completion_audit.md` | `async_compat_direct_runtime_hook_count=0`, `exact_duplicate_runtime_hook_count=0`, `gc_async_runtime_owner_wildcard_facade_count=0`, and `nogc_async_runtime_owner_wildcard_facade_count=0`. |
| No-GC families do not depend upward on GC compatibility families | `scripts/audit/runtime_backend_boundaries.py` | `nogc_family_forbidden_gc_import_count=0`. |
| Sync and GC facade families are backed by async/no-GC surfaces instead of independent runtime-hook owners | `src/lib/gc_sync_mut`, `src/lib/gc_async_immut`, `src/lib/gc_sync_immut`, `src/lib/nogc_sync_immut`; `scripts/audit/runtime_backend_boundaries.py` | `sync_compat_direct_runtime_hook_count=0` and `sync_compat_facade_mirror_violation_count=0`. |
| Async compatibility families have no placeholder bodies | `scripts/audit/runtime_backend_boundaries.py` | `async_compat_pass_todo_count=0`. |
| SimpleOS lower layers do not import POSIX/libc compatibility modules | `scripts/audit/runtime_backend_boundaries.py` | `simpleos_lower_layer_posix_libc_import_count=0` for `src/os/kernel`, `src/os/drivers`, `src/os/services`, `src/os/sosix`, `src/os/userlib`, and `src/os/async`. |
| Portable library roots do not import POSIX/Linux outside explicit compatibility/platform owners | `scripts/audit/runtime_backend_boundaries.py` | `portable_lib_forbidden_posix_linux_import_count=0`. |
| Portable library roots do not import SimpleOS/kernel/driver/service layers directly | `scripts/audit/runtime_backend_boundaries.py` | `portable_lib_forbidden_os_import_count=0`. |
| Restricted targets admit only compatible families | `src/compiler/70.backend/target_presets.spl`; `src/compiler/99.loader/module_resolver/resolution.spl`; `test/01_unit/compiler/module_resolver/allowed_families_spec.spl` | Target presets carry `allowed_families`; resolver filters stdlib family subdirectories when restrictions are active. |
| Noalloc capability is compiler-owned metadata | `src/compiler/99.loader/module_resolver/types.spl`; `src/compiler/99.loader/module_resolver/manifest.spl`; `test/01_unit/compiler/module_resolver/allocation_capability_manifest_spec.spl` | `DirectoryManifest` and `ChildModule` store `AllocationCapability`; manifests infer noalloc family roots and honor `@no_alloc` / `@alloc`. |
| Target-restricted execution promotes family violations to hard errors | `src/compiler_rust/driver/src/cli/basic.rs`; `src/compiler_rust/driver/src/cli/test_runner/*`; `src/compiler_rust/driver/src/cli/native_build.rs`; `src/compiler_rust/native_all/src/lib.rs` | Rust check/test/direct-file/native-build paths enable strict runtime-family mode for baremetal/SimpleOS targets; focused unit test covers SimpleOS vs hosted behavior. |
| Facade families have behavior coverage | `test/01_unit/lib/{gc_sync_mut,gc_async_immut,gc_sync_immut,nogc_sync_immut}/facade_resolution_spec.spl`; immutable native probe specs listed in `runtime_backend_completion_audit.md` | Interpreter facade resolution passes; native immutable facade smoke covers coordination and persistent collections. |
| SimpleOS boot/runtime path remains covered | `doc/04_architecture/compiler/runtime_backend_completion_audit.md` | Recorded one-shot `simple os test --all` evidence passes x86_64, x86_32, riscv64, riscv32, arm64, and arm32 with `Results: 6 passed, 0 failed`. |
| Architecture documentation is current | `doc/04_architecture/runtime/runtime_family_support_matrix.md`; `doc/04_architecture/compiler/runtime_backend_completion_audit.md` | Family ownership, loader order, strict target policy, SimpleOS POSIX boundary, facade routing policy, and maintenance gates are documented. |

## Completion Judgment

The current implementation satisfies the requested architecture for existing runtime families and entrypoints. Remaining notes are maintenance gates for future modules: keep boundary audits at zero, keep facade/native smoke in CI, and require new restricted-target module-loading paths to document strict-family and allocation-capability enforcement before promotion.
