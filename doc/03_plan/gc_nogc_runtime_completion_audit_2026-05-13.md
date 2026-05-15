# GC/No-GC Runtime Library Completion Audit

Date: 2026-05-13

## Objective Restatement

1. Make the Simple standard library surface available across async/no-GC and GC async runtime families where practical.
2. Keep the canonical sync/no-GC library surface complete on the other runtime configurations without forcing backend dependency direction through the wrong family.
3. Keep SimpleOS and POSIX-facing code as consumers of Simple backend libraries; portable Simple libraries must not depend on `os.*`, POSIX, Linux, or examples code.
4. Document the production contract and the remaining gates clearly.

## Prompt-to-Artifact Checklist

| Requirement | Evidence | Status |
|-------------|----------|--------|
| Full library surface on async/no-GC | `comm -23 nogc_sync_mut nogc_async_mut` reports `nogc_async_missing=0` | Complete for file availability |
| Full library surface on GC async | `comm -23 nogc_sync_mut gc_async_mut` reports `gc_async_missing=0` | Complete for file availability |
| Preserve async/GC family extras | Latest count reports `nogc_async_extra=267`, `gc_async_extra=227`; GC-only render bridge/pipeline/cache/shader modules were preserved | Complete |
| Avoid no-GC libraries depending on GC async | `test/unit/lib/dependency_boundary_spec.spl` now checks `nogc_sync_mut` and `nogc_async_mut` for direct `std.gc_async_mut` imports; test passes with 17 examples | Complete for direct import boundary |
| Avoid GC async depending on sync/no-GC | `test/unit/lib/dependency_boundary_spec.spl` now checks `gc_async_mut` for direct `std.nogc_sync_mut` imports; test passes | Complete for direct import boundary |
| Avoid noalloc depending on allocating runtime families | `test/unit/lib/dependency_boundary_spec.spl` checks `nogc_async_mut_noalloc` for direct imports from `nogc_sync_mut`, `nogc_async_mut`, `nogc_async_immut`, and `gc_async_mut`; test passes | Complete for direct import boundary |
| Avoid noalloc depending on app surfaces | `test/unit/lib/dependency_boundary_spec.spl` checks `nogc_async_mut_noalloc` for direct `app.*` imports; test passes | Complete for direct import boundary |
| Avoid noalloc allocation opt-in markers | `test/unit/lib/dependency_boundary_spec.spl` checks `nogc_async_mut_noalloc` for `@alloc` module annotations; test passes | Complete for marker-level regression |
| Avoid noalloc transitive imports through unsafe helper modules | `scripts/audit/noalloc_reachable_imports.py` computes the reachable import closure from `src/lib/nogc_async_mut_noalloc` and `test/unit/lib/dependency_boundary_spec.spl` fails if that closure reaches allocating runtime families, OS/app/example, POSIX/Linux, `@alloc`, or host allocation APIs | Complete for reachable import closure |
| Keep noalloc family checker-clean | Rebuilt bootstrap `simple check` over all 128 `src/lib/nogc_async_mut_noalloc/**/*.spl` files and all 128 `src/std/nogc_async_mut_noalloc/**/*.spl` files reports all checks passed | Complete |
| Restrict target presets to compatible runtime families | `src/compiler/70.backend/target_presets.spl` carries `allowed_families`; `preset_apply_compile_options()` writes `gc_off` and `allowed_families` into `CompileOptions`; resolver filtering is covered by `test/unit/compiler/module_resolver/allowed_families_spec.spl` | Complete for preset-to-resolver wiring |
| Remove conflicting compiler `GcMode` names | `src/compiler/00.common/gc_config.spl` is the only `enum GcMode:`; write-barrier algorithms use `GcStrategy`; guarded by `test/unit/compiler/semantics/gc_strategy_naming_spec.spl` | Complete |
| Mark GC async family with real root GC attribute | `src/lib/gc_async_mut/__init__.spl` now starts with `@gc`; Rust parser recognizes module-level `gc`; `parser/tests/gc_module_attribute.rs` verifies `@gc` before export-only roots; fresh bootstrap check accepts the root | Complete |
| Verify real semantic GC boundary warnings | `test/unit/compiler/semantics/gc_boundary_check_spec.spl` imports `check_gc_boundary_imports()` and covers no-GC->GC, noalloc->allocating, noalloc->GC, GC->no-GC, and neutral `common` imports | Complete for direct checker behavior |
| Surface GC boundary diagnostics through query lint | `src/app/cli/query_lint.spl` now invokes `check_gc_boundary_imports()` for runtime-family source files; `test/unit/app/cli/query_lint_gc_boundary_spec.spl` verifies JSON diagnostics for no-GC->GC and noalloc->allocating imports, plus no warning for `common` imports | Complete for query diagnostics surface |
| Surface GC boundary diagnostics through `simple check` | Rust `gc_boundary_crossing` lint is wired into `src/compiler_rust/driver/src/cli/check.rs` with only that lint enabled for `check`; driver tests cover warn/no-warn cases and rebuilt bootstrap smoke emits `warning[gc_boundary_crossing]` for a real no-GC->GC import file | Complete for `simple check` diagnostic surface |
| Guard interpreter GC boundary warning hook | `test/unit/compiler/interpreter/gc_family_boundary_hook_spec.spl` source-checks family extraction order, common-family skip, no-GC->GC warning, noalloc->allocating warning, and deduplication wiring | Complete for hook wiring |
| Surface GC boundary diagnostics through interpreter execution | Rust interpreter module loading now emits the same warning class for real no-GC->GC and noalloc->allocating import paths, including imported `src/std/<family>` modules; rebuilt bootstrap smoke emits one `[gc-warning]` before normal execution | Complete for interpreter execution diagnostic visibility |
| Portable libs must not depend on SimpleOS/POSIX/Linux | Boundary spec checks direct `os.*`, POSIX, and Linux namespace imports from `src/lib`; test passes | Complete for direct imports |
| Production OS code must not depend on examples | Boundary spec checks `src/os`, `src/app`, system specs, and tests for direct examples imports; test passes | Complete |
| Runtime family documentation | `doc/05_design/gc_nogc_module_parity.md`, `doc/04_architecture/runtime_family_stdlib_surface.md`, and `doc/04_architecture/runtime_family_support_matrix.md` updated with current counts and render/core ownership notes | Complete for current parity state |
| Parser/import health after mechanical GC rewrites | `find src/lib/gc_async_mut -type f -name '*.spl' ... src/compiler_rust/target/bootstrap/simple check` passes for 1625 files, including the real root `@gc` marker | Complete |

## Remaining Production Gaps

| Gap | Why It Still Matters |
|-----|----------------------|
| Compiler family enforcement is closed for current restricted-target entrypoints | Runtime-family root attributes now include both `@no_gc` and `@gc`; the manifest-backed checker, Rust `simple check`, target-aware test/native-cache execution, direct file execution, Rust/native_all native-build, and Simple-side target-preset resolution all have strict-family enforcement paths for baremetal/SimpleOS. New restricted-target module-loading entrypoints must declare which covered path they use before promotion. |
| Noalloc allocation checker is closed for current restricted-target gates | Direct noalloc imports from allocating runtime families, `app.*`, explicit `@alloc` markers, host allocation API calls, and unsafe reachable imports through helper modules are blocked by regression tests, target-strict `simple check`, the baremetal verifier, and the reachable-import audit; resolver manifests carry compiler-owned `AllocationCapability` metadata. Future restricted-target module-loading entrypoints should consume that metadata directly instead of bypassing the strict-check path. |
| SimpleOS direct POSIX imports remain inside `src/os` | This is acceptable for the current "libs must not depend POSIX" boundary, but replacing OS app/kernel direct POSIX calls with backend contracts would be a separate SimpleOS refactor. |

## Latest Verification

```text
find src/lib/gc_async_mut -type f -name '*.spl' -print0 | xargs -0 src/compiler_rust/target/bootstrap/simple check
=> All checks passed (1625 file(s))

src/compiler_rust/target/bootstrap/simple test test/unit/lib/dependency_boundary_spec.spl --mode=interpreter
=> Passed: 18, Failed: 0

src/compiler_rust/target/bootstrap/simple test test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl --mode=interpreter
=> Passed: 7, Failed: 0

bin/simple test test/unit/compiler/semantics/gc_strategy_naming_spec.spl --mode=interpreter
=> Passed: 2, Failed: 0

bin/simple test test/unit/compiler/semantics/gc_boundary_check_spec.spl --mode=interpreter
=> Passed: 6, Failed: 0

bin/simple test test/unit/compiler/interpreter/gc_family_boundary_hook_spec.spl --mode=interpreter
=> Passed: 5, Failed: 0

bin/simple test test/unit/app/cli/query_lint_gc_boundary_spec.spl --mode=interpreter
=> Passed: 3, Failed: 0

bin/simple test test/unit/app/cli/query_diagnostics_spec.spl --mode=interpreter
=> Passed: 6, Failed: 0

bin/simple run src/app/cli/query.spl query check src/lib/nogc_sync_mut/.gc_boundary_query_smoke.spl --format json
=> emitted one `gc_boundary_crossing` diagnostic for `use std.gc_async_mut.task`; temporary smoke file removed after run

cargo test -p simple-compiler gc_boundary -- --nocapture
=> Passed: 4, Failed: 0

cargo test -p simple-driver --lib test_check_ -- --nocapture
=> Passed: 7, Failed: 0

cargo check -p simple-driver
=> passed

cargo fmt --check
=> passed

cargo build --profile bootstrap -p simple-driver
=> passed

find src/lib/nogc_async_mut_noalloc -type f -name '*.spl' -print0 | xargs -0 src/compiler_rust/target/bootstrap/simple check
=> All checks passed (128 file(s))

find src/std/nogc_async_mut_noalloc -type f -name '*.spl' -print0 | xargs -0 src/compiler_rust/target/bootstrap/simple check
=> All checks passed (128 file(s))

src/compiler_rust/target/bootstrap/simple check src/lib/nogc_async_mut_noalloc/log src/std/nogc_async_mut_noalloc/log src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl
=> All checks passed (9 file(s))

src/compiler_rust/target/bootstrap/simple test test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl --mode=interpreter
=> Passed: 22, Failed: 0; legacy inline asm warnings remain in baremetal semihost/system API files

python3 scripts/audit/noalloc_reachable_imports.py
=> noalloc reachable import closure is restricted to nogc_async_mut_noalloc/common

src/compiler_rust/target/bootstrap/simple test test/unit/lib/dependency_boundary_spec.spl --mode=interpreter
=> Passed: 18, Failed: 0

src/compiler_rust/target/bootstrap/simple test test/unit/compiler/verify/baremetal_noalloc_constraints_spec.spl --mode=interpreter
=> Passed: 7, Failed: 0

src/compiler_rust/target/bootstrap/simple run src/compiler/90.tools/verify/baremetal.spl
=> PASS: all infrastructure files present; noalloc source constraints all OK, including unsafe reachable imports

src/compiler_rust/target/bootstrap/simple check src/lib/nogc_sync_mut/.gc_boundary_compile_smoke.spl
=> emitted `warning[gc_boundary_crossing]` for `use std.gc_async_mut.task`; temporary smoke file removed after run

cargo test -p simple-compiler gc_boundary_warning_message -- --nocapture
=> passed 3 interpreter module-loader warning-message tests

src/compiler_rust/target/bootstrap/simple run src/lib/nogc_sync_mut/.gc_boundary_interpreter_smoke.spl
=> emitted one `[gc-warning] GC module 'std.gc_async_mut' ... imported in no-GC context ...`, then printed `ok`; temporary smoke file removed after run

cargo check -p simple-parser
=> passed

cargo build --profile bootstrap -p simple-driver
=> passed

cargo test -p simple-parser parse_gc_module_attribute_before_export_only_root
=> Passed: 1, Failed: 0

cargo test -p simple-parser packed_struct
=> Passed: 3, Failed: 0

src/compiler_rust/target/bootstrap/simple check src/lib/gc_async_mut/__init__.spl
=> passed

env SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/debug/simple os test --scenario=riscv64-virtio-fat32-smf
=> QEMU boot passed; serial output included FS_MOUNT_OK, SMF_DISCOVERY_OK, SMF_CLI_LAUNCH_OK, SMF_WM_GUI_LAUNCH_OK, SIMPLEOS_RISCV_SMF_FS_PASS, TEST PASSED

env LLVM_SYS_180_PREFIX=/usr src/compiler_rust/target/debug/simple os test --arch=riscv64
=> QEMU boot passed on the default riscv64 arch path after rebuilding the Rust driver with the LLVM feature; serial output included FS_MOUNT_OK, SMF_DISCOVERY_OK, ELF_LOAD_OK arch=riscv64, SMF_CLI_LAUNCH_OK, SMF_WM_GUI_LAUNCH_OK, NATIVE_GUI_PROCESS_RENDER_OK, SIMPLEOS_RISCV_SMF_FS_PASS, and TEST PASSED

env LLVM_SYS_180_PREFIX=/usr src/compiler_rust/target/debug/simple os test --all
=> One-shot SimpleOS boot matrix passed: x86_64, x86_32, riscv64, riscv32, arm64, and arm32 all reported PASS; final summary was Results: 6 passed, 0 failed

src/compiler_rust/target/debug/simple test test/feature/usage/cuda_spec.spl --mode=interpreter --clean --force-rebuild
=> Passed: 5, Failed: 0 on a host with NVIDIA RTX A6000 and TITAN RTX visible via nvidia-smi

src/compiler_rust/target/debug/simple test test/feature/scilib/cuda_device_buffer_spec.spl --mode=interpreter --clean --force-rebuild
=> Passed: 20, Failed: 0; covers explicit CUDA buffers, CUDA-owned NDArray storage, device-side arithmetic, shape/combine operations, reductions, and slicing on the same CUDA host

src/compiler_rust/target/debug/simple os test --help
=> Not a help-only path; attempted the default x86_64 Cranelift OS build and failed before QEMU because Ring's vendored curve25519.c requires missing third_party/fiat/curve25519_64.h and the link still had unresolved rt_typed_words_u64_push / rt_typed_words_u64_set

env SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/debug/simple os test --arch=x86_64
=> QEMU boot passed after restoring the vendored Ring fiat headers and adding freestanding rt_typed_words_u64_push / rt_typed_words_u64_set wrappers; serial output included [stage1] PASS: Kernel boot + PCI scan and TEST PASSED

env SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/debug/simple os test --scenario=arm64-virtio-fat32-smf
=> QEMU boot passed: ARM64 now links with the freestanding runtime helpers, boots VirtIO-BLK FAT32 media, preserves raw fixture lengths that can look like tagged integers, accepts the one-byte padded LLVM/Rust SMF fixture reads, reads ELF-backed SMF bytes for hello/simple_compiler/simple_interpreter/simple_loader/llvm/clang/rust, registers process pids for those apps, emits the required simple_compiler/simple_loader/clang/rust process-backed and VFS read markers, and reaches guest TEST PASSED

env SIMPLE_OS_BUILD_BACKEND=llvm LLVM_SYS_180_PREFIX=/usr src/compiler_rust/target/debug/simple os test --scenario=arm32-virtio-fat32-smf
=> QEMU boot passed after rebuilding the Rust driver with the LLVM feature and removing freestanding VFS/FAT32 dependence on common.string_core.str_char_at; serial output included process-backed and VFS read markers for hello_world/simple_compiler/simple_interpreter/simple_loader/llvm/clang/rust and TEST PASSED

env SIMPLE_OS_BUILD_BACKEND=llvm LLVM_SYS_180_PREFIX=/usr src/compiler_rust/target/debug/simple os test --scenario=riscv32-virtio-fat32-smf
=> QEMU boot passed after rebuilding the Rust driver with the LLVM feature; serial output included FS_MOUNT_OK, SMF_DISCOVERY_OK, ELF_LOAD_OK arch=riscv32, SMF_CLI_LAUNCH_OK, SMF_WM_GUI_LAUNCH_OK, NATIVE_GUI_PROCESS_RENDER_OK, SIMPLEOS_RISCV_SMF_FS_PASS, and TEST PASSED

bin/simple test test/unit/compiler/driver/compile_options_normalization_spec.spl --mode=interpreter
=> Passed: 10, Failed: 0

bin/simple test test/unit/compiler/module_resolver/allowed_families_spec.spl --mode=interpreter
=> Passed: 3, Failed: 0

bin/simple test test/unit/compiler/target_presets_spec.spl --mode=interpreter
=> Passed: 23, Failed: 0

Global parity:
nogc_async_missing=0
gc_async_missing=0
nogc_async_extra=267
gc_async_extra=227
```
