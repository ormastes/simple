# BUG: @cfg multi-variant function mis-dispatch on x86_64-unknown-none native-build

**Status:** fixed (2026-07-10)
**Severity:** high (silently routes to the wrong architecture's implementation)
**Component:** compiler native-build `@cfg` resolution (Cranelift, `x86_64-unknown-none`)
**Found:** 2026-07-10 (during the SimpleOS SSH → ring-3 exec demo)

## Symptom

A function defined once per architecture via `@cfg(...)` (six same-named variants,
compiled as `<name>$dup0..dup5`) is called from a wrapper, and the WRONG variant is
selected on the `x86_64-unknown-none` build.

Two independent reproductions in `src/os/kernel/loader/fs_exec_spawn.spl`:

1. `_fs_exec_spawn_ring3_active` — the `@cfg(x86_64)` variant calls
   `x86_64_fs_exec_spawn` (FAT + ring-3 handoff). At runtime the wrapper
   `fs_exec_spawn_ring3` instead reached the `@cfg(x86)`/riscv variant that calls
   `fs_exec_spawn` → `fs_exec_spawn_as` → `g_vfs_read_executable_bytes`. Proof: the
   serial log shows `[vfs-read] …` (only reachable via `fs_exec_spawn_as`) while the
   intended `x86_64_fs_exec_spawn_as` (its unique `spawn:preloaded`/`preload-check`
   prints) is never hit.
2. A fresh helper `_fs_exec_spawn_ring3_preloaded_active` with the same 6-variant
   `@cfg` shape returned `-16` (a non-x86_64 stub body) instead of calling the
   `@cfg(x86_64)` body.

## Root cause (confirmed)

The native-build pipeline (`src/compiler_rust`) never evaluated per-declaration
`@cfg(<arch>)` at all. All six same-named variants survived into one compilation
unit; because they share a signature the `$dupN` overload path is skipped
(`mir/lower/lowering_core.rs`: `sigs.iter().all(|s| s == &sigs[0])`), and
`declare_functions` (`codegen/shared.rs:82`) keeps whichever is declared **FIRST**
and silently skips the rest. First-wins is source-order, not target-aware: any
target whose variant is not written first is mis-dispatched. (The `x86` token
theory was wrong — the whole-file `file_arch_cfg_gate` never applies to a
multi-arch file, so no per-decl arch selection ran.)

## Fix

`native_project/discovery.rs::strip_inactive_cfg_arch_fns` drops top-level
`@cfg(<arch>)`-gated function items whose arch does not match `effective_target()`,
called after parse in `compiler.rs::compile_file_to_object` (codegen path) and in
`imports.rs::build_import_map` (symbol/arity maps). Only recognized arch aliases
(and `not(<arch>)`) gate; `test`/`baremetal`/`("key","value")` cfgs are left
untouched, mirroring `parser_preprocessor.spl`. Unit test:
`native_project::tests::test_strip_inactive_cfg_arch_fns_keeps_only_target_variant`.
The `x86_64_fs_exec_spawn` workaround in `src/os/apps/sshd/sshd.spl` was reverted
to the `fs_exec_spawn_ring3` wrapper; the merged x86_64 kernel links a single
`_fs_exec_spawn_ring3_active` that tail-calls `x86_64_fs_exec_spawn`.

## Workaround (no longer needed — fixed at root)

Call the single, non-`@cfg`, `pub` target function directly (e.g.
`x86_64_fs_exec_spawn(...)`), bypassing the `@cfg` dispatch helper. Unambiguous
symbol → correct target. (Downside: caller must be arch-specialized or guarded.)

## Repro / fix pointer

Minimize: a wrapper calling a 6-`@cfg`-variant helper where the `x86_64` variant
calls fn A and another variant calls fn B; build `--target x86_64-unknown-none
--backend cranelift`; observe B runs. Fix in native-build `@cfg` token activation /
variant selection so `x86_64` targets bind the `@cfg(x86_64)` variant.

## Related

- `doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md` (bug #4 there)
