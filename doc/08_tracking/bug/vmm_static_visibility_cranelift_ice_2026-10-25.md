# vmm_vma / vmm_copy / vmm_address_space: Cranelift ICE on private vmm statics

- **Status:** fixed at the source (permanent, not a workaround).
- **Found:** Phase 3 run-27e (worktree `simple-p3fix-r27`, HEAD `d3fc04205cf`),
  `[ERROR] 3 module(s) failed with ICE: os.kernel.memory.vmm_address_space,
  os.kernel.memory.vmm_copy, os.kernel.memory.vmm_vma (codegen, caught)`.

## Symptom

The receipt and the driver only say
`backend AOT diagnostic payload was not a readable text value (len=-1)`.
The real error is the line printed just before each failure:

```
[cranelift] imported non-public module static 'os_kernel_memory_vmm__PTE_WRITABLE' requires visibility-preserving accessor support
[cranelift] imported non-public module static 'os_kernel_memory_vmm__g_next_as_id' requires visibility-preserving accessor support
[cranelift] imported non-public module static 'os_kernel_memory_vmm__PTE_USER' requires visibility-preserving accessor support
```

(`declare_module_statics`, `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`.)
Each module reports only its first offender.

## Root cause

`src/os/kernel/memory/vmm.spl` declared no `pub` items at all. Its split-out
siblings import its `PTE_*`/`VMM_*`/`PAGE_SIZE` constants and the `g_vmm` /
`g_next_as_id` globals. Under the language rule (private = same file only;
the decision is in `cranelift_private_static_cross_module_2026-10-24.md`), those
imports are illegal, so the backend is right to reject them. Private *literal*
initializers (`4096`, `0xFFFF...`) are inlined by `provider_globals.spl`
and slip through. Computed ones (`1 << n`) and every `var` become external
statics and fail.

## Fix

Every vmm.spl `val`/`var` that another file imports (20 names, every
`@cfg` variant of `VMM_KERNEL_SPACE_START`) is now `pub`. The set was computed
from all 29 `use os.kernel.memory.vmm.{...}` importers, not only the
three failing modules. Private functions imported cross-file (`_read_pte`,
...) are left unchanged: the adapter does not reject them, and they are out
of scope here.

Spec: `test/01_unit/os/kernel/memory/vmm_static_visibility_spec.spl`. It is a
source-shape check and does not native-build.

## Why the kernel is in the compiler closure (not cut)

`bootstrap_main` -> `app.io._CliCompile.compile_targets` ->
`native_runtime_provider_config_v1` ->
`nogc_sync_mut.database.pure_sql.bitmap_provider_selection_config_v1` (and
`bitmap_provider_v1`) -> `os.smf.provider_loader` -> `os.posix.dynlib` ->
`os.posix.dylib_async` -> `os.kernel.loader.dylib_registry` ->
`os.kernel.loader.elf64` -> `os.kernel.memory.vmm` (+ siblings). That is 26 kernel
modules in run-27e. `os.smf.host_target` does not pull in the kernel.

The pull is by design. `os.posix.dynlib` is the unified facade, and its SMF
arm routes to the kernel-owned registry. `provider_loader` admits
`artifact_kind: "smf"` as well as `"native"`. The bitmap config passes only
`"native"`, so that SMF arm is dead *for that caller*, but nothing makes it dead
statically. Cutting the chain would need a host-only dynlib facade without the
SMF arm. That is a design change, filed here as an open follow-up and not made in this
fix. The other 23 kernel modules compile, so they are not blocking.

## Diagnostic len=-1 (not fixed)

The payload loss is the existing class
`stage2_aot_error_message_lost_invalid_heap_2026-09-06.md`.
`declare_module_statics` reports failure through a sentinel dict key and
`print`s the text, so no message string reaches `backend_aot_write_diagnostic`.
Carrying the text would mean threading it through the statics result. That is a
compiler change that needs a Stage 2 rebuild, so it is out of scope for this source fix.

## Original release/1.0.0 verification (2026-10-25, Stage 2 p2shard-17, cranelift, aarch64)

The test was a tiny entry importing `os.kernel.memory.{vmm,vmm_vma,vmm_copy,vmm_address_space}`
with `--source src/os` and a 22-module closure.
- Red (pre-fix vmm.spl): rc=1, `3 module(s) failed with ICE` on the same three modules.
- Green (fix): rc=0, 22/22 compiled and linked. Every one of the 34
  `os.kernel.memory.vmm.*` / `__simple$global_address$v1$os_kernel_memory_vmm__*`
  undefined references in the three consumer objects is defined by the new `vmm.o`.
- `os.kernel.memory.vmm` itself must be rebuilt. The run-27e cached vmm object
  defines 0 `global_address` accessors, because they are emitted only for `pub` statics.

## Port to release_phase3

Port base: `ec223ca1f1e0a14ff09fd0d15b1c1349e153f859`. The provider file
on this base is byte-identical to the parent of the original fix
`dd919a7ceacb0af59f14551de49ff1fc8b1587ae`; the 25 visibility declarations
apply without semantic conflict. The associated source-shape spec comes from
`f8ba8546fa3214afdcd6630eb037638f5bce7646` (release/1.0.0 PR #4549).

The original native results above belong to that earlier build lineage.
This port checks unchanged declaration values, visibility coverage, diff
whitespace, direct-env guards, and executable-spec layout. It does not claim
new native compilation, SSpec execution, or a Phase 3 pass. The available
`simple-p3fix-cltest` candidate has a successful Stage 2 sanity receipt but its
`phase2-compatibility.manifest.not-published` remains unpublished after the
qualification was terminated. No source-matched admitted producer for this
port base is established.

The next qualified compile must rebuild the provider `vmm.spl` together with
`vmm_copy.spl`, `vmm_address_space.spl`, and `vmm_vma.spl`, using a private
cache. Reusing the old private provider object would leave the consumer
accessor references unresolved even after this source correction.
