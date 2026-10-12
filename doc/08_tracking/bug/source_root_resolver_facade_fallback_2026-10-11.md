# Source-root resolver answers a module import with an ancestor package facade

- **Bug key:** `source-root-resolver-facade-fallback`
- **Date:** 2026-10-11
- **Introduced by:** `11fdfa806e7` (2026-10-10, "select CUDA composition and reject unsupported dynamic output")
- **Status:** fixed in source on `work/rel-p3-export-items-20261011`. Takes effect once stage 2 is rebuilt from a tree that contains the fix.
- **Kind:** logic regression in the driver's source closure. Not a native miscompile: it reproduces under the seed-interpreted harness.

## Symptom

Phase 3 (`native-build --source <composition> --source src/compiler --source src/app --source src/lib --entry-closure`, stage 2 built from `4182b2d01b5`) fails HIR with 18 shown errors and 7080 hidden by the cap. Evidence: `rel-p3run/p3c-llvm/build.log`.

- `module compiler.backend.codegen_types has no exported item CodegenOutputKind`, the same for `compiler.backend.native.mach_inst` (every imported name) and `compiler.mir_opt.mod`.
- `unresolved type: LlvmTypeMapper`, `LlvmVersionInfo`, `GpuBackendKernelPlan`, `GpuGenerated2DBackendCompileContract`, `PortableComputeCompilePlan`.
- `unresolved type: Predicate` in files under `src/compiler/70.backend/`.

## Root cause

`_driver_resolve_source_root_entry_import_v1` (`src/compiler/80.driver/driver_source_loading.spl`) is tried before the checkout resolver for every closure import. When the spelling is not a module under a `--source` root it stripped the last segment and retried, and returned `Found` for whatever it reached. The checkout resolver, which owns the layout rewrites the roots cannot see, never ran.

| import | resolver answer | correct file |
|---|---|---|
| `compiler.backend.codegen_types` | `70.backend/__init__.spl` | `70.backend/backend/codegen_types.spl` |
| `compiler.backend.native.mach_inst` | `70.backend/__init__.spl` | `70.backend/backend/native/mach_inst.spl` |
| `compiler.mir_opt.mod` | `60.mir_opt/__init__.spl` | `60.mir_opt/mir_opt/mod.spl` |
| `backend.env` (70.backend/backend.spl) | `70.backend/__init__.spl` | no module (unresolved, as before) |

The driver registers the import spelling as an alias of the file it resolved to, so `compiler.backend.codegen_types` named the facade surface. HIR then reports each named item as missing from it. The `unresolved type` errors are downstream: the type's declaring module was imported by its users through a misbound spelling (`use compiler.backend.llvm_type_mapper.{LlvmTypeMapper}`, `compiler.backend.llvm_version`, `compiler.backend.gpu_backend_metadata`, ...). The `Predicate` errors are also downstream: the facade pulled `70.backend/arch_rules.spl` into the closure, whose `use predicate.{...}` is a single-segment import the closure skips.

The primitive-name `[hir-reexport-chase-unresolved] ... item=i64|bool|text|Option` lines in the same log are stderr diagnostics, not fatal errors, and are unrelated.

## Fix

Two rules in the source-root resolver, both stated in comments at the code:

1. A root does not outrank the checkout by stripping. Once the checkout resolver resolves the current spelling exactly, the root resolver reports `Missing` and the fallback selects that file.
2. After stripping, a root may answer only with a module file (`use module.item`), never with `mod.spl` / `__init__.spl`.

A root still wins for a spelling that exists under it, so composition overrides are unchanged. The call site passes the importing directory through the new `_driver_resolve_source_root_entry_import_from_v1`; the two-argument function is kept for existing callers.

Also changed:

- `src/compiler/70.backend/arch_rules.spl` imports `compiler.common.predicate` / `compiler.common.predicate_parser` by full name.
- Both K1 composition entry points (`src/compositions/kernel_llvm*/compiler/driver/bootstrap_k1_selected.spl`) call `panic(...)` instead of bare `error(...)`. That was a separate bug from `270ab10e40a`: phase 3 reported `unresolved name: error` at lines 54 and 60. `error` in `std.common.error` only builds a value, so the old call did not abort on a failed admission either.

## Evidence

Seed `seed-head/simple.exe test`:

- `test/01_unit/compiler/driver/source_root_doubled_package_import_spec.spl`: 0/3 before the fix, 7/7 after.
- `test/01_unit/compiler/driver/source_root_composition_precedence_spec.spl`: 10/10 after (unchanged).

Census with the real resolver functions over every distinct `use` spelling in `src/{compiler,app,lib,plugins,compositions}` (9,649 spellings), phase-3 root order:

- 217 spellings on 908 import lines resolve differently after the fix. 100 spellings / 427 lines are `compiler.backend.*`, `compiler.blocks.*` and `compiler.mir_opt.mod`. The rest are `app.ui.*` and `app.dashboard.*` (dot-named directories) and a few `std.*` spellings, which matter for phase 4.

Stage-2 binary with the bug (`rel-p3run/frozen2`), phase-3 lane, source workaround applied (see below): 43 HIR fatals after 744 modules, against 319 fatals after 440 modules in the unpatched run. None of the three original classes remain.

Not verified: a phase-3 run on a stage 2 rebuilt with the fix.

## Open

- After the fix a root still outranks the checkout for 11 spellings (50 lines) that exist exactly under a root. One is the intended overlay. Seven have no checkout answer at all. Three change the selected file: `common.string_builder` -> `src/app/common/string_builder.spl` instead of `src/lib/common/string_builder.spl` (34 lines), `common.json`, `io.process_ops`. That is the ordered-root contract `11fdfa806e7` introduced; whether an ordinary `src/<name>` root should outrank the checkout's library precedence is for that change's owner.
- Residual classes in the workaround run, not explained here: `unresolved type: BlockId` in `60.mir_opt/{__init__,mir_opt_integration,optimizer_plugin}.spl` (also present in the unpatched run), and pattern errors in `35.semantics/perf/collection_plan.spl` and `50.mir/mir_verify.spl`.

## Temporary source workaround (stage-2 binaries that carry the bug)

`rel-p3run/workarounds/p3-export-items/apply.sh <tree>` rewrites the 100 affected compiler spellings to the doubled form the faulty resolver finds exactly (`compiler.backend.backend.X`, `compiler.blocks.blocks.X`, `compiler.mir_opt.mir_opt.mod`), and applies the `arch_rules.spl` and `panic` edits. It is mechanical and idempotent. The doubled spellings are valid for the seed and for a fixed stage 2, so the edits are harmless if left in, but they are tagged for removal:

```
# WORKAROUND(stage2:source-root-resolver-facade-fallback, BUG-pending): doubled-package imports spelled in full
```

It does not cover the `app.ui.*` dot-directory spellings: those have no alternative dotted form, so phase 4 needs the rebuilt stage 2.

Dropping `--source src/compiler` is not a workaround: the lane then fails on the entry module with other unresolved types. There is no flag or environment switch that disables the source-root-first order.
