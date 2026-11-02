# stage2_facade_sdn_leaf_method_mangling_2026-11-02

- Status: **fixed in current source** (waf-5); frozen stage2 still affected -> revert-ready after stage3 self-build
- Severity: P1 (undefined `SdnBackendImpl.process_module` at link)
- Related: `stage2_native_build_run_fn_undefined_reference_link_failure_2026-08-08.md`,
  `bootstrap_default_len_is_empty_not_materialized_2026-07-13.md` (defsym aliases),
  `mir_facade_mirlowering_silent_unresolved_import_2026-09-01.md`

## Symptom

`src/compiler/80.driver/driver.spl` imports `SdnBackendImpl` via the facade `compiler.backend.sdn`; the type is
defined in `src/compiler/70.backend/backend/sdn.spl` (logical `compiler.backend.backend.sdn`). Callers emitted
`compiler.backend.backend.SdnBackendImpl.process_module` / `.create`; the definer emits
`compiler.backend.backend.sdn.SdnBackendImpl.process_module`.

## Root cause

Not the facade itself: the module's leaf is literally `sdn`. Imported impl methods are named
`"{owner_module}.{Type}::{method}"` with `owner_module = hir_module_logical_name_from_path(defining_module)`
(`module_reexport_materialization.spl`). For an imported symbol `defining_module` is already the dotted logical
name, and `module_logical_name_from_path` (`src/compiler/00.common/module_path_naming.spl`) stripped a trailing
`.sdn` as if it were a file extension, so `compiler.backend.backend.sdn` became `compiler.backend.backend`. The
MIR link registry key (`compiler.backend.backend.sdn#SdnBackendImpl.process_module`) then missed and the raw
mis-qualified symbol name was emitted. Any module whose leaf is `sdn` (or matches the `.sdn` suffix) was hit.

## Fix

`.sdn` is stripped only when it is a file suffix: the text has a path separator, or the stem has no dot
(`app.sdn`). A dotted logical name keeps its `sdn` leaf.

## Evidence

- `test/01_unit/compiler/50.mir/generic_selfcall_facade_symbols_spec.spl` facade scenarios (both
  `compiler.backend.*` and neutral `app.*` paths): red before (target `...backend.SdnBackendImpl.process_module`
  missing), green after.
- `test/01_unit/compiler/common/module_path_naming_spec.spl`: new `sdn` leaf case; existing `.sdn` file
  extension cases unchanged.

## Revert condition

Stage-2 form (`driver.spl` importing from the defining module, or defsym aliases) stays until a stage3 built from
this fix links `SdnBackendImpl.process_module` without them.

## Phase-3 stage3 link evidence (lane A, 2026-11-02)

The manual stage3 link (`C:/dev/p3new/linkdry`, `@link3.rsp`, 1414 objects) reported
`undefined symbol: compiler.backend.SdnBackendImpl.process_module`, referenced by `CompilerDriver.process_sdn`
and `compiler.driver.driver_types.__lambda_lift_9`, while the definer emits
`compiler.backend.sdn.SdnBackendImpl.process_module`. Lane A first guessed that the facade re-export path was used
for mangling; the leaf-strip root cause above explains the same symptom. A static scan of all 1414 objects found
only this one symbol with a missing module segment.

Link workaround: lld's MinGW driver rejects `--defsym` on COFF, so the link uses
`-Wl,-Xlink=-alternatename:compiler.backend.SdnBackendImpl.process_module=compiler.backend.sdn.SdnBackendImpl.process_module`
(passed through `P3_LINK_EXTRA_ARGS` in `scripts/bootstrap/p3-manual-link-stage3.shs`). Undefined count went from 12 to 11.
