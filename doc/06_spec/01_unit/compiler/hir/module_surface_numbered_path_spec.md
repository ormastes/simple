# Numbered editor module surface identity

Manual mirror of `test/01_unit/compiler/hir/module_surface_numbered_path_spec.spl`.
Source SHA-256: `43f34538d785d26ef5e75fb3783cbcaf945927af0b9b8ff091c6c11af718a666`.
Status: **UNRUN** for this source revision. This manual is hand-authored because the admitted Stage 2 binary exposes `native-build` but no SPipe doc generator. It records the executable assertions and does not claim a test pass.

## Purpose

A physical `src/lib/editor/00.common/types.spl` source must have the same logical HIR module name as `src/lib/editor/common/types.spl`. The original Stage 2 compiler reported missing exports for the numbered owner. A 33-module native-build probe reproduced those HIR failures; a separate diagnostic source tree with `00.common` renamed to `common` cleared the HIR failures and reached MIR. Both probes used 20 threads and a 6,835,937 KiB process-tree RSS ceiling. The renamed probe is diagnostic evidence, not a pass for this patch.

## Scenarios

1. **Numbered and plain editor paths:** `module_logical_name_from_path` returns `lib.editor.common.types` for both `00.common` and `common`; a Windows-style path has the same result.
2. **Prefix bounds:** a four-digit `0000.common` directory remains in the logical name, and the numeric file name `00.foo.bar.spl` remains `00.foo.bar` through construction, freeze, and registry lookup.
3. **One physical owner:** `ModuleSurfaceBuilder.add_parsed` retains the physical `00.common` path while construction and freeze both set logical/canonical names to `lib.editor.common.types` and package to `lib.editor.common`. `std.editor.common.types` and an alternate `std.editor.alias_types`/`lib.editor.alias_types` pair map to the same surface, which still contains `EditorBufferId`.
4. **Collision rejection:** a distinct `common/types.spl` physical source cannot claim the same `lib.editor.common.types` alias after the numbered source.

## Verification

Run the executable spec with an admitted self-hosted test runner. The Stage 2 compiler's `native-build` command can build a fixture but cannot execute SPipe scenarios. A later compiler build from this patch must rerun the retained editor fixture and show the editor import errors absent; this has not occurred yet.

Diagnostic logs: `review/editor_minimal/build_inrepo_cold.log` and `review/editor_minimal/build_unnumbered.log` under the preserved Cranelift concat967 output root. The baseline failed in HIR with direct missing exports. The renamed variant reached MIR and failed on separate `env_ops.spl` method errors, so no executable was run.
