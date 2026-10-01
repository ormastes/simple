# SimpleOS Cortex-M policy objects export mangled symbols; `simpleos_stm32u585.elf` cannot link

**Status:** FIXED 2026-09-26 (root cause in compiler; see Resolution)
**Found by:** `sh scripts/os/run_simpleos_stm32u585.shs --build-only` after the
native-build SIGILL fix (`native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`).
**Oracle:** `sh scripts/check/check-cm33-scalar-parser-fs-object.shs stm32u585 <object>`
(pins the exact 11-symbol external surface, incl. the module initializer).

## Symptom

Both policy objects build for `thumbv8m.main-none-eabi`, but the link fails
with 12 undefined symbols referenced by `cm33_shim.c`. `llvm-nm` on
`scalar_parser_fs_policy-thumbv8m.main-none-eabi.o` shows the definitions
exist under the wrong names:

```
T os.kernel.arch.cortex_m33.scalar_parser_fs_policy.cm33_policy_fs_add_file
T __module_init__home_yoon_simple_build_scv_snapshots_scv_revision_v1_<sha>_src_os_kernel_arch_cortex_m33_scalar_parser_fs_policy_spl_dynamic
```

The 2026-09-19 ELF linked with plain `cm33_policy_fs_add_file` and plain
`__module_init_src_os_kernel_arch_cortex_m33_scalar_parser_fs_policy_spl_dynamic`.

## Root cause — two independent defects

1. **`@export("C")` never reached HIR through the flat-AST bridge.** The
   parser only carries the asm-placement decorator subset into the flat decl
   pool (`parser_pending_asm_placement`, `enum_module_body.spl`: naked /
   section / align / global / noreturn / entry / interrupt), and
   `convert_nodes.spl` rebuilds `fn.attributes` only from that subset plus
   rt/gpu/hardware/generic/clocked. `export(...)` was dropped, so
   `HirFunction.has_export_attr` was always false. This was masked until
   `59cba6907ad` (2026-09-22, "preserve provider class identity across HIR
   and MIR") replaced `function_names.push(func.name)` with
   `mir_provider_function_name(...)`, which module-qualifies every function
   that is not extern / exported / global / entry / `main` — so every C-ABI
   export became `os.kernel.arch.cortex_m33.<module>.<fn>`.
2. **`__module_init_*` was derived from the raw parsed path.**
   `mir_dynamic_module_init_name` sanitized `module.name`, which under
   `SIMPLE_BOOTSTRAP=1` is the parsed PATH. With `SIMPLE_SCV_FREEZE_FALLBACK=1`
   (`native_build_closure.spl` `_nb_scv_snapshot_path_v1`) the entry is
   parsed from `build/scv_snapshots/scv_revision_v1_<sha>/src/...`, so the
   symbol embedded the host directory and a content hash and could never
   match the fixed name the shim declares.

## Resolution

- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` —
  `parser_pending_asm_placement` admits `export(...)` (it fixes the symbol's
  linkage name, same class as `global`).
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` — rebuilds
  `export(C,name:sym)` as `Attribute("export", [StringLit("C"),
  Assign(Ident("name"), StringLit("sym"))])`, the shape `parse_export_attrs`
  already consumes.
- `src/compiler/00.common/module_path_naming.spl` — new
  `module_source_relative_path` (the prefix-stripping half of
  `module_logical_name_from_path`, now shared): any spelling of a source
  path (worktree, SCV snapshot, `./`, `../`) collapses to `src/...`.
- `src/compiler/50.mir/_MirLowering/module_lowering.spl` —
  `mir_dynamic_module_init_name` derives from that repo-relative path.

Not changed: `cm33_shim.c`, the object gate's expected symbol set.
Left as-is (local `b` symbols, not part of the ABI): the module's `.bss`
globals `g_<raw path>_<NAME>` still embed the snapshot path; they link fine
but make objects non-reproducible across hosts. Follow-up if reproducible
objects are wanted: route `runtime_global_owner` in
`lower_runtime_module_initializers_named` through the same helper after
checking every reader of the static name.

## Specs

- `test/01_unit/compiler/hir/export_attr_survives_flat_bridge_spec.spl` —
  parse -> HIR keeps `has_export_attr` / `export_name`; MIR symbol stays
  plain in a non-entry provider module while the unexported sibling is still
  qualified.
- `test/01_unit/compiler/mir/module_init_symbol_repo_relative_spec.spl` —
  snapshot path and repo path yield the same `__module_init_*` name.
- `test/01_unit/compiler/common/module_path_naming_spec.spl` — new
  `module_source_relative_path` cases plus the snapshot-path logical name.
- Object gate: `scripts/check/check-cm33-scalar-parser-fs-object.shs` (unchanged).
