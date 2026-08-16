# SCV and Rendering File-Read Coverage Feature Expert

## Role

Own feature-specific knowledge for the **byte contract of the canonical
file-read APIs** in `src/lib/nogc_sync_mut/io/file_ops.spl`, and for how the two
big consumer families — SCV (`src/lib/scv/**`) and the font/rendering path —
depend on it. Scope is byte fidelity of the read entry points, not SCV
versioning semantics and not renderer behavior.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- System-test plan (REQ-IOREAD-001..006, design authority): [doc/03_plan/sys_test/scv_render_file_read_coverage.md](../../../03_plan/sys_test/scv_render_file_read_coverage.md)
- Guide: [doc/07_guide/lib/io/file_read_byte_contracts.md](../../../07_guide/lib/io/file_read_byte_contracts.md)
- Authored mirror: [doc/06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md](../../../06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md)
- Executable spec: `test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl`
- Definition-count guard (byte family): `test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl`
- Tracking record (text family, OPEN): [doc/08_tracking/bug/file_read_has_23_definitions_with_two_return_types_2026-08-16.md](../../../08_tracking/bug/file_read_has_23_definitions_with_two_return_types_2026-08-16.md)
- Tracking record (byte family, signatures unified): `doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`
- Blocking record (no runtime): [doc/08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md](../../../08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md)

## What a new agent must know first

1. **There are many same-named readers.** `file_read_bytes` has four
   definitions; `file_read` has 23 across two return types. Before changing any
   `file_read*` signature, grep the whole tree — the toolchain surfaces only the
   pair that collides in the closure it happened to compile, so a clean run is
   not evidence of a single definition.

2. **The canonical shapes, since 2026-08-16.** `file_read_bytes -> [u8]` is
   canonical. `file_read_bytes_i64 -> [i64]` exists for SCV and
   `cache_validator` only. New code uses the `[u8]` form.

3. **SCV and rendering read through different definitions.** SCV imports
   `file_read_bytes_i64` from `io.file_ops` and narrows with the module-local
   `scv_i64_bytes_to_u8` (27 call sites, 10 modules). The font path
   (`io/font_sffi.spl`, `sffi/spl_fonts.spl`, `text_layout/font_renderer.spl`)
   imports `file_read_bytes` from `std.nogc_sync_mut.sffi.io`, which was already
   `[u8]`. **A change to `io.file_ops` does not automatically reach the render
   path** — verify which definition a caller actually binds before reasoning
   about blast radius.

4. **Sign extension is the failure mode.** ASCII fixtures pass while bytes above
   `0x7F` are wrong. Any new coverage must exercise the full 0..255 range; the
   committed spec does exactly that, deliberately.

5. **`scv_i64_bytes_to_u8` is not exported.** `src/lib/scv/store.spl` exports
   only `scv_object_path`. Coverage outside SCV must assert the equivalent
   invariant through the public readers rather than calling it.

## Landed state

Modern step-based SSpec source and authored mirror are complete and committed.
**They have never been executed** — no qualified pure-Simple runtime exists in
the workspace (Rust seed is inadmissible; the on-disk bootstrap stages are
byte-identical and segfault on a two-line program). The spec is fail-closed by
construction: preconditions are asserted, nothing skips, no oracle is stubbed to
pass. Do not record a pass for it until it has actually run.

## Code landed by this lane

- **`file_read` two-return-type spread closed.** The three module-local
  `fn file_read(path: text) -> text?` definitions
  (`40.mono/monomorphize/hot_reload.spl`,
  `99.loader/module_resolver/manifest.spl`,
  `99.loader/module_resolver/resolution.spl`) are renamed `file_read_opt`, with
  their 6 call sites. `file_read` is now 20 definitions, all `-> text`. Safe
  because all three were non-exported, so no cross-module caller could bind them.
- **`app.io.mod` shim asymmetry closed.** It now imports and exports
  `file_read_bytes_i64` alongside `file_read_bytes`.
- **Guard added:** `test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl`
  (REQ-IOREAD-007/008), with positive and negative oracle self-checks.

## Open work

- Execute both specs once a runtime exists; record results in the plan. Nine
  asserted facts were verified by running the guard's own oracle commands, which
  establishes the facts but **not** that the harness ran.
- Converge the remaining 20 same-named `file_read -> text` definitions to one.
  Not attempted here. Read the sibling doc first: full convergence of
  `file_read_bytes` was tried and reverted because it hung the compiler.
- The seed remains unbuildable (duplicate `rt_heap_*_bytes`), which is what
  blocks execution. Owned by another lane — do not edit `runtime_memtrack.c`
  from here.
