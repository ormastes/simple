# Seed ignores `@cfg(arch)` on a top-level `use` (cross-arch closure leak)

Status: fixed (2026-11-22). Priority: P2 toolchain. Owner: seed parser / native_project discovery.

Observed 2026-11-21 while building the SimpleOS arm64 fs_exec kernel
(`--entry-closure --target aarch64-unknown-none`): riscv-only modules
(`os.kernel.arch_adapt.riscv_tlb` -> `os.kernel.arch.riscv64.cpu`,
`os.kernel.arch.riscv32.cpu`) were pulled into the aarch64 closure through an
ungated top-level `use os.kernel.hal.paging...` in `src/os/kernel/memory/vmm.spl`.

Root cause: the parser routes a decorated `use`/`export` to `parse_item()` and
drops its attributes (`src/compiler_rust/parser/src/parser_impl/items.rs:666`);
`UseStmt` has no attribute field (`parser/src/ast/nodes/modules.rs:69-80`), and
`compiler/src/pipeline/cfg_strip.rs` only blanks inactive `let/val/var/const/static`
and strips inactive `@cfg(arch)` fns. So `@cfg(riscv64)\nuse ...` is cosmetic.

What does work: a function-local `use` inside an inactive `@cfg(arch)` fn —
`strip_inactive_cfg_arch_fns` runs before `extract_reachable_module_paths`
(`native_project/discovery.rs:941` vs `:1118`).

Workaround (tagged, landed with this bug): vmm.spl imports `hal.paging` inside
the `@cfg(riscv64)`/`@cfg(riscv32)` `_invlpg` bodies; pinned by
`test/01_unit/os/kernel/arch_adapt/hal_arch_gating_contract_spec.spl`.

Fix needed: carry attributes on `UseStmt` and drop inactive-cfg `use` items in
`cfg_strip` before dependency collection. Then the `@cfg` lines already on
`console_byte.spl` imports become effective (today they are not).

## Fix (2026-11-21, work/seed-cfg-use-20261121)

The seed's text pre-parse pass `strip_inactive_cfg_arch_globals`
(`compiler/src/pipeline/cfg_strip.rs`), which already runs before every
dependency-collection parse (discovery, imports, compiler, interpreter), now
treats top-level `use` / `import` / `from m import` / `common use` /
`export ... from m` as cfg-gated declarations (`is_top_level_import_decl`).
An inactive `@cfg(<arch>)` import is blanked (multi-line `{...}` included), so
the other-arch module never enters the closure. Pure Simple
(`parser_preprocessor.spl` second `@cfg` pass) already blanked the declaration
after a false `@cfg`; no pure-Simple change was needed.
Tests: Rust `inactive_cfg_arch_top_level_use_is_blanked_before_dependency_collection`,
spec `test/01_unit/compiler/pipeline/seed_cfg_top_level_use_spec.spl`.

Residual: the seed text verdict only understands `@cfg(<arch>)` /
`@cfg(not(<arch>))`; compound or non-arch conditions on a `use`
(`@cfg(baremetal or simpleos)`, `@cfg(macos)`, `@cfg(os == "linux")`) stay
ungated in the seed (compound-arch tracked by
seed_cfg_strip_ignores_compound_arch_cfg_2026-11-20).

## Follow-up Resolution (2026-11-22, work/mac-bugs-seed-parity-20261122)

`UseStmt`, `MultiUse`, and `ExportUseStmt` now carry `attributes: Vec<Attribute>`
populated by `parse_attributed_item` / `parse_pub_item_with_attrs`, compound
architecture `@cfg` expressions (`not`/`or`/`and`/`all`/`any`) are evaluated by
both `cfg_line_arch_verdict` and `cfg_attr_arch_verdict`, and
`strip_inactive_cfg_arch_fn_nodes` recursively strips inactive `@cfg` imports
across top-level items, nested containers (`trait`, `mixin`, `actor`, `extend`,
`macro`, etc.), and expression blocks (`do:`, `unsafe:`, `match`, `defer:`)
before dependency discovery. Retired the fn-local `use` workaround in
`src/os/kernel/memory/vmm.spl` in favor of top-level `@cfg(riscv64)` /
`@cfg(riscv32)` imports, updated `hal_arch_gating_contract_spec.spl`, and added
Rust unit tests in `cfg_strip.rs` and `native_project/discovery.rs`.
