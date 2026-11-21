# Seed ignores `@cfg(arch)` on a top-level `use` (cross-arch closure leak)

Status: open. Priority: P2 toolchain. Owner: seed parser / native_project discovery.

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
