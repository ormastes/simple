# Codegen Cranelift ISA/config SFFI wrappers share the io_file_open text-ABI mis-expansion defect — 2026-10-22

## Symptom

`src/lib/nogc_sync_mut/sffi/codegen.spl` hand-expands text arguments to
`(ptr, len)` with `rt_string_data`/`rt_string_len` for the Cranelift module
and ISA-family externs:

- `cranelift_new_aot_module(name, target)` → `rt_cranelift_new_aot_module_triple(rt_string_data(name), rt_string_len(name), rt_string_data(target), rt_string_len(target))`
- `cranelift_new_aot_module_config_v2(name, target, cpu, opt_level, features)` → 9-arg `spl_cranelift_new_aot_module_config_v2(...)`
- `cranelift_aot_isa_feature_v2(module, feature)` → `spl_cranelift_aot_isa_feature_v2(module, rt_string_data(feature), rt_string_len(feature))`

This is the SAME pattern that made `io_file_open` return -1 for every entry
read in seed-built native binaries (fixed 2026-10-22 in
`src/lib/nogc_sync_mut/sffi/fs.spl` by declaring the extern in text form and
letting the compiler's text-ABI registry perform the expansion; the rebuilt
seed's call-site lowering re-expanded the already-extracted raw pointer,
verified by candidate disassembly). These externs carry the same expanded
`[I64, I64, ...]` specs in
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1825-1827` and have
no `text_arg_indices` rows in `codegen/instr/calls.rs`, so the manual
expansion is the only text handling — and it is exactly the shape the seed
mis-lowers.

Observable effect: in a seed-built (AOT) compiler binary, the ISA-feature
readback `cranelift_aot_isa_feature_v2` receives `rt_string_data(address)`
instead of `rt_string_data(feature_text)`, so the Cranelift runtime looks up
a garbage feature name and returns a garbage/0 i64; the configured-module
constructors similarly build modules under garbage names/targets. Under the
Rust seed's own execution the same source behaves correctly, so the defect
only surfaces in self-hosted binaries — precisely the configuration the
stage-2/3/4 bootstrap lanes build.

## Status

Open. Source-level fix prepared in the same shape as the accepted
`rt_io_file_open` fix: declare these externs with `text` parameters
(e.g. `extern fn spl_cranelift_aot_isa_feature_v2(module: i64, feature: text) -> i64`)
and pass the text values directly. Runtime-side (Rust) behavior is
correct; no runtime change needed. Not yet applied because the bootstrap
lane owned the tree at filing time.

## Evidence

- `runtime_sffi.rs:1822-1827` — expanded I64 specs for the whole
  `rt_cranelift_*` / `spl_cranelift_*` family.
- `codegen.spl:38-49` — the manual `rt_string_data`/`rt_string_len`
  expansion at the call sites.
- Sibling bug: `stage2_sanity_p2_add_zero_source_files_scv_cold_snapshot_2026_10_22.md`
  (io_file_open chain, fixed).
