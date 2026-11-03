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

**Revalidated 2026-11-02: still plausible because the report title (Cranelift ISA/config SFFI wrappers hand-expand text with rt_string_data/rt_stri) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Policy re-check and re-scope (2026-11-02, lane a6dffc9c/p12-8)

Checked against current policy/design: **still valid, re-scoped to: all
hand-expanded `rt_cranelift_*` text wrappers in `sffi/codegen.spl`; fix via the
two-arg twin route (`fs.spl` precedent) or seed+Simple text-registry rows
(`calls.rs` `text_arg_indices`, `text_extern_abi.spl` + arity + parity spec,
`interpreter_extern/cranelift.rs` accepting text); needs seed-built native
red/green.** Difficulty raised 3 -> 4. No code change made.

The earlier "Status" claim that only the `text` declaration is needed is wrong:
declaring the externs as `text` is a no-op until the registries carry rows.

File:line list:

- `src/lib/nogc_sync_mut/sffi/codegen.spl` ~34-53: hand expansion for
  `cranelift_new_module`, `cranelift_new_aot_module`,
  `cranelift_new_aot_module_config_v2`, `cranelift_aot_isa_feature_v2`; the same
  pattern recurs in `cranelift_declare_string_data`,
  `cranelift_declare_global_data*`, `cranelift_function_addr_in_func`,
  `cranelift_begin_function` and later wrappers (wider than the three named).
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3132` `text_arg_indices`
  (no rows for these symbols; `rt_io_file_open` precedent at ~3301).
- `src/compiler/50.mir/text_extern_abi.spl:40` `text_arg_indices`, `:239`
  `text_extern_semantic_arity`; parity spec
  `test/01_unit/compiler/mir/text_extern_abi_seed_parity_spec.spl`.
- `src/compiler_rust/compiler/src/interpreter_extern/cranelift.rs:199`
  (`spl_cranelift_aot_isa_feature_v2`) and the module constructors read raw
  `i64` ptr/len via `expect_i64`; they break if the wrapper passes text.
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1866-1872` expanded I64 specs.
- `src/lib/nogc_sync_mut/sffi/fs.spl:332` records that multi-arg text externs
  mis-pass the length in seed-produced candidates (why `fs.spl` moved to
  two-arg twins); `spl_cranelift_new_aot_module_config_v2` mixes text and
  scalar args and is the highest-risk form.

## Investigation 2026-11-03 (lane work/cranelift-text-abi) - premise NOT confirmed, status stays open

Static finding (origin/release/1.0.0 `27e65c24371`):

- Every `rt_cranelift_*` / `spl_cranelift_*` extern in `sffi/codegen.spl` is
  declared with raw `i64` ptr/len params and has NO `text_arg_indices` row in
  `codegen/instr/calls.rs:3132`, so the seed lowering performs no text
  expansion for them; the only expansion is the wrapper's single
  `rt_string_data(x)` / `rt_string_len(x)`. `rt_string_data` is registered as
  `[I64] -> [I64]` (`runtime_sffi.rs:646`) taking the RuntimeValue string.
- That is exactly the "two-arg twin" shape the accepted `fs.spl`
  `rt_io_file_open_read/_write/_append` fix uses (same hand expansion, raw
  `i64` externs, no text row). The `io_file_open` defect needed a *text*
  declaration plus a `text_arg_indices` row (double expansion); the cranelift
  family has neither, so no double-expansion path was found in source.
- Therefore no source change was made. The bug can only be confirmed or closed
  by a seed-built NATIVE run.

Interpreter run of the probe below (seed `bin/simple.exe run`) fails
differently: `spl_cranelift_aot_isa_feature_v2: argument 2 must be an integer`
(interpreter bridge, separate from native lowering); not evidence for this bug.

Why no native red/green on this Windows host (blockers, reproducible):

1. `simple compile probe.spl --native` generates code but the legacy linker
   (`linker/native.rs`) invokes `lld-link` with GNU args (`-o`,
   `--whole-archive`, `-lkernel32`): `lld-link: error: could not open
   '<out>.exe'`. Same with `--linker lld`, llvm-mingw clang first on PATH.
2. `simple native-build probe.spl` (seed) is a whole-project build: needs a
   worker binary (`native_build_worker_binary_valid`, set `SIMPLE_BINARY` to a
   forward-slash path) and then fails with `SCV-E-ADMISSION:
   source-inventory-root-empty: --source root 'src/os'` on a sparse worktree;
   ~8 min per attempt.

Repro to run on a Linux seed (or full checkout):

```spl
use std.nogc_sync_mut.sffi.codegen.{cranelift_new_aot_module_config_v2, cranelift_aot_isa_feature_v2}
fn main():
    val m = cranelift_new_aot_module_config_v2("probe", "x86_64-unknown-linux-gnu", "", 1, ["has_avx"])
    print "avx={cranelift_aot_isa_feature_v2(m, "has_avx")} bogus={cranelift_aot_isa_feature_v2(m, "has_nonexistent_zzz")}"
```

Expect `avx=1 bogus=0`. If the seed-built native binary prints garbage, the
defect is in seed call lowering of `rt_string_data(<text param>)` (not in
`codegen.spl`); write a Rust test in `calls.rs` against that lowering. If it
prints the expected values, close this bug as invalid with that transcript.
