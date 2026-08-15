# Vulkan Engine2D native JIT is missing `rt_struct_receiver_valid`

## Status

Resolved for the named symbol (2026-08-15, see Resolution below): the JIT
codegen panic on `rt_struct_receiver_valid` / `rt_struct_alloc` and the
`rt_process_run_owned_bounded_value` module fallback are fixed and verified.
A distinct follow-up blocker remains open (native `rt_vulkan_*` stubs, last
section). Original status: Open. This blocks native-mode Vulkan Engine2D
integration and therefore blocks
native 8K/80 evidence on the available discrete GPUs. It does not invalidate
the exact interpreter-mode device-readback receipts.

## Reproduction

```sh
env SIMPLE_VULKAN_READBACK_TIMEOUT_SECS=75 \
  SIMPLE_VULKAN_READBACK_WORK_DIR=build/vulkan-engine2d-readback-live-2026-08-12 \
  REPORT_PATH=doc/09_report/vulkan_engine2d_readback_2026-08-12.md \
  sh scripts/check/check-vulkan-engine2d-readback.shs
```

The strict Vulkan probe initializes the backend and completes exact clear and
rectangle device readbacks, then the native-mode policy stops before its
integration specifications because JIT compilation falls back to the
interpreter. The reported missing runtime function is
`rt_struct_receiver_valid` while compiling Engine2D/SFFI methods.

## Required fix and acceptance

1. Export/link `rt_struct_receiver_valid` through the native JIT runtime
   symbol table used by Engine2D and SFFI method compilation.
2. Run the canonical Vulkan readback gate in native mode with no interpreter
   fallback and both integration specifications executed.
3. Record the physical adapter identity in the receipt; selection-rule
   inference alone is insufficient for an 8K performance claim.
4. Only then run the dynamic and retained 7680x4320 presentation measurements
   with p50/p95, RSS, fallback/completion state, and checksum/readback proof.

## Evidence

The 2026-08-12 gate report is
`doc/09_report/vulkan_engine2d_readback_2026-08-12.md`. It found RTX A6000
and TITAN RTX discrete adapters as well as llvmpipe; it records exact
device-readback correctness, not native execution or 8K/80 throughput.

## Source audit update (2026-08-12)

The missing symbol is already fixed in current source: it is implemented in
`src/runtime/runtime_memory.c`, listed in the full JIT manifest, and the
runtime build now uses the multiline-aware export scanner. A fresh isolated
runtime build generated both the linked extern and `RuntimeSymbolEntry` for
`rt_struct_receiver_valid`, and its focused runtime-test binary linked.

The failed live gate was using stale compiler/runtime artifacts built before
that scanner correction. Do not add a duplicate registry patch. Rebuild and
publish a self-hosted compiler/runtime authority containing the current source,
then rerun the native Vulkan gate with adapter-name telemetry.

## Resolution (2026-08-15)

The "already fixed in source" claim above was wrong for the JIT path. The C
implementation, manifest entry (`common/src/runtime_symbols.rs:2116`), and
export scanner were all in place, but **`RUNTIME_FUNCS` in
`compiler/src/codegen/runtime_sffi.rs` had no `RuntimeFuncSpec` for
`rt_struct_alloc` or `rt_struct_receiver_valid`**. Both are codegen roots
(listed in `runtime_symbol_is_codegen_root`, emitted directly by
`codegen/instr/{fields,closures_structs}.rs`, never via a MIR call node), so
`declare_runtime_functions` skipped them and `resolve_runtime_func` panicked
with `missing runtime fn 'rt_struct_receiver_valid'` at
`codegen/instr/helpers.rs:308` — reproduced live 2026-08-15 with a
freshly-built seed that already exported both symbols (`nm` confirmed), proving
the stale-artifact theory insufficient.

Fix 1: added the two specs to `RUNTIME_FUNCS`
(`rt_struct_alloc(&[I64])->[I64]`, `rt_struct_receiver_valid(&[I64,I64,I64])->[I8]`).

Rerun then exposed the next JIT blocker in the same gate:
`unresolved external symbol 'rt_process_run_owned_bounded_value'` (whole-module
interpreter fallback). The name is in the manifest but
`src/runtime/runtime_process_owned.c` was never in the seed runtime crate's C
source list. Fix 2: added it to `compiler_rust/runtime/build.rs` `c_sources`;
its only cross-file C dependency, `rt_free_deep` (lives in `runtime_native.c`,
deliberately not compiled there), is swapped for the Rust `rt_string_free` via
`SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE` — exact-equivalent, every value it
deep-frees is an `rt_string_new` result.

Verification (binary `cargo build --release --bin simple`, 2026-08-15):
- Before: evidence log had 5,108 `rt_struct_receiver_valid` mentions and
  repeated `[CODEGEN PANIC] ... missing runtime fn` for `SffiFileLock.is_valid`
  / `.close` / `file_lock_acquire`.
- After: `grep -c "missing runtime fn" evidence.log` = 0; no
  `rt_process_run_owned_bounded_value` fallback.
- `test/02_integration/rendering/vulkan_strict_spec.spl` and
  `engine2d_cpu_vulkan_parity_spec.spl` both PASS (exit 0) on the fixed binary.

## Remaining blocker (new, distinct): native `rt_vulkan_*` are feature-gated stubs

With the JIT no longer falling back, the gate now fails earlier and
differently: `vulkan_probe_status=Unavailable`, `init_error=availability`.
Cause: JIT-compiled code calls the **linked** `rt_vulkan_is_available`, which
without the `vulkan` cargo feature is the `return 0` stub in
`runtime/src/vulkan_graphics_runtime_core.rs` (ICF-folded with `rt_vulkan_init`
at the same address). The interpreter instead dispatches to the real
dlopen-based probe in `compiler/src/interpreter_extern/gpu.rs`, which is why
interpreter mode initialized Vulkan. Building with the feature
(`cargo build --release --bin simple --features simple-compiler/vulkan`) fails
in vendored `rspirv` with `E0583: file not found for module 'build'`, so the
native-feature lane is itself broken. Native-mode Vulkan Engine2D therefore
needs either (a) the vendored rspirv/vulkan feature build repaired, or (b) a
C-ABI bridge from the JIT's `rt_vulkan_*` imports to the interpreter's
dlopen-based providers. Tracked here until split out.
