# Cranelift AOT objects place functions at 1-byte alignment

Status: FIXED in the seed bridge (2026-11-07); needs a Stage 2 rebuild to reach
shipped binaries. Opened OPEN (P2) 2026-11-07. Found while making the Windows Stage 2
`avx_server_loadgen` / `simple_web_server` exchange HTTP.

## Observation

Every `.text$subsection` section in the Stage 2 cranelift AOT objects
(`--backend cranelift`, Windows x86_64, `x86_64-w64-windows-gnu`) carries
`IMAGE_SCN_ALIGN_1BYTES`. In the linked `loadgen.exe`, 1299 of 2089 text
symbols are not 16-byte aligned, and 161 have `addr & 7 == 1`. One example is
`test.03_system.tools.avx_server_loadgen.__lambda_lift_0` at `0x140037251`.

## Cause

`src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs`
(`rt_cranelift_aot_define_function`) calls `ObjectModule::define_function`.
Vendored cranelift-object 0.116.1 (`backend.rs:346,378`) aligns each function
to `max(buffer.alignment, isa.function_alignment().minimum, symbol_alignment)`.
On x64, `function_alignment()` returns `minimum: 1, preferred: 32`
(`cranelift-codegen/src/isa/x64/inst/mod.rs:2892`), and `preferred` is never
used. Code lowered from ELF objects is likely affected the same way; that has
not been measured.

## Impact

- Correctness: any runtime that reads a code address as a tagged word loses
  bits. That happened in `runtime_thread.c` `spl_worker_callable`, which was
  fixed on the same day to accept a bare entry for kind VALUE. Other decoders
  of function words, such as the pool submit, have not been audited for bare
  entries.
- Performance: hot loops start at unaligned addresses. This skews the AVX
  server system perf lane (`check-avx-server-system-perf.shs`).

## Fix direction

In `cranelift_sffi.rs`, compile with `ctx.compile` and define the function
with `define_function_bytes(..., alignment = max(buffer.alignment,
isa.function_alignment().preferred), ...)`, or align to at least 16. This
needs a rebuild of the cranelift bridge and the Stage 2 compiler.

## Fix (2026-11-07)

`src/compiler_rust/compiler/src/codegen/shared.rs` adds
`MIN_FUNCTION_ALIGNMENT = 16` and `define_function_aligned()`. The helper
compiles the context and calls `Module::define_function_bytes` with alignment
`max(buffer.alignment, isa.function_alignment().minimum, 16)`. The vendored
cranelift crates are unchanged, and cranelift 0.116 has no
`log2_min_function_alignment` setting.

Every production `Module::define_function` call in the seed codegen now goes
through the helper, for both AOT (`ObjectModule`) and JIT (`JITModule`):

- `cranelift_sffi.rs`: `rt_cranelift_define_function` and
  `rt_cranelift_aot_define_function`
- `common_backend.rs`: 3 sites
- `closure_boxed_entry.rs`: 2 sites
- `shared.rs`: `create_body_stub`

Only test fixtures still call `define_function` directly. The helper behaves the
same as `define_function` because the seed never enables JIT hotswap, which is
the only extra step the JIT `define_function` path performs.

The 16-byte floor applies on every target. On aarch64 and s390x it raises the
minimum from 4. On riscv64 it raises it from 2. On x86_64 it raises it from 1.
The pure-Simple side (`src/compiler/70.backend/backend/cranelift_*.spl`) sets no
function-alignment flag that could override this. Its only alignment input is
the static/data alignment in `cranelift_codegen_adapter.spl`.

### Evidence

- New test
  `codegen::cranelift_sffi::tests::test_aot_functions_are_16_byte_aligned`.
  It goes through the real FFI path (`rt_cranelift_begin_function` ->
  `rt_cranelift_aot_define_function` -> `rt_cranelift_emit_object_raw`) for
  `x86_64-unknown-linux-gnu`, `x86_64-pc-windows-gnu` (COFF) and
  `aarch64-unknown-linux-gnu`. For each of 5 functions it checks that the
  containing section's alignment is >= 16 and that the symbol offset is 16-aligned.
  - Before the fix it fails with
    `x86_64-unknown-linux-gnu: section of fnalign_0 has alignment 1`.
  - After the fix it passes.
- `cargo test -p simple-compiler --lib codegen::` result: 1086 passed, 2 failed.
  Both failures also occur on the unmodified tree:
  - `test_configured_fma_isa_lowers_a_real_function` looks for a section name
    containing the symbol, but per-function sections are named
    `.text.subsection`.
  - `test_cranelift_jit_typed_dict_float_literal_key_compatibility` fails on a
    native `Dict<f64,_>` lookup.
- Not proven here: the alignment in a linked Stage 2 binary. The pure-Simple
  Stage 2 compiler reaches this bridge through the seed's `rt_cranelift_*`
  exports, so shipped binaries pick up the fix only after a Stage 2 rebuild.
  After that rebuild, re-run the measurement above (1299 of 2089 unaligned).
  The `runtime_thread.c` bare-entry workaround stays in place. Other
  function-word decoders, such as the pool submit, still have not been audited.
