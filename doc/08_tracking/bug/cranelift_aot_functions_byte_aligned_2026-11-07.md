# Cranelift AOT objects place functions at 1-byte alignment

Status: OPEN (P2). 2026-11-07. Found while making the Windows Stage 2
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
