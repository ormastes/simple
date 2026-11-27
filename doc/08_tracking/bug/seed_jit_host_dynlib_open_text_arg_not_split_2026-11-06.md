# Seed JIT: every host `dynlib_open` returns 0 (`loader-failed`) — text arg not split to (ptr, len)

- **Filed:** 2026-11-06 (found by the AVX server system-perf work)
- **Component:** Rust seed Cranelift JIT (and LLVM twin table) — extern call lowering
- **Severity:** high — every JIT provider admission fails silently as `loader-failed`
- **Status:** fixed (branch `work/seed-jit-batch2-20261106`)

## Symptom

Under the seed's default JIT, every `dynlib_open` of a provider DLL returns 0, so
`provider_admit_*` reports `loader-failed`. `SIMPLE_EXECUTION_MODE=interpret`
loads the same DLL and admits it.

```
simple run test/02_integration/app/vector_provider/http_vector_parser_live_socket.spl \
  build/providers/simple_vector_provider_levelled.dll \
  ff317f5a67f1ec69279d061482fc1450ad29637382b574be24d67bbb311a1ecc
# JIT (base ecb705896a4): FAIL HTTP vector live socket probe: HTTP provider admission failed: loader-failed  rc=1
```

DLL: `D:/dev/tmp-rel100-simd/vlevels/x86_64-w64-windows-gnu/simple_vector_provider_levelled.dll`
staged at `build/providers/`, sha256 `ff317f5a…1ecc`.

Minimal repro: `test/fixtures/compiler/seed_jit_miscompiles/host_dynlib_open_text_arg.spl`
(expected `open_ok=true sym_ok=true`):

| engine (base ecb705896a4) | output |
|---|---|
| JIT | `open_ok=false` / `sym_ok=false` |
| interpreter | `open_ok=true` / `sym_ok=true` |

## Root cause

`rt_host_dynlib_open(path_ptr, path_len, mode)` and
`rt_host_dynlib_symbol(handle, name_ptr, name_len)`
(`runtime/src/value/wsffi_native.rs`) take text as a `(ptr, len)` pair, and
`codegen/runtime_sffi.rs` registers 3-word machine signatures for both. But
neither name was in `text_arg_indices` (`codegen/instr/calls.rs`, LLVM twin
`codegen/llvm/functions/calls.rs`), so the JIT passed the boxed text handle as
`path_ptr` and the next argument (`mode`) as `path_len`. `raw_text_cstring`
then built a 2-byte path from the handle bytes (or refused it) and the open
returned 0. The interpreter (`interpreter_extern/host_dynlib.rs`) splits the
text itself, and the pure-Simple twin table
(`src/compiler/50.mir/text_extern_abi.spl:170-172`) already listed both names —
only the seed tables were missing them.

## Resolution

Added `rt_host_dynlib_open => [0]` and `rt_host_dynlib_symbol => [1]` to both seed
`text_arg_indices` tables.

Rust test `compiler/tests/host_dynlib_text_abi_jit.rs` lowers the real call via
`calls::compile_call` and runs it:

- before: 4/4 FAILED (`host_dynlib_open_receives_path_bytes_length_and_mode`
  received `path_len=2` (the mode) → `left: -3002`; table lookup `None`;
  real `kernel32.dll` open returned 0)
- after: 4/4 passed

End to end after the fix: see "Verification" below.

## Verification

Seed built from this branch (`cargo build --release --bin simple`, Windows host):

- fixture under `SIMPLE_EXECUTION_MODE=jit`: `open_ok=true` / `sym_ok=true` (was `false`/`false`)
- live probe under JIT: provider admission now succeeds (no `loader-failed`); the
  request then reached the parser and router. The run next died with SIGSEGV
  when `SimpleHttpServer.handle_connection_on_owner_v1` returned. That crash is
  a separate defect: under the JIT, a function with `defer` loses its
  implicit-tail return value. It is recorded in
  `seed_mir_defer_clobbers_implicit_tail_return_2026-11-06.md`.
- live probe under `SIMPLE_EXECUTION_MODE=interpret`:
  `HTTP_VECTOR_LIVE_SOCKET_PROBE_COMPLETE provider_used=true ...` rc=0
- after the `defer` fix as well: live probe under JIT prints
  `HTTP_VECTOR_LIVE_SOCKET_PROBE_COMPLETE provider_used=true ...` rc=0.
