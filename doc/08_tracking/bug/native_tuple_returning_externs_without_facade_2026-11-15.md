# Native tuple-returning runtime externs: facade routing was runtime-origin only

Status: process-run family + cpuid FIXED on branch
`work/native-process-run-tuple-abi-20261115`; the unrouted list below is OPEN.

## Defect

`shell_output("uname -m")` returned `""` in a Cranelift-built binary;
`host_arch()` fell back; every `process_run` exit code read `4`.
Oracle: `test/fixtures/native_process_run_tuple_abi/main.spl` (expected stdout
in its header, confirmed by the seed interpreter).

## Mechanism (proven)

1. A stdlib `extern fn rt_process_run(...) -> (text, text, i64)` call is
   **foreign** origin in MIR (provider registry: an actual extern), argc 3 after
   the `text_arg_indices` (ptr, len) split. MIR reads the result with
   `GetField 0/1/2`, i.e. raw word loads.
2. The C owners return a registered `SplArray*`/tuple handle, so the word loads
   read its header. `runtime_native.c` ships `*_tuple` facades that re-pack the
   result into a raw rt_alloc 3-word block.
3. Both pure-Simple backends routed to those facades for **runtime** origin only:
   - Cranelift `cranelift_codegen_adapter.spl`: the redirects (added
     `2add6be09ff`) sit after `if func_op.call_origin != MirCallOrigin.Runtime:`,
     which returns early through `cl_import_call_signature`.
   - LLVM `_MirToLlvm/core_codegen.spl`: the name chain is reset by
     `if func.call_origin != MirCallOrigin.Runtime: call_func_name = func_name`
     (added `22f021ced66`, 2026-11-10). The retained IR of
     `lib.nogc_sync_mut.io.process_ops` shows `call ptr @rt_process_run(`,
     `@rt_process_run_timeout(`, `@rt_process_run_bounded(`,
     `@rt_process_run_bounded_bytes(` -- the owners, not the facades.

## Fix

One table, `runtime_tuple_result_facade(name, word_count)` in
`src/compiler/50.mir/text_extern_abi.spl` (beside the arg-split registry that
already keys these owners). Both backends consult it for every non-source call.
`test/01_unit/compiler/backend/runtime_tuple_result_facade_census_spec.spl`
fails when a tuple-returning `extern fn` under `src/` is neither in the table
nor in its named unrouted list, and when either backend regrows its own list.

## ABI table (routed)

| extern (Simple decl) | words | C owner returns | Rust owner returns | facade |
|---|---|---|---|---|
| `rt_process_run(cmd, args) -> (text, text, i64)` | 3 | `int64_t` (SplArray*) | `RuntimeValue` | `rt_process_run_tuple` |
| `rt_process_run_timeout(cmd, args, ms) -> (text, text, i32)` | 4 | `int64_t` | `RuntimeValue` | `rt_process_run_timeout_tuple` |
| `rt_process_run_bounded(cmd, args, ms, max) -> (text, text, i64)` | 5 | `SplArray*` | `RuntimeValue` | `rt_process_run_bounded_tuple` |
| `rt_process_run_bounded_bytes(...) -> ([u8], [u8], i64)` | 5 | `int64_t` (weak) | `RuntimeValue` | `rt_process_run_bounded_bytes_tuple` |
| `rt_process_run_owned_observed_bounded_value(...) -> (text, text, [i64])?` | 5 | `int64_t*` | none | `rt_process_run_owned_observed_bounded_text` |
| `rt_cpuid_tuple(leaf, sub) -> (...)` | 2 | `int64_t` | `RuntimeValue` | `rt_cpuid_tuple_block` |

The seed (Rust) Cranelift destructures through `rt_tuple_get`, so the seed and
the interpreter are correct; only the pure-Simple AOT backends need facades.

## Open: tuple-returning externs with no facade

Listed in `census_unrouted()` of the census spec (53 names: `rt_shell_exec_tuple`,
`rt_io_udp_recv_from`, `rt_terminal_get_size`, `rt_http_*`, `rt_ssh_exec`,
`rt_process_run_with_limits` (Rust only), `rt_process_owned_v3_poll_value`,
`rt_process_observation_v4_*`, gamepad/rapier/lyon/winit, ...). The ones
spot-checked (`rt_shell_exec_tuple`, `rt_terminal_get_size`,
`rt_io_udp_recv_from`, `rt_process_run_with_limits`) return a registered handle
(C `int64_t`, Rust `RuntimeValue`) that native `GetField` raw loads would
misread the same way; the rest are unclassified. Unverified natively.

## Contract choice

Kept: the Simple declaration stays `-> (text, text, i64)` (interpreter and
seed semantics unchanged; 400+ declarations untouched) and the backend renames
the callee to the raw-block facade. Argument marshalling is unchanged: MIR splits
`cmd` because the call is still named `rt_process_run` (`text_arg_indices`),
and the facade takes exactly those post-split words
(`const char*, uint64_t, SplArray*, ...`). User code calling
`rt_process_run_tuple` by name would NOT be split, so that path is not used.
The facade result is a raw `rt_alloc` block, not an `rt_tuple_new` tuple, so it
does not depend on the separate runtime-tuple `.0` representation defect. The
alternative (declare `-> [text]` and read with `rt_array_get`) works today but
changes every caller's type and the interpreter contract.

Rust runtime lane: `rt_process_run_timeout_tuple` existed only in C, so routing
foreign calls to it would have left it unresolved against the Rust runtime
capsule (`libsimple_native_all.a` lacks it). Added the Rust twin
(`env_process.rs`) and dropped its `c-only` row from
`scripts/check/rt_dual_implementation_baseline.txt`.
`rt_process_run_owned_observed_bounded_text` stays C-only (runtime_native.c). RISK: the default Stage 2 capsule (`libsimple_native_all.a`) carries its owner (`runtime_process_owned.o`) but not the facade, so a foreign call from `io/resource_scope.spl` (imported by the test runner / full CLI) now resolves only on lanes that link runtime_native.c (Stage 4 / C bundle); on the Rust-runtime capsule it becomes an unresolved symbol instead of a silent misread.

Separate, not fixed here: the LLVM native build of the fixture fails in `llc`
with `'%lN' defined with type 'i64' but expected 'ptr'` in
`lib.nogc_sync_mut.io.process_ops` (`_process_observation_cleanup_pending_start_v1`,
result of a source call), `lib.common.process.observation_v1` and
`lib.common.crypto.sha256` -- none on a process-run call.

Same origin hole, not fixed here: the Cranelift `rt_env_get` -> `rt_env_get_value`
and `rt_process_spawn_guarded` -> `_value` redirects and the LLVM `env_get`/argv
remaps are still runtime-origin only.
