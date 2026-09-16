# Stage 2 Native SSpec Runner Process Crash

## Status

ABI FIXED and admitted for the NVMe Phase 2 path. A current-source Stage 2
linked with the rebuilt LLVM native-all authority compiles and runs the exact
native NVMe SSpec and standalone docgen. The global deployed full CLI remains
stale; no additional Stage 3 run or full bootstrap was required.

## Evidence

The admitted Retry 15 Stage 2 pure-Simple compiler can native-build
`rv32_nvme_nand_read_level_spec.spl` in 10.85 seconds. The resulting 35,120-byte
x86-64 executable reaches `rt_process_run` and then terminates with SIGSEGV in
`memcpy` before producing an SSpec summary. An unstripped rebuild gives the same
backtrace:

```text
__memcpy_avx_unaligned_erms
rt_process_run
<generated native spec>
```

The broad `src/app/test_runner_new/main.spl` build without an explicit runtime
bundle fails after 52.72 seconds in nine transitive debug/signal/coverage
modules. These are runner-closure failures, not NVMe firmware failures.

The corrected runtime-bundle recipe reproduced the same nine failures in 52.40
seconds at 416,340 KiB peak RSS. A one-module native runner that called
`rt_cli_run_file` built in 1.8 seconds, but correctly failed closed at execution
because the admitted standalone runtime does not provide the Rust interpreter
driver hook.

Disassembly of the retained direct-spec debug binary proves the crash is an ABI
lowering defect:

```text
src__lib__nogc_sync_mut__io_runtime__process_run:
    xor %edx,%edx
    jmp rt_process_run
```

Generated native code passes `(text, [text])`, while the selected raw
`rt_process_run` provider expects `(cmd_ptr, cmd_len, args)` and reaches
`memcpy` with the args pointer as `cmd_len`. Current source already routes this
call to `rt_process_run_tuple` in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, and the matching
facade exists in `src/runtime/runtime_native.c`; the admitted Stage 2 compiler
did not emit that lowering.

The retained Stage 3 pure-Simple refresh was then allowed its full 90-minute
cap. It remained at 99% CPU, reached 1,849,336 KiB peak RSS, emitted no
diagnostic, produced no output binary, and exited 124. Do not rerun this
identical command.

## Root-Cause Fix and Focused Evidence

The Rust LLVM direct-call and method-call paths did not apply the existing
process-runtime argument expansion used by Cranelift. Both now reuse
`process_c_runtime_arg_indices`, so `rt_process_run(text, args)` lowers to
`rt_process_run(cmd_ptr, cmd_len, args)`. The focused LLVM IR regression passed:

```text
process_run_uses_ptr_len_array_runtime_abi ... ok
1 passed; 0 failed
```

The incrementally rebuilt `simple-driver` then compiled the exact canonical
SSpec through the explicit `SIMPLE_NATIVE_BUILD_RUST=1` bootstrap handler in
23.00 seconds at 693,884 KiB peak RSS. The resulting 45,552-byte executable ran
the real self-test, clean/garbage GHDL, and AXI recovery gates:

```text
5 examples, 0 failures
elapsed 3:17.08; peak RSS 349,924 KiB
```

This is focused compiler/SSpec diagnostic evidence, not pure-Simple release
admission. The standalone SPipe docgen closure exposed two further native
defects. Literal LaTeX braces in `src/lib/common/math_repr.spl` were parsed as
an interpolation of undeclared `T`; escaping them as `{{T}}` fixes HIR lowering.
LLVM also omitted the existing `has` collection-method alias and emitted an
undefined `has` symbol. The alias now lowers to `rt_contains`, matching
Cranelift, and the parser uses its existing `ends_with` plus slicing support
instead of the unavailable native `trim_end_matches` method.

Both focused LLVM alias regressions pass. The incrementally rebuilt driver then
compiled standalone `spipe_docgen`, which ran against the canonical NVMe SSpec
and generated all five scenarios with zero stubs. The generated page was
not retained because its five-line source documentation block would replace
the richer existing manual and reported seven documentation-quality warnings.

## Phase 2 Admission

The first current-source Stage 2 rebuild still linked the stale
`libsimple_native_all.a`, so its exact SSpec reproduced the original two-argument
wrapper and SIGSEGV. This proved that Stage 2 `native-build` uses the linked Rust
compiler authority; changing or rebuilding only Simple frontend modules cannot
update that ABI lowering.

Only `simple-native-all` was rebuilt with LLVM from current source. Relinking
Stage 2 against that isolated authority produced:

```text
Build complete: 3 compiled, 719 cached, 0 failed
Stage 2: 127,226,392 bytes
elapsed 1:54.75; peak RSS 950,956 KiB
sha256 0ea34e1eb7b116c69dadac4686e984df517743be0295ee718295539d9f89c900
```

Disassembly of its newly compiled SSpec proves the native call now computes
`rt_string_data(cmd)`, computes `rt_string_len(cmd)`, places args in `%rdx`,
and calls `rt_process_run(cmd_ptr, cmd_len, args)`. The executable then passed
the real self-test, clean/garbage GHDL, and AXI recovery gates:

```text
5 examples, 0 failures
elapsed 3:46.16; peak RSS 349,712 KiB
sha256 d57440c9d23df0b98b8daa4d15a7452cbbf3fef8692f01eda1af575facc872e1
```

The same Stage 2/runtime pair compiled standalone docgen. It parsed all five
canonical scenarios with zero stubs in 0.02 seconds at 6,648 KiB peak RSS.
Its output was retained under build evidence rather than replacing the richer
manual; the seven source-documentation warnings remain visible. The docgen
binary SHA-256 is
`e7d7b50a8fa02d441174f27ce3c1066b5a6b3a19873733a63723866bbc85b1ea`.

Earlier required source checks each reported `OK` for `src/compiler`, `src/lib`,
`src/app/mcp`, and `src/app/simple_lsp_mcp`, then exited 1 because the deployed
CLI had no sibling `simple_seed`. A sibling has since been restored, but the
global full-CLI source/MCP admission was not rerun to convergence and is not
claimed here. The earlier MCP stdio smoke also retained unresolved SSpec names
(`describe`, `slow_it`, `step`, and `expect`). These global tool-admission gaps
are separate from the admitted NVMe Phase 2 pair.

Final review also found a separate pre-existing ABI mismatch outside this
focused fix: `rt_process_run_with_limits` is declared with five parameters in
`runtime_sffi.rs` and four source-level arguments in the Simple facade, while
the Rust provider takes eight parameters. It remains fail-closed follow-up work
and is intentionally not added to the shared process argument map here.

Local evidence:

- `build/logs/stage2-nvme-sspec-direct/`
- `build/logs/stage2-sspec-runner/`
- `build/logs/stage2-sspec-runner-runtime-bundle/`
- `build/mini_builds/fixed-driver-build.*`
- `build/mini_builds/fixed-spec-rust-build.*`
- `build/mini_builds/fixed-spec-run.*`
- `build/mini_builds/fixed-docgen-build.*`
- `build/mini_builds/docgen-driver-build.*`
- `build/mini_builds/docgen-native-build.*`
- `build/mini_builds/nvme-admission/`
- `build/bootstrap/nvme-admission-20260729/`

## Resume Gate

The NVMe Phase 2 software gate is complete. Do not substitute the stale global
deployed CLI for the admitted Stage 2/runtime pair, and do not rerun the bounded
Stage 3 command. Physical Cosmos+ BT-001..BT-006 remains the next production
gate.
