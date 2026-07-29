# Stage 2 Native SSpec Runner Process Crash

## Status

BLOCKED after the bounded Stage 2 and Stage 3 attempts. No full bootstrap was
run.

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

Local evidence:

- `build/logs/stage2-nvme-sspec-direct/`
- `build/logs/stage2-sspec-runner/`
- `build/logs/stage2-sspec-runner-runtime-bundle/`

## Resume Gate

First admit a Stage 3 compiler that demonstrably emits
`rt_process_run_tuple`, or fix the silent Stage 3 compile throughput defect.
Then rebuild and execute the exact NVMe SSpec and standalone SPipe docgen once.
Do not accept the Rust `rt_cli_run_file` compatibility path as pure-Simple
release evidence.
