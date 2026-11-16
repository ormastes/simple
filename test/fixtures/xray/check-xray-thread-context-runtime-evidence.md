# Runtime thread context fixture attempt

Status: **LINK FAILED; fixture was not run.** This is harness evidence, not a
runtime-hook result or provider qualification.

## Inputs

- Source commit: `1cc48abf35db2d0b74f6ec0b6c7611c9d45ecba4`
- Compiler: Clang 23.1.0 (`ea7d852a70e8bdfaf601d6626a760f9771b2c4b4`)
- Fixture at attempt: `501787e4dbf841a17578a34c464d3a6493be56a35700a6e3e2e403cafa174a5b`
- Admission header at attempt: `cf16532dd4e7e574fccbb1a6e5b46f05c83632372b14ad6c49e3c4220472d01e`
- Host available memory preflight: 31,617,970,176 bytes
- Resource bound: required cgroup `MemoryMax=256M`, swap disabled; outer timeout 30 seconds
- Attempt artifacts: `/tmp/xray-thread-context-runtime-attempt-20261114`

The fixture links the production `runtime_thread.c` compiled with
`SIMPLE_XRAY_CONTEXT_HOOKS_V1=1` and the production Linux LLVM adapter, without
instrumenting either runtime object. The test invokes the adapter-registered
handler directly; it does not use patched compiler-rt sleds.

## Commands

```sh
art=/tmp/xray-thread-context-runtime-attempt-20261114
mkdir -p "$art"
clang -std=c11 -O1 -g -ffunction-sections -fdata-sections -pthread \
  -DSIMPLE_XRAY_CONTEXT_HOOKS_V1=1 -DSIMPLE_RUNTIME_NO_RUST_ARRAY_PACKING \
  -Isrc/runtime -c src/runtime/runtime_thread.c -o "$art/runtime_thread.o"
clang -std=c11 -O1 -g -ffunction-sections -fdata-sections -pthread \
  -mgeneral-regs-only -Isrc/runtime -Isrc/runtime/xray \
  -c src/runtime/xray/xray_llvm_adapter_linux.c -o "$art/xray_adapter.o"
clang -std=c11 -O1 -g -ffunction-sections -fdata-sections -pthread \
  -Isrc/runtime -Isrc/runtime/xray \
  test/fixtures/xray/check-xray-thread-context-runtime.c \
  "$art/runtime_thread.o" "$art/xray_adapter.o" \
  -Wl,--gc-sections -ldl -o "$art/check-xray-thread-context-runtime"
file "$art/check-xray-thread-context-runtime"
timeout 20s "$art/check-xray-thread-context-runtime"
```

These were run under:

```sh
CAP_MEM_MAX=256M CAP_REQUIRE=1 scripts/resource/run_capped.shs \
  timeout 30s bash -c 'set -eu; <commands above, in order>'
```

Compilation completed. Linking stopped because the test fixture did not define
`rt_value_int` and `rt_value_unbox_int`, referenced by
`spl_pool_v1_boxed_task_dispatch` in `runtime_thread.o`. No executable was
produced, and no runtime assertions ran. The value functions are production
owned by `src/runtime/runtime_native.c`; the fixture contains no replacements.

The corrected fixture source is Astra-reviewed, but its link is unrun. It will compile the real
`runtime_native.c` and real dependencies with function/data sections and link
those objects with `--gc-sections`, recording a linker map and discarded
sections. That owner also supplies the production closure ABI. The fixture's
closure stand-ins were removed to avoid strong duplicate definitions. Memory
tracking remains test scaffolding and is outside the fixture's coverage. This
corrected command has not been run.

The approved corrected object set follows the production core-C ownership
flags in `src/compiler/70.backend/backend/runtime_compiler.spl`: compile
`runtime_thread.c`, `runtime_native.c`, and `runtime_memory.c` with
`-DSIMPLE_RUNTIME_MEMORY_OWNER=1`, `-DSIMPLE_RUNTIME_TIMESTAMP_OWNER=1`,
`-DSIMPLE_RUNTIME_NO_RUST_ARRAY_PACKING=1`, `-DSIMPLE_CORE_C_STANDALONE=1`,
and `-DSIMPLE_RUNTIME_THREAD_CPU_COUNT_OWNER=1`; add
`-DSIMPLE_XRAY_CONTEXT_HOOKS_V1=1` only for `runtime_thread.c`. All use
`-ffunction-sections -fdata-sections`. Link the real objects with
`-Wl,--gc-sections`, `-Wl,-Map=<attempt>/link.map`, and
`-Wl,--print-gc-sections`; retain linker stderr. The boxed-dispatch section is
expected to stay live and is not exercised by this fixture's direct-task
scenario. Root authorized a 1 GiB / 60 second attempt, conditional on the
resource preflight below. The object-set command has not been run.

## Corrected-attempt resource preflight

`MemAvailable` was 59,902,668,800 bytes, so the 24 GiB floor passed. The user
manager reported 40 active scopes: eight capped scopes had 94,380,367,872 bytes
aggregate remaining, while 32 scopes were unlimited and therefore had no
measurable remaining allowance. The finite remaining peer allowance alone
exceeded available memory by more than 34 GiB, before the required 8 GiB
reserve. The corrected attempt was not launched. This is a fail-closed
resource preflight, not a fixture or product failure.

## Final launch decision

The first corrected invocation failed bash parsing before the workload script
began; no C compilation or fixture process started. The attempt was rewritten
as `/tmp/xray-thread-context-runtime-attempt.sh`, and `bash -n` passed. Before
launch, a fresh inventory found 58,124,189,696 bytes available and these active
capped build/test allowances: mem-probe 12 GiB max / 6.40 GiB current,
covexpr 6 GiB / 1.78 GiB, cargo/rustc 24 GiB / 1.44 GiB, noarm2 workers 12 GiB
each / 0.77 GiB and 0.50 GiB, plus seed-base 16 GiB / 2.16 GiB. The remaining
peer allowances exceeded available memory before the required 8 GiB host
reserve and separate 2 GiB receipt-probe reservation. The corrected fixture
was not launched. No native attempt result exists.

The close scenario checks callbacks made after close while workers were paused
before those attempts; it does not race close against an already admitted
callback.
