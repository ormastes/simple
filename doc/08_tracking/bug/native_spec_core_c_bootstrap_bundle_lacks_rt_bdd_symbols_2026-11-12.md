# Native spec route: `core-c-bootstrap` runtime bundle lacks `rt_bdd_*`, so a spec that reaches link fails (2026-11-12)

Status: OPEN (filed, not fixed). Severity P2 (blocks every `--native-backend=` spec row that
gets through MIR when the producer is the Stage 2 bootstrap compiler with its receipt-bound
runtime).

## Symptom
`test/01_unit/lib/common/config_core/host_config_spec.spl` run through the Stage 2-built test
runner (PR #8510 build at `bfe789dd411`) with run 15's Stage 2 as producer
(`--native-backend=cranelift`, `SIMPLE_RUNTIME_PATH=<run15>/stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority`,
runtime bundle `core-c-bootstrap`): parse/HIR/MIR/codegen of the 121-module closure succeed, the
link fails:

```
[LLVM-LINK] error: link_to_native failed: cc linking failed: ld.lld: error: undefined symbol: rt_bdd_record_result
ld.lld: error: undefined symbol: rt_bdd_executed_total
ld.lld: error: undefined symbol: rt_bdd_failed_total
collect2: error: ld returned 1 exit status
  error: extern fn rt_bdd_record_result is declared but not implemented anywhere -- declared at .../src/lib/nogc_sync_mut/spec/...
```

The symbols exist in `src/runtime/runtime.c:1705` (`rt_bdd_record_result`) and `runtime.h:1746`;
they are referenced from `lib.nogc_sync_mut.spec.print_summary`. The `core-c-bootstrap` bundle
that the Stage 2 producer links against does not carry them, so no SSpec file can link natively
on this route — the matrix's `loader_native_aot_tests` / `run-native-aot-suite.shs` rows would
fail the same way once the producer gets that far.

Side observation: the link is driven through `cc` (the `collect2:` line is the GCC driver's
collector) even though `ld.lld` is the linker; CLAUDE.md forbids GCC in the toolchain, and the
Stage 2 driver should invoke clang/lld directly.

## Repro
cwd = checkout of `bfe789dd411`; scratch `s2runner/suite.sh k3_unit <runner> test/01_unit/lib/common/config_core`
(native route env as in `scripts/bootstrap/run-native-aot-suite.shs`, `SIMPLE_TEST_PREPROCESS_BOUNDARY=0`).
Producer stderr: `<TMPDIR>/native-build-stderr-<pid>-1.log`.

## Next
Add the `rt_bdd_*` family (and whatever else `lib.nogc_sync_mut.spec` needs at link) to the
`core-c-bootstrap` bundle, or give the native spec route its own bundle; make the link step call
`clang`/`ld.lld` directly.
