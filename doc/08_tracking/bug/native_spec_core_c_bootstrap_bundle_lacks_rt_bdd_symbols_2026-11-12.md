# Native spec route: `core-c-bootstrap` runtime bundle lacks `rt_bdd_*`, so a spec that reaches link fails (2026-11-12)

Status: fix-implemented-verification-pending (2026-11-27, W2-3 Windows triage). `src/runtime/runtime_native.c` (`12892-13009`) and `src/runtime/runtime.c` (`1491-1512`) now define and export `rt_bdd_record_result`, `rt_bdd_executed_total`, `rt_bdd_failed_total`, `rt_bdd_describe_start_rv`, `rt_bdd_describe_end`, `rt_bdd_it_start_rv`, `rt_bdd_it_end`, `rt_bdd_has_failure`, `rt_bdd_note_skip`, `rt_bdd_fail_rv`, `rt_bdd_expect_fail`, `rt_bdd_expect_eq_rv`, `rt_bdd_expect_truthy_rv`, `rt_bdd_expect_truthy`, `rt_bdd_format_results`, and `rt_bdd_clear_state`, and `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` compiles `runtime_native.c` into the `core-c-bootstrap` capsule. Severity P2 (Stage 2 native SSpec link verification on Linux/aarch64 and `src/app/compile/native.spl` link-driver inspection remain outside this Windows lane).

## Verification 2026-11-27 (Windows host)

- `sh test/01_unit/runtime/runtime_bdd_native_exports_contract_test.shs` -> `PASS: runtime_native.c owns rt_bdd_* exports across core-c, memowner, standalone, and legacy profiles`.
- Pending outside this Windows lane: full Stage 2 native `--native-backend=cranelift` SSpec link+run and direct `clang`/`ld.lld` driver verification (`src/app/compile/native.spl`).

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
