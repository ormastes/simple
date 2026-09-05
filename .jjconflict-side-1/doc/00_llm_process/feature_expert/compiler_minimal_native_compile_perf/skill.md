# Minimal native-compile performance feature expert

## Ownership

Own only the lane defined by
`doc/03_plan/sys_test/compiler_minimal_native_compile_perf.md`: exact compiler
admission, the one-function fixture, five-sample native-build measurement,
artifact execution, and the 120% time / 110% RSS comparison.

## Invariants

- Never discover, select, or fall back to a compiler implicitly.
- Never count a Rust seed, Stage2 diagnostic probe, compile-only result, stale
  output, or missing baseline as performance evidence.
- Bind compiler path and SHA-256 in an explicit pure-Simple admission receipt.
- Run exactly one live five-sample campaign per verification session.
- Require every emitted artifact to be nontrivial, hashed, and executable.
- Missing qualification is BLOCKED/FAIL, never skipped or converted to PASS.

## Canonical artifacts

- Implementation: `src/app/compiler_perf/minimal_native_compile_perf.spl`
- SSpec: `test/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.spl`
- Manual: `doc/06_spec/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.md`
- Requirements: `doc/02_requirements/feature/compiler_minimal_native_compile_perf.md`
- State: `.spipe/compiler_minimal_native_compile_perf/state.md`
- LLM wiki: `doc/00_llm_process/llm_wiki.md#minimal-native-compile-performance`

## Current evidence state

`TEST_BLOCKED`: no admitted pure-Simple full CLI can run SSpec, docgen,
`sspec-maintain`, or the optimizer. Static guards may accept the prepared
contract but must never be reported as runtime or performance PASS.

Do not edit shared compiler-performance skills for this lane. Runtime repair,
Phase 4, loader/packed-byte performance, and compiler optimization ownership
belong elsewhere.
