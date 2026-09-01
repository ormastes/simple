# String-core UTF-8 coverage closure — 2026-08-26

## Scope

Production owner: `src/lib/common/string_core.spl`

Spec: `test/01_unit/lib/common/string_core_basic_coverage_spec.spl`

Runner: pure-Simple lightweight single-file source instrumentation.

## Retained result

```text
Passed: 280
Failed: 0
coverage: src/lib/common/string_core.spl 98% (158/160 lines)
coverage-branch: src/lib/common/string_core.spl 100% (52/52 decisions)
```

Command:

```text
SIMPLE_COVERAGE=1 \
SIMPLE_COVERAGE_OUTPUT=build/coverage/string_core_single_runner_cycle3.sdn \
bin/simple run src/app/test_runner_new/test_runner_single.spl \
test/01_unit/lib/common/string_core_basic_coverage_spec.spl --timeout=240
```

## Convergence history

| Cycle | Examples | Branch | Line | Change |
|---|---:|---:|---:|---|
| 1 | 266/266 | 35/42 (83%) | 116/160 (72%) | Authoritative baseline |
| 2 | 277/277 | 48/52 (92%) | 154/160 (96%) | Added missing public operation families and Unicode widths |
| 3 | 280/280 | 52/52 (100%) | 158/160 (98%) | Added final independent early/control branches |

The result proves branch closure only for this Simple owner and this
interpreter/source-instrumented backend. It does not prove Rust, C, SIMD,
Engine2D, Engine3D, device, or aggregate all-owner coverage.
