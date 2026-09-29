# System Test Plan: Minimal Native-Compile Performance

## Scope and criterion

Measure a disjoint compiler criterion: five process-cold, incremental-cache-
disabled native builds of
`test/03_system/app/compiler/feature/fixtures/minimal_native_compile_main.spl`.
The fixture returns zero and has no imports. Gate p50/p95 wall time at 120% and
max RSS at 110% of an admitted baseline from the identical campaign.

## Traceability

| Requirement | System evidence |
|---|---|
| REQ-CMNCP-001, NFR-CMNCP-001/003 | absent identity, seed rejection, exact receipt scenarios |
| REQ-CMNCP-002 | compile failure, missing/small artifact, valid executable scenarios |
| REQ-CMNCP-003 | invalid baseline, regression, exact-boundary scenarios |
| REQ-CMNCP-004, NFR-CMNCP-002/003 | invalid-count block, missing-compiler block, single live five-sample scenario |

Canonical SSpec:
`test/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.spl`.
Mirrored manual:
`doc/06_spec/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.md`.

## Qualified environment

Export all of:

```text
SIMPLE_CMNCP_COMPILER
SIMPLE_CMNCP_ADMISSION_RECEIPT
SIMPLE_CMNCP_COMPILER_SHA256
SIMPLE_CMNCP_WORK_DIR
SIMPLE_CMNCP_BASELINE_P50_US
SIMPLE_CMNCP_BASELINE_P95_US
SIMPLE_CMNCP_BASELINE_MAX_RSS_KB
```

The receipt schema is documented in the manual. The runtime executing SSpec
and the compiler under measurement must both be admitted pure-Simple
self-hosted artifacts. A Rust seed cannot execute the test or supply evidence.

## One-pass verification

When qualified, run exactly once:

```bash
SIMPLE_LIB=src <admitted-self-hosted-simple> test test/03_system/app/compiler/feature/compiler_minimal_native_compile_perf_spec.spl --mode=interpreter
```

Pass requires every deterministic case and the one live campaign. Retain the
test output, admission receipt, environment values (excluding secrets), and
`$SIMPLE_CMNCP_WORK_DIR/minimal-native-compile-perf.receipt`.
If unavailable, record `TEST_BLOCKED` and do not substitute another runtime. At most
three verify/fix cycles are allowed; convergence stops the lane.

## Execution order and dependencies

1. Validate the exact runtime and compiler admission receipts.
2. Run the deterministic admission/artifact/budget scenarios.
3. Run the two fail-closed campaign preflight scenarios.
4. Run the one live five-sample campaign and retain its receipt.

The focused SSpec command owns this order; operators must not split out and
repeat the live scenario to manufacture a preferred sample.

## Manual rendering and capture policy

The mirrored manual keeps the 14 operator steps, scenario narratives,
scorecard, traceability, and claim limits visible. Executable detail may be
folded when qualified docgen is available. This non-UI lane captures an
`artifact` receipt at
`$SIMPLE_CMNCP_WORK_DIR/minimal-native-compile-perf.receipt`; no screenshot or
TUI capture applies.

## Risk areas

- An unbound/stale compiler binary could create false attribution.
- A stale or trivial output could create a false compile success.
- Incremental caches or repeated live execution could bias measurements.
- An unavailable runner could be mislabeled PASS from static inspection.

The implementation fails closed on each risk, and the live scenario runs once.

## Current evidence

On 2026-08-16 no admitted full CLI could execute SSpec. An admitted Stage2
candidate with SHA-256
`68cbbbbd60ed073e2e21aac682207f0c21cef703f5fe7a920fee3e32c19af2aa`
failed three distinct minimal source probes before artifact emission with
`str.clear was called on a receiver that is not text`. Those diagnostic runs
are not baseline or runtime PASS evidence. Live verification is `TEST_BLOCKED`.
