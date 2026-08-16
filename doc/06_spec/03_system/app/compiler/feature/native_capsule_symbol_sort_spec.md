# Native capsule symbol ordering

**Status:** TEST_BLOCKED — executable SSpec is ready, but this lane has no
admitted pure-Simple Stage 4/5 full CLI for `test`, `spipe-docgen`, or
`sspec-maintain`.

**Audience:** compiler maintainers reviewing frozen native-capsule identity
generation and operators qualifying a future self-hosted CLI.

**Executable source:**
`test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl`

## Purpose and claim boundary

The system contract calls the production
`native_capsule_sorted_symbol_ids_v1` function and verifies deterministic
ascending ordering, value-semantic input preservation, merge-boundary behavior,
and a fail-closed full-result oracle. It complements the retained performance
report; it does not impose a machine-dependent timing threshold or claim
whole-compiler, Stage 4, release, or cross-host performance.

The Rust seed is prohibited. The admitted pure-Simple Stage 2 compiler used by
the performance lane supports only `compile` and `native-build`, so it cannot
certify this SSpec runner or its documentation pipeline.

## Preconditions

1. A pure-Simple full CLI has an explicit Stage 4/5 admission receipt.
2. Its resolved path and SHA-256 are recorded.
3. Bounded `--version` and `test --help` probes pass without a seed/debug banner.
4. `SIMPLE_NO_STUB_FALLBACK=1` is active for executable verification.
5. The source revision contains the typed bottom-up mergesort implementation.

## Deterministic production ordering

### Should order reverse symbols without mutating caller input

Requirement: REQ-CNSS-001.

1. Create a reverse-ordered native-capsule symbol set.
2. Invoke the production sorter.
3. Require IDs `0..7` in ascending order.
4. Require the original input to remain `7..0`.

### Should preserve an already ordered symbol set

Requirement: REQ-CNSS-001.

1. Submit IDs `0..5` in canonical order.
2. Invoke the production sorter.
3. Require the identical six-element sequence.

### Should order mixed negative and duplicate identifiers deterministically

Requirement: REQ-CNSS-001.

1. Submit `[3, -1, 2, 3, 0, -1]`.
2. Invoke the production sorter.
3. Require `[-1, -1, 0, 2, 3, 3]` and cardinality six.

## Merge boundary behavior

### Should return an empty result for empty input

Requirement: REQ-CNSS-002.

1. Invoke the sorter with no symbols.
2. Require zero output values.

### Should preserve a singleton identifier exactly

Requirement: REQ-CNSS-002.

1. Invoke the sorter with `SymbolId(41)`.
2. Require one output whose ID remains `41`.

### Should order a non-power-of-two reverse workload through the partial tail

Requirements: REQ-CNSS-002 and NFR-CNSS-001.

1. Generate 4,097 reverse-ordered IDs.
2. Invoke the production sorter so the final merge pass has a partial tail.
3. Audit every output position, exact cardinality, and a positive weighted
   checksum.
4. Require audit code `ok`.

## Fail-closed result auditing

### Should accept a complete canonical result with an exact checksum

Requirement: REQ-CNSS-003.

1. Sort eight reverse-ordered IDs.
2. Audit every position.
3. Require code `ok`, count `8`, and weighted checksum `204`.

### Should reject a result with missing symbols

Requirement: REQ-CNSS-003.

1. Present three IDs while declaring four expected values.
2. Require `length-mismatch`, observed count `3`, and checksum `-1`.

### Should reject interior corruption that endpoint checks would miss

Requirement: REQ-CNSS-003.

1. Present `[0, 1, 1, 3]`, retaining the expected endpoints while corrupting
   the interior.
2. Require `id-mismatch:2`, count `4`, and checksum `-1`.

## Qualified operator commands

```text
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=native
bin/simple spipe-docgen test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --baseline
```

Expected executable result: nine examples, zero failures, no fallback/stub
markers, and a trustworthy nonzero executed-example count. Expected docgen
result: complete mirror, `0 stubs`. Expected maintenance result: current mirror
and no blocker-capped `SSDOC-*` findings.

## Current evidence and remediation

- Static source/manual traceability: PASS — nine scenarios, eighteen visible
  steps, built-in matchers only, real assertions in every scenario, and zero
  executable `.spl` files under `doc/06_spec`.
- SSpec runtime: TEST_BLOCKED — qualified full CLI unavailable.
- SPipe docgen: TEST_BLOCKED — qualified full CLI unavailable.
- `sspec-maintain`: TEST_BLOCKED — qualified full CLI unavailable.
- Remediation: obtain an admitted current-source full CLI, record its identity,
  then execute the four commands above once in order and replace this status
  only from retained successful output.

The authoritative test plan is
`doc/03_plan/sys_test/compiler_native_capsule_symbol_sort.md`; measured
performance evidence is
`doc/09_report/perf/compiler_native_capsule_symbol_sort_microbenchmark_2026-08-16.md`.
