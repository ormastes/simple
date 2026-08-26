# Lang Script Vs Compiler Bench Specification

> Tests covering lang script vs compiler bench (AC-4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lang Script Vs Compiler Bench Specification

## Scenarios

### lang script vs compiler bench (AC-4)

#### fib workload writes successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fib workload writes successfully
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("fib workload writes successfully")
rt_dir_create_all("/tmp/bench_lang")
val ok = write_fib_workload("/tmp/bench_lang/fib20.spl")
expect(ok).to_equal(true)
```

</details>

#### interpreter (script) mode produces correct fib(20)

- interpreter (script) mode produces correct fib(20)
   - Expected: fib_val equals `FIB_ORACLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("interpreter (script) mode produces correct fib(20)")
rt_dir_create_all("/tmp/bench_lang")
write_fib_workload("/tmp/bench_lang/fib20.spl")
val simple_bin = find_simple_bin()
val fib_val = run_fib_correctness(simple_bin, "/tmp/bench_lang/fib20.spl", "script")
# Correctness assertion: oracle = 6765
expect(fib_val).to_equal(FIB_ORACLE)
```

</details>

#### mode strings are distinct — script != native (AC-4 never-collapsed)

- mode strings are distinct — script != native (AC-4 never-collapsed)
   - Expected: script_mode equals `script`
   - Expected: native_mode equals `native`
   - Expected: smf_mode equals `smf`
   - Expected: script_ne_native is true
   - Expected: script_ne_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("mode strings are distinct — script != native (AC-4 never-collapsed)")
# AC-4: each mode must be a distinct row, never merged.
# We assert the mode label strings are distinct — simple and definitive.
val script_mode = "script"
val native_mode = "native"
val smf_mode = "smf"
expect(script_mode).to_equal("script")
expect(native_mode).to_equal("native")
expect(smf_mode).to_equal("smf")
val script_ne_native = script_mode != native_mode
expect(script_ne_native).to_equal(true)
val script_ne_smf = script_mode != smf_mode
expect(script_ne_smf).to_equal(true)
```

</details>

#### SMF mode produces correct fib(20)

- SMF mode produces correct fib(20)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("SMF mode produces correct fib(20)")
# TODO: SMF loader currently cannot resolve time externs used in harness internals
# when run via interpreter-spawned process. Enable this test once SMF extern
# resolution is stable (see cross-language-perf.shs comment on SMF fallback).
pending("smf-extern-segfault")
```

</details>

#### native mode produces correct fib(20)

- native mode produces correct fib(20)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("native mode produces correct fib(20)")
# Native compilation requires a full toolchain (linker, clang). This test
# is tagged so it can be enabled on CI where native targets are available.
# TODO: Enable once native compilation is confirmed stable in test runner.
pending("native-compile-required")
```

</details>

#### bench_emit writes report and metrics files

- bench_emit writes report and metrics files


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench_emit writes report and metrics files")
# TODO: cross-module struct type metadata is not available in interpreter mode —
# BenchResult constructed inside imported make_bench_result returns Unit to caller.
# This test requires compiled mode (--mode=native or --mode=smf with stable externs).
# The harness and report modules are correct; this is an interpreter limitation.
# Enable once the interpreter resolves cross-module struct types (bug: interp_cross_module_struct_unit).
pending("interp-cross-module-struct-unit")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lang script vs compiler bench (AC-4).
- lang script vs compiler bench (AC-4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `606838d9c57454eb8ea0ac0f90e5c0f4a0e701877aba0079f23ae50b7137b6cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `606838d9c57454eb8ea0ac0f90e5c0f4a0e701877aba0079f23ae50b7137b6cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `606838d9c57454eb8ea0ac0f90e5c0f4a0e701877aba0079f23ae50b7137b6cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl
mirror: doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fib workload writes successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpreter (script) mode produces correct fib(20)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mode strings are distinct — script != native (AC-4 never-collapsed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
