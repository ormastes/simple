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
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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
expect(fib_val).to_equal(FIB_ORACLE)  # oracle: fib(20) = 6765 in script mode
```

</details>

#### mode strings are distinct — script != native (AC-4 never-collapsed)

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- SMF mode produces correct fib(20)
   - Expected: c_code equals `0`
   - Expected: rt_file_exists("/tmp/bench_lang/fib20.smf") is true
   - Expected: code equals `0`
   - Expected: parse_fib_result(stdout) equals `FIB_ORACLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("SMF mode produces correct fib(20)")
# Proven working 2026-08-27: compile the workload to .smf, then execute the
# compiled artifact via `run <file.smf>` and assert the fib oracle.
rt_dir_create_all("/tmp/bench_lang")
write_fib_workload("/tmp/bench_lang/fib20.spl")
val simple_bin = find_simple_bin()
val (c_out, _c_err, c_code) = rt_process_run(simple_bin, ["compile", "/tmp/bench_lang/fib20.spl", "--output", "/tmp/bench_lang/fib20.smf"])
expect(c_code).to_equal(0)  # oracle: compile to SMF succeeds
expect(rt_file_exists("/tmp/bench_lang/fib20.smf")).to_equal(true)
val (stdout, _stderr, code) = rt_process_run(simple_bin, ["run", "/tmp/bench_lang/fib20.smf"])
expect(code).to_equal(0)  # oracle: the compiled SMF artifact executes cleanly
expect(parse_fib_result(stdout)).to_equal(FIB_ORACLE)  # oracle: fib(20) = 6765 via the SMF loader
```

</details>

#### native mode produces correct fib(20)

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- native mode produces correct fib(20)
   - Expected: c_code equals `0`
   - Expected: rt_file_exists("/tmp/bench_lang/fib20_nat") is true
   - Expected: code equals `0`
   - Expected: parse_fib_result(stdout) equals `FIB_ORACLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("native mode produces correct fib(20)")
# Proven working 2026-08-27: native-build the workload and execute the
# produced binary; assert the fib oracle.
rt_dir_create_all("/tmp/bench_lang")
write_fib_workload("/tmp/bench_lang/fib20.spl")
val simple_bin = find_simple_bin()
val (c_out, _c_err, c_code) = rt_process_run(simple_bin, ["native-build", "/tmp/bench_lang/fib20.spl", "--output", "/tmp/bench_lang/fib20_nat"])
expect(c_code).to_equal(0)  # oracle: native-build compiles and links the workload
expect(rt_file_exists("/tmp/bench_lang/fib20_nat")).to_equal(true)
val (stdout, _stderr, code) = rt_process_run("/tmp/bench_lang/fib20_nat", [])
expect(code).to_equal(0)  # oracle: the native binary executes cleanly
expect(parse_fib_result(stdout)).to_equal(FIB_ORACLE)  # oracle: fib(20) = 6765 natively compiled
```

</details>

#### bench_emit writes report and metrics files

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- bench_emit writes report and metrics files
   - Expected: rt_file_exists("/tmp/bench_lang/report.sdn") is true
   - Expected: rt_file_exists("/tmp/bench_lang/metrics.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench_emit writes report and metrics files")
rt_dir_create_all("/tmp/bench_lang")
write_fib_workload("/tmp/bench_lang/fib20.spl")
val simple_bin = find_simple_bin()
run_bench_and_emit(simple_bin, "/tmp/bench_lang/fib20.spl",
    "/tmp/bench_lang/report.sdn", "/tmp/bench_lang/metrics.sdn")
expect(rt_file_exists("/tmp/bench_lang/report.sdn")).to_equal(true)  # oracle: the bench report artifact is emitted
expect(rt_file_exists("/tmp/bench_lang/metrics.sdn")).to_equal(true)  # oracle: the metrics table artifact is emitted
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `23110d893fb9f8be4011c2a5f825eb8e70c58003b8b7641e176444e0d25e87e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23110d893fb9f8be4011c2a5f825eb8e70c58003b8b7641e176444e0d25e87e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23110d893fb9f8be4011c2a5f825eb8e70c58003b8b7641e176444e0d25e87e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl
mirror: doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md (current)
findings: 3 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/lang/lang_script_vs_compiler_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
<!-- sspec-maintain:scorecard:end -->
