# Test Runner Result Wrapper Specification

> Tests covering interpreter test result wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Result Wrapper Specification

## Scenarios

### interpreter test result wrapper

#### adds summary and fail-closed result checks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adds summary and fail-closed result checks
   - Expected: file_write(source_path, "describe \"sample\":\n    it \"passes\":\n        expect(1 equals `1)\n")).to_be(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds summary and fail-closed result checks")
val source_path = "/tmp/simple_result_wrapper_{time_now_unix_micros()}_spec.spl"
expect(file_write(source_path, "describe \"sample\":\n    it \"passes\":\n        expect(1).to_equal(1)\n")).to_be(true)

val (wrapped_path, cleanup_path) = build_interpreter_result_wrapper(source_path)
val wrapped = file_read(wrapped_path)
expect(wrapped).to_start_with("use std.spec.{print_summary, get_exit_code, get_executed_test_count}")
expect(wrapped).to_contain("print_summary()")
expect(wrapped).to_contain("get_executed_test_count() == 0")
expect(wrapped).to_contain("get_exit_code() != 0")
expect(wrapped).to_contain("print_summary()\nif get_executed_test_count() == 0:")
expect(wrapped).to_contain("panic(\"test-runner: no examples executed\")\nif get_exit_code() != 0:")

expect(file_delete(cleanup_path)).to_be(true)
expect(file_delete(source_path)).to_be(true)
```

</details>

#### fails closed for a missing source

- fails closed for a missing source
   - Expected: wrapped_path equals ``
   - Expected: cleanup_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for a missing source")
val (wrapped_path, cleanup_path) = build_interpreter_result_wrapper("/tmp/simple_missing_result_wrapper_spec.spl")
expect(wrapped_path).to_equal("")
expect(cleanup_path).to_equal("")
```

</details>

#### accepts only coherent native summaries and one completion marker

- accepts only coherent native summaries and one completion marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only coherent native summaries and one completion marker")
val marker = "test-runner: native result wrapper complete"
val green = "sample\n1 examples, 0 failures\n{marker}\n"
val red = "sample\n1 examples, 1 failures\n{marker}\nerror: test-runner: spec failed\n"
expect(valid_native_result(green, 0)).to_be(true)
expect(valid_native_result(red, 1)).to_be(true)
expect(valid_native_result(red + "junk\n", 1)).to_be(false)
expect(valid_native_result("sample\n1 examples, 1 failures\n{marker}\nprefix test-runner: spec failed suffix\n", 1)).to_be(false)
expect(valid_native_result(green, 1)).to_be(false)
expect(valid_native_result(red, 0)).to_be(false)
expect(valid_native_result("sample\n1 examples, 0 failures\n", 0)).to_be(false)
expect(valid_native_result("sample\n1 examples, 0 failures\n{marker}\n{marker}\n", 0)).to_be(false)
expect(valid_native_result("sample\n01 examples, 00 failures\n{marker}\n", 0)).to_be(true)
expect(valid_native_result("sample\n2 examples, 10 failures\n{marker}\ntest-runner: spec failed\n", 1)).to_be(false)
expect(valid_native_result("sample\nx examples, 0 failures\n{marker}\n", 0)).to_be(false)
```

</details>

#### keeps the focused runner on the fail-closed pure native route

- keeps the focused runner on the fail-closed pure native route


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the focused runner on the fail-closed pure native route")
val runner = file_read("src/app/test/font_evidence_runner.spl")
expect(runner).to_contain("<pure-simple-compiler> <compiler-sha256> <core-c-runtime-dir> <runtime-sha256> <spec.spl>")
expect(runner).to_contain("preprocess_spipe_native_result_file(spec)")
expect(runner).to_contain("use std.test_runner.test_result_wrapper.{preprocess_spipe_native_result_file}")
expect(runner.contains("use std.test_runner.test_runner_execute")).to_be(false)
expect(runner).to_contain("SIMPLE_NATIVE_SPEC_MODE")
expect(runner).to_contain("SIMPLE_EXECUTION_MODE=")
expect(runner).to_contain("SIMPLE_BOOTSTRAP_STAGE4=0")
expect(runner).to_contain("\"-i\"")
expect(runner).to_contain("PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin")
expect(runner).to_contain("--runtime-bundle\", \"core-c-bootstrap")
expect(runner).to_contain("rt_bdd_executed_count")
expect(runner).to_contain("test-runner: native result wrapper complete")
expect(runner).to_contain("val marker_at = stdout.index_of(marker)")
expect(runner).to_contain("if marker_at < 0:")
expect(runner).to_contain("after_marker.contains(marker)")
expect(runner.contains("stdout.split(marker)")).to_be(false)
expect(runner).to_contain("decimal_text_valid(examples)")
expect(runner).to_contain("decimal_text_lte(failures, examples)")
expect(runner.contains("fields[0].to_i64()")).to_be(false)
expect(runner.contains("fields[2].to_i64()")).to_be(false)
expect(runner).to_contain("run_bounded(\"300s\", \"/usr/bin/env\", build_env_args)")
expect(runner).to_contain("compiler_sha != expected_compiler_sha")
expect(runner).to_contain("archive_sha != expected_archive_sha")
expect(runner).to_contain("wrapped_sha = file_sha256(wrapped)")
expect(runner).to_contain("file_sha256(wrapped) == wrapped_sha")
expect(runner).to_contain("cache_key = expected_archive_sha + \"-\" + wrapped_sha")
expect(runner.contains("substring(0, 16)")).to_be(false)
expect(runner).to_contain("\"build/native_probe/font-spec-cache-\" + cache_key")
expect(runner).to_contain("pure_compiler_route_valid(compiler)")
expect(runner).to_contain("defines_symbols(native")
expect(runner).to_contain("file_sha256(native) == native_sha")
expect(runner).to_contain("compiler/runtime provider changed during build")
expect(runner).to_contain("run_bounded(\"15s\", \"/usr/bin/unlink\", [path])")
expect(runner.contains("file_delete")).to_be(false)
expect(runner).to_contain("eprint stderr")
expect(runner).to_contain("return 124")
expect(runner.contains("build_interpreter_result_wrapper")).to_be(false)
expect(runner.contains("process_run_timeout")).to_be(false)
expect(runner).to_contain("compiler.contains(\"compiler_rust\")")
expect(runner.contains("interpret_file")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner_result_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter test result wrapper.
- interpreter test result wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60c8e85aba745f12b1f8c34d4960709f9f9c1851f5ca887e8a8f7a62131ec92e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60c8e85aba745f12b1f8c34d4960709f9f9c1851f5ca887e8a8f7a62131ec92e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60c8e85aba745f12b1f8c34d4960709f9f9c1851f5ca887e8a8f7a62131ec92e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/test_runner_result_wrapper_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner_result_wrapper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner_result_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner_result_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner_result_wrapper_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds summary and fail-closed result checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner_result_wrapper_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for a missing source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner_result_wrapper_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only coherent native summaries and one completion marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
