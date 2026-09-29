# Result Wrapper Unit Specification

> Tests covering test_result_wrapper (hardening).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result Wrapper Unit Specification

## Scenarios

### test_result_wrapper (hardening)

#### reachable panic branches

#### includes BOTH fail-closed panic strings as reachable branches in the wrapped source

- includes BOTH fail-closed panic strings as reachable branches in the wrapped source
   - Expected: file_write(source_path, "describe \"sample\":\n    it \"passes\":\n        expect(1 equals `1)\n")).to_be(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes BOTH fail-closed panic strings as reachable branches in the wrapped source")
val source_path = "/tmp/simple_result_wrapper_hardening_{time_now_unix_micros()}_spec.spl"
expect(file_write(source_path, "describe \"sample\":\n    it \"passes\":\n        expect(1).to_equal(1)\n")).to_be(true)

val (wrapped_path, cleanup_path) = build_interpreter_result_wrapper(source_path)
val wrapped = file_read(wrapped_path)

expect(wrapped).to_contain("panic(\"test-runner: no examples executed\")")
expect(wrapped).to_contain("panic(\"test-runner: spec failed\")")
expect(wrapped).to_contain("if get_exit_code() != 0:\n    panic(\"test-runner: spec failed\")")

expect(file_delete(cleanup_path)).to_be(true)
expect(file_delete(source_path)).to_be(true)
```

</details>

#### wrapper/cleanup path contract

#### returns the same non-empty path for both the wrapped file and its cleanup target

- returns the same non-empty path for both the wrapped file and its cleanup target
   - Expected: file_write(source_path, "describe \"x\":\n    it \"y\":\n        expect(1 equals `1)\n")).to_be(true`
   - Expected: wrapped_path equals `cleanup_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the same non-empty path for both the wrapped file and its cleanup target")
val source_path = "/tmp/simple_result_wrapper_contract_{time_now_unix_micros()}_spec.spl"
expect(file_write(source_path, "describe \"x\":\n    it \"y\":\n        expect(1).to_equal(1)\n")).to_be(true)

val (wrapped_path, cleanup_path) = build_interpreter_result_wrapper(source_path)
assert_not_equal(wrapped_path, "")
expect(wrapped_path).to_equal(cleanup_path)

expect(file_delete(cleanup_path)).to_be(true)
expect(file_delete(source_path)).to_be(true)
```

</details>

#### produces distinct wrapper paths across successive calls on the same source (no collision)

- produces distinct wrapper paths across successive calls on the same source (no collision)
   - Expected: file_write(source_path, "describe \"x\":\n    it \"y\":\n        expect(1 equals `1)\n")).to_be(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces distinct wrapper paths across successive calls on the same source (no collision)")
val source_path = "/tmp/simple_result_wrapper_unique_{time_now_unix_micros()}_spec.spl"
expect(file_write(source_path, "describe \"x\":\n    it \"y\":\n        expect(1).to_equal(1)\n")).to_be(true)

val (wrapped_a, cleanup_a) = build_interpreter_result_wrapper(source_path)
val (wrapped_b, cleanup_b) = build_interpreter_result_wrapper(source_path)
assert_not_equal(wrapped_a, wrapped_b)

expect(file_delete(cleanup_a)).to_be(true)
expect(file_delete(cleanup_b)).to_be(true)
expect(file_delete(source_path)).to_be(true)
```

</details>

#### deliberate-red: unreadable input

#### fails closed to empty paths for a source that does not exist on disk

- fails closed to empty paths for a source that does not exist on disk
   - Expected: wrapped_path equals ``
   - Expected: cleanup_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to empty paths for a source that does not exist on disk")
val (wrapped_path, cleanup_path) = build_interpreter_result_wrapper("/tmp/simple_definitely_missing_result_wrapper_{time_now_unix_micros()}_spec.spl")
expect(wrapped_path).to_equal("")
expect(cleanup_path).to_equal("")
```

</details>

#### result_wrapper_path branch coverage (pure, no file I/O)

#### preserves the directory prefix when the input path has a slash

- preserves the directory prefix when the input path has a slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the directory prefix when the input path has a slash")
val wrapped = result_wrapper_path("dir/sub/spec.spl")
expect(wrapped).to_start_with("dir/sub/.simple_result_")
expect(wrapped).to_end_with("_spec.spl")
```

</details>

#### uses an empty directory prefix when the input path has no slash

- uses an empty directory prefix when the input path has no slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses an empty directory prefix when the input path has no slash")
val wrapped = result_wrapper_path("bare_name_no_slash_spec.spl")
expect(wrapped).to_start_with(".simple_result_")
expect(wrapped).to_end_with("_bare_name_no_slash_spec.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_result_wrapper (hardening).
- test_result_wrapper (hardening)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `707c453ea93e9609e9a1c7757399203357a999d8dc0e43dba133baab28f81fc0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `707c453ea93e9609e9a1c7757399203357a999d8dc0e43dba133baab28f81fc0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `707c453ea93e9609e9a1c7757399203357a999d8dc0e43dba133baab28f81fc0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/result_wrapper_unit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/result_wrapper_unit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/result_wrapper_unit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes BOTH fail-closed panic strings as reachable branches in the wrapped source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the same non-empty path for both the wrapped file and its cleanup target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces distinct wrapper paths across successive calls on the same source (no collision)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
