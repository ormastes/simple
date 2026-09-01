# Multi Mode Test Runner Specification

> Tests covering Multi-Mode Test Runner Unit Tests, TestExecutionMode, execution_mode_from_string, parse_mode_str, TestInitConfig, TestFileResult, TestRunResult, TestModeResult, TestAllModesResult, parse_test_args.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Mode Test Runner Specification

## Scenarios

### Multi-Mode Test Runner Unit Tests

### TestExecutionMode

#### has Interpreter variant

- has Interpreter variant
   - Expected: name equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Interpreter variant")
val mode = TestExecutionMode.Interpreter
val name = execution_mode_to_string(mode)
expect(name).to_equal("interpreter")
```

</details>

#### has Smf variant

- has Smf variant
   - Expected: name equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Smf variant")
val mode = TestExecutionMode.Smf
val name = execution_mode_to_string(mode)
expect(name).to_equal("smf")
```

</details>

#### has Native variant

- has Native variant
   - Expected: name equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Native variant")
val mode = TestExecutionMode.Native
val name = execution_mode_to_string(mode)
expect(name).to_equal("native")
```

</details>

#### has AllModes variant

- has AllModes variant
   - Expected: name equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has AllModes variant")
val mode = TestExecutionMode.AllModes
val name = execution_mode_to_string(mode)
expect(name).to_equal("all-modes")
```

</details>

#### composite is detected correctly

- composite is detected correctly
   - Expected: execution_mode_is_composite(mode) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("composite is detected correctly")
val mode = TestExecutionMode.Composite("baremetal(riscv32)")
expect(execution_mode_is_composite(mode)).to_equal(true)
```

</details>

#### non-composite is detected correctly

- non-composite is detected correctly
   - Expected: execution_mode_is_composite(mode) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-composite is detected correctly")
val mode = TestExecutionMode.Interpreter
expect(execution_mode_is_composite(mode)).to_equal(false)
```

</details>

### execution_mode_from_string

#### parses interpreter

- parses interpreter
   - Expected: execution_mode_to_string(mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses interpreter")
val mode = execution_mode_from_string("interpreter")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

#### parses native

- parses native
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses native")
val mode = execution_mode_from_string("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses smf

- parses smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses smf")
val mode = execution_mode_from_string("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all

- parses all
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses all")
val mode = execution_mode_from_string("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

- parses all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses all-modes")
val mode = execution_mode_from_string("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

### parse_mode_str

#### parses native string

- parses native string
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses native string")
val mode = parse_mode_str("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses binary as native

- parses binary as native
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses binary as native")
val mode = parse_mode_str("binary")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses loader as smf

- parses loader as smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses loader as smf")
val mode = parse_mode_str("loader")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses smf

- parses smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses smf")
val mode = parse_mode_str("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all as all-modes

- parses all as all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses all as all-modes")
val mode = parse_mode_str("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

- parses all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses all-modes")
val mode = parse_mode_str("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter

- defaults to interpreter
   - Expected: execution_mode_to_string(mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to interpreter")
val mode = parse_mode_str("unknown")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

### TestInitConfig

#### default has nil init_fn

- default has nil init_fn
   - Expected: config.init_fn == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default has nil init_fn")
val config = test_init_config_default()
expect(config.init_fn == nil).to_equal(true)
```

</details>

#### default has nil init_module

- default has nil init_module
   - Expected: config.init_module == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default has nil init_module")
val config = test_init_config_default()
expect(config.init_module == nil).to_equal(true)
```

</details>

#### default timeout is 30000

- default timeout is 30000
   - Expected: config.timeout_ms equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default timeout is 30000")
val config = test_init_config_default()
expect(config.timeout_ms).to_equal(30000)
```

</details>

#### with_module sets module path

- with_module sets module path
   - Expected: config.init_module == nil is false
   - Expected: config.init_module.unwrap() equals `test/init.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_module sets module path")
val config = test_init_config_with_module("test/init.spl")
expect(config.init_module == nil).to_equal(false)
expect(config.init_module.unwrap()).to_equal("test/init.spl")
```

</details>

### TestFileResult

#### is_ok when no failures

- is_ok when no failures
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok when no failures")
val r = make_passing_result("test.spl")
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when failures exist

- is not ok when failures exist
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not ok when failures exist")
val r = make_failing_result("test.spl")
expect(r.is_ok()).to_equal(false)
```

</details>

### TestRunResult

#### is_ok when total_failed is zero

- is_ok when total_failed is zero
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok when total_failed is zero")
val r = make_passing_run_result()
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when total_failed > 0

- is not ok when total_failed > 0
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not ok when total_failed > 0")
val r = make_failing_run_result()
expect(r.is_ok()).to_equal(false)
```

</details>

### TestModeResult

#### is_ok delegates to inner result

- is_ok delegates to inner result
   - Expected: mr.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok delegates to inner result")
val mr = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
expect(mr.is_ok()).to_equal(true)
```

</details>

#### is not ok when inner result has failures

- is not ok when inner result has failures
   - Expected: mr.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not ok when inner result has failures")
val mr = TestModeResult(
    mode: TestExecutionMode.Native,
    result: make_failing_run_result(),
    duration_ms: 200
)
expect(mr.is_ok()).to_equal(false)
```

</details>

### TestAllModesResult

#### summary contains mode names

- summary contains mode names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("summary contains mode names")
val mr1 = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
val all = TestAllModesResult(mode_results: [mr1], all_passed: true)
val s = all.summary()
expect(s).to_contain("interpreter")
```

</details>

#### summary contains pass/fail counts

- summary contains pass/fail counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("summary contains pass/fail counts")
val mr1 = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
val all = TestAllModesResult(mode_results: [mr1], all_passed: true)
val s = all.summary()
expect(s).to_contain("5 passed")
expect(s).to_contain("0 failed")
```

</details>

### parse_test_args

#### parses --mode=native

- parses --mode=native
   - Expected: execution_mode_to_string(opts.mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --mode=native")
val opts = parse_test_args(["--mode=native", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("native")
```

</details>

#### parses --mode=loader

- parses --mode=loader
   - Expected: execution_mode_to_string(opts.mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --mode=loader")
val opts = parse_test_args(["--mode=loader", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("smf")
```

</details>

#### parses --all-modes

- parses --all-modes
   - Expected: execution_mode_to_string(opts.mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses --all-modes")
val opts = parse_test_args(["--all-modes", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter mode

- defaults to interpreter mode
   - Expected: execution_mode_to_string(opts.mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to interpreter mode")
val opts = parse_test_args(["test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("interpreter")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/multi_mode_test_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multi-Mode Test Runner Unit Tests, TestExecutionMode, execution_mode_from_string, parse_mode_str, TestInitConfig, TestFileResult, TestRunResult, TestModeResult, TestAllModesResult, parse_test_args.
- Multi-Mode Test Runner Unit Tests
- TestExecutionMode
- execution_mode_from_string
- parse_mode_str
- TestInitConfig
- TestFileResult
- TestRunResult
- TestModeResult
- TestAllModesResult
- parse_test_args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-multi_mode_test_runner`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52ad434dc82b428f46730dd5b59bdf36deeab5853b8693598edb125a6047a504`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52ad434dc82b428f46730dd5b59bdf36deeab5853b8693598edb125a6047a504`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52ad434dc82b428f46730dd5b59bdf36deeab5853b8693598edb125a6047a504`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/multi_mode_test_runner_spec.spl
mirror: doc/06_spec/unit/multi_mode_test_runner_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/unit/multi_mode_test_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/multi_mode_test_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/multi_mode_test_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/multi_mode_test_runner_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/multi_mode_test_runner_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Interpreter variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/multi_mode_test_runner_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Smf variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/multi_mode_test_runner_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Native variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
