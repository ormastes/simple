# multi_mode_test_runner_spec

> Verifies the multi mode test runner behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# multi_mode_test_runner_spec

Verifies the multi mode test runner behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/multi_mode_test_runner_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the multi mode test runner behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Multi-Mode Test Runner Unit Tests

### TestExecutionMode

#### has Interpreter variant

- Verify: has Interpreter variant
   - Expected: name equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: has Interpreter variant")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.Interpreter
val name = execution_mode_to_string(mode)
expect(name).to_equal("interpreter")
```

</details>

#### has Smf variant

- Verify: has Smf variant
   - Expected: name equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: has Smf variant")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.Smf
val name = execution_mode_to_string(mode)
expect(name).to_equal("smf")
```

</details>

#### has Native variant

- Verify: has Native variant
   - Expected: name equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: has Native variant")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.Native
val name = execution_mode_to_string(mode)
expect(name).to_equal("native")
```

</details>

#### has AllModes variant

- Verify: has AllModes variant
   - Expected: name equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: has AllModes variant")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.AllModes
val name = execution_mode_to_string(mode)
expect(name).to_equal("all-modes")
```

</details>

#### composite is detected correctly

- Verify: composite is detected correctly
   - Expected: execution_mode_is_composite(mode) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: composite is detected correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.Composite("baremetal(riscv32)")
expect(execution_mode_is_composite(mode)).to_equal(true)
```

</details>

#### non-composite is detected correctly

- Verify: non-composite is detected correctly
   - Expected: execution_mode_is_composite(mode) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: non-composite is detected correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = TestExecutionMode.Interpreter
expect(execution_mode_is_composite(mode)).to_equal(false)
```

</details>

### execution_mode_from_string

#### parses interpreter

- Verify: parses interpreter
   - Expected: execution_mode_to_string(mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses interpreter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = execution_mode_from_string("interpreter")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

#### parses native

- Verify: parses native
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = execution_mode_from_string("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses smf

- Verify: parses smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses smf")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = execution_mode_from_string("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all

- Verify: parses all
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses all")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = execution_mode_from_string("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

- Verify: parses all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses all-modes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = execution_mode_from_string("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

### parse_mode_str

#### parses native string

- Verify: parses native string
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses native string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("native")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses binary as native

- Verify: parses binary as native
   - Expected: execution_mode_to_string(mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses binary as native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("binary")
expect(execution_mode_to_string(mode)).to_equal("native")
```

</details>

#### parses loader as smf

- Verify: parses loader as smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses loader as smf")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("loader")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses smf

- Verify: parses smf
   - Expected: execution_mode_to_string(mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses smf")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("smf")
expect(execution_mode_to_string(mode)).to_equal("smf")
```

</details>

#### parses all as all-modes

- Verify: parses all as all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses all as all-modes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("all")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### parses all-modes

- Verify: parses all-modes
   - Expected: execution_mode_to_string(mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses all-modes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("all-modes")
expect(execution_mode_to_string(mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter

- Verify: defaults to interpreter
   - Expected: execution_mode_to_string(mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: defaults to interpreter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mode = parse_mode_str("unknown")
expect(execution_mode_to_string(mode)).to_equal("interpreter")
```

</details>

### TestInitConfig

#### default has nil init_fn

- Verify: default has nil init_fn
   - Expected: config.init_fn == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: default has nil init_fn")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = test_init_config_default()
expect(config.init_fn == nil).to_equal(true)
```

</details>

#### default has nil init_module

- Verify: default has nil init_module
   - Expected: config.init_module == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: default has nil init_module")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = test_init_config_default()
expect(config.init_module == nil).to_equal(true)
```

</details>

#### default timeout is 30000

- Verify: default timeout is 30000
   - Expected: config.timeout_ms equals `30000)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: default timeout is 30000")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = test_init_config_default()
expect(config.timeout_ms).to_equal(30000)  # oracle: pinned constant asserted by this scenario
```

</details>

#### with_module sets module path

- Verify: with_module sets module path
   - Expected: config.init_module == nil is false
   - Expected: config.init_module.unwrap() equals `test/init.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: with_module sets module path")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = test_init_config_with_module("test/init.spl")
expect(config.init_module == nil).to_equal(false)
expect(config.init_module.unwrap()).to_equal("test/init.spl")
```

</details>

### TestFileResult

#### is_ok when no failures

- Verify: is_ok when no failures
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is_ok when no failures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = make_passing_result("test.spl")
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when failures exist

- Verify: is not ok when failures exist
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is not ok when failures exist")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = make_failing_result("test.spl")
expect(r.is_ok()).to_equal(false)
```

</details>

### TestRunResult

#### is_ok when total_failed is zero

- Verify: is_ok when total_failed is zero
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is_ok when total_failed is zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = make_passing_run_result()
expect(r.is_ok()).to_equal(true)
```

</details>

#### is not ok when total_failed > 0

- Verify: is not ok when total_failed > 0
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is not ok when total_failed > 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = make_failing_run_result()
expect(r.is_ok()).to_equal(false)
```

</details>

### TestModeResult

#### is_ok delegates to inner result

- Verify: is_ok delegates to inner result
   - Expected: mr.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is_ok delegates to inner result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mr = TestModeResult(
    mode: TestExecutionMode.Interpreter,
    result: make_passing_run_result(),
    duration_ms: 100
)
expect(mr.is_ok()).to_equal(true)
```

</details>

#### is not ok when inner result has failures

- Verify: is not ok when inner result has failures
   - Expected: mr.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: is not ok when inner result has failures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: summary contains mode names


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: summary contains mode names")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: summary contains pass/fail counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: summary contains pass/fail counts")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: parses --mode=native
   - Expected: execution_mode_to_string(opts.mode) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses --mode=native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val opts = parse_test_args(["--mode=native", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("native")
```

</details>

#### parses --mode=loader

- Verify: parses --mode=loader
   - Expected: execution_mode_to_string(opts.mode) equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses --mode=loader")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val opts = parse_test_args(["--mode=loader", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("smf")
```

</details>

#### parses --all-modes

- Verify: parses --all-modes
   - Expected: execution_mode_to_string(opts.mode) equals `all-modes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: parses --all-modes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val opts = parse_test_args(["--all-modes", "test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("all-modes")
```

</details>

#### defaults to interpreter mode

- Verify: defaults to interpreter mode
   - Expected: execution_mode_to_string(opts.mode) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-multi_mode_test_runner
step("Verify: defaults to interpreter mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val opts = parse_test_args(["test/"])
expect(execution_mode_to_string(opts.mode)).to_equal("interpreter")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cab3d440627fb94625b175c55d04281844a46dfc1c36138d0cef071d96ec7003`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cab3d440627fb94625b175c55d04281844a46dfc1c36138d0cef071d96ec7003`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cab3d440627fb94625b175c55d04281844a46dfc1c36138d0cef071d96ec7003`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/multi_mode_test_runner_spec.spl
mirror: doc/06_spec/01_unit/multi_mode_test_runner_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/multi_mode_test_runner_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/multi_mode_test_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/multi_mode_test_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
