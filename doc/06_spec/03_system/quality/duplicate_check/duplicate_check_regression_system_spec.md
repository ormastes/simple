# Duplicate Check Regression System Specification

> Tests covering duplicate-check system regressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Regression System Specification

## Scenarios

### duplicate-check system regressions

<details>
<summary>Advanced: executes the CLI regression unit spec end-to-end</summary>

#### executes the CLI regression unit spec end-to-end _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes the CLI regression unit spec end-to-end
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes the CLI regression unit spec end-to-end")
val (stdout, _, code) = run_spec("test/unit/app/duplicate_check/duplicate_check_spec.spl")

expect(code).to_equal(0)
expect(stdout).to_contain("Passed:")
expect(stdout).to_contain("All tests passed")
```

</details>


</details>

<details>
<summary>Advanced: executes semantic fallback regressions end-to-end</summary>

#### executes semantic fallback regressions end-to-end _(slow)_

- executes semantic fallback regressions end-to-end
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes semantic fallback regressions end-to-end")
val (stdout, _, code) = run_spec("test/system/duplicate_check/semantic_fallback_probe_spec.spl")

expect(code).to_equal(0)
expect(stdout).to_contain("Passed:")
expect(stdout).to_contain("All tests passed")
```

</details>


</details>

<details>
<summary>Advanced: runs semantic analysis by default for bare duplicate-check invocations</summary>

#### runs semantic analysis by default for bare duplicate-check invocations _(slow)_

- runs semantic analysis by default for bare duplicate-check invocations
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs semantic analysis by default for bare duplicate-check invocations")
val root = "/tmp/simple_duplicate_check_system_default"
make_cli_fixture(root)

val (stdout, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--semantic-threshold",
    "0.70",
    "--ollama-url",
    "http://127.0.0.1:9"
])

expect(code).to_equal(1)
expect(stdout).to_contain("Source: 2 items, 2 documented")
expect(stdout).to_contain("Summary: 2 total, 2 documented")
expect(stdout).to_contain("[text-based fallback]")
```

</details>


</details>

<details>
<summary>Advanced: runs token mode for 5-line code duplication</summary>

#### runs token mode for 5-line code duplication _(slow)_

- runs token mode for 5-line code duplication
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs token mode for 5-line code duplication")
val root = "/tmp/simple_duplicate_check_system_token"
make_token_fixture(root)

val (_, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--mode",
    "token",
    "--min-lines",
    "5",
    "--min-tokens",
    "8"
])

expect(code).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: runs cosine mode for fuzzy duplication</summary>

#### runs cosine mode for fuzzy duplication _(slow)_

- runs cosine mode for fuzzy duplication
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs cosine mode for fuzzy duplication")
val root = "/tmp/simple_duplicate_check_system_cosine"
make_cosine_fixture(root)

val (_, _, code) = rt_process_run("bin/simple", [
    "duplicate-check",
    root,
    "--mode",
    "cosine",
    "--min-lines",
    "5",
    "--min-tokens",
    "8",
    "--similarity-threshold",
    "0.55"
])

expect(code).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: falls back cleanly in bootstrap semantic mode without HTTP extern support</summary>

#### falls back cleanly in bootstrap semantic mode without HTTP extern support _(slow)_

- falls back cleanly in bootstrap semantic mode without HTTP extern support
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back cleanly in bootstrap semantic mode without HTTP extern support")
val (_, _, code) = run_bootstrap([
    "run",
    "src/compiler/90.tools/duplicate_check/main.spl",
    "src/compiler/90.tools/duplicate_check",
    "--semantic",
    "--semantic-threshold",
    "0.7",
    "--ollama-url",
    "http://127.0.0.1:9"
])

expect(code).to_equal(0)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate-check system regressions.
- duplicate-check system regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4aa2dcdf5bf3e15e209ffc3545b540f97beb2171379c535bde323edc4403ed03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4aa2dcdf5bf3e15e209ffc3545b540f97beb2171379c535bde323edc4403ed03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4aa2dcdf5bf3e15e209ffc3545b540f97beb2171379c535bde323edc4403ed03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl
mirror: doc/06_spec/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the CLI regression unit spec end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes semantic fallback regressions end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs semantic analysis by default for bare duplicate-check invocations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
