# test_analysis_log_modes_spec

> Purpose: This spec proves test analysis log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_analysis_log_modes_spec

Purpose: This spec proves test analysis log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/test_analysis_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves test analysis log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### test analysis log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTANALYSISLOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_test_analysis(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Test Failure Analysis")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

- supports log-mode json ready output
- supports log-mode json ready output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json ready output")
step("supports log-mode json ready output")
val (out, err, code) = _run_test_analysis(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"test-analysis\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json classification output

- supports json classification output
- supports json classification output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports json classification output")
step("supports json classification output")
val (out, err, code) = _run_test_analysis(["--log-mode=json", "classify", "parse error"])
expect(code).to_equal(0)
expect(out).to_contain("\"operation\":\"classify\"")
expect(out).to_contain("\"errorType\":\"parse_error\"")
```

</details>

#### supports json feature extraction output

- supports json feature extraction output
- supports json feature extraction output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports json feature extraction output")
step("supports json feature extraction output")
val (out, err, code) = _run_test_analysis(["--log-mode=json", "extract", "expected expression, found At"])
expect(code).to_equal(0)
expect(out).to_contain("\"operation\":\"extract\"")
expect(out).to_contain("\"feature\":\"matrix_multiplication\"")
```

</details>

#### supports json analyze planning

- supports json analyze planning
- supports json analyze planning
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports json analyze planning")
step("supports json analyze planning")
val (out, err, code) = _run_test_analysis(["--log-mode=json", "analyze", "--db=tmp.sdn"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"operation\":\"analyze\"")
```

</details>

#### supports dot progress for help output

- supports dot progress for help output
- supports dot progress for help output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for help output")
step("supports dot progress for help output")
val (out, err, code) = _run_test_analysis(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nTest Failure Analysis")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
val (out, err, code) = _run_test_analysis(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing message output

- renders json missing message output
- renders json missing message output
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders json missing message output")
step("renders json missing message output")
val (out, err, code) = _run_test_analysis(["--log-mode=json", "classify"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Command classify requires an error message")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-TESTANALYSISLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d614b821c16f4b745e643ecd89bdc204622d0286c5bae001456c6182434b50b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d614b821c16f4b745e643ecd89bdc204622d0286c5bae001456c6182434b50b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d614b821c16f4b745e643ecd89bdc204622d0286c5bae001456c6182434b50b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/test_analysis_log_modes_spec.spl
mirror: doc/06_spec/integration/app/test_analysis_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/test_analysis_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/test_analysis_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/test_analysis_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/test_analysis_log_modes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/test_analysis_log_modes_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json ready output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/test_analysis_log_modes_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports json classification output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
