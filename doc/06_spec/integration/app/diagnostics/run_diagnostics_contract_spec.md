# `simple run` diagnostic contract

> Exercises the real interpreted run path for runtime-facing diagnostics so stable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `simple run` diagnostic contract

Exercises the real interpreted run path for runtime-facing diagnostics so stable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/diagnostics/run_diagnostics_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the real interpreted run path for runtime-facing diagnostics so stable
codes and help text are not lost in process-level error rendering.

## Scenarios

### `simple run` diagnostics

#### prints stable undefined function code and help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prints stable undefined function code and help
   - Expected: code equals `1`
   - Expected: combined does not contain `semantic:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints stable undefined function code and help")
seed_undefined_function_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", UNDEFINED_FUNCTION_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E1002]")
expect(combined).to_contain("function `missing_function` not found")
expect(combined).to_contain("= help: check the function name or import the module that defines it")
expect(combined.contains("semantic:")).to_equal(false)
```

</details>

#### prints stable division by zero code and help

- prints stable division by zero code and help
   - Expected: code equals `1`
   - Expected: combined does not contain `semantic:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints stable division by zero code and help")
seed_division_by_zero_source()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", DIVISION_BY_ZERO_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E2001]")
expect(combined).to_contain("division by zero")
expect(combined).to_contain("= help: check the divisor before dividing")
expect(combined.contains("semantic:")).to_equal(false)
```

</details>

#### prints stable missing file code and help

- prints stable missing file code and help
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prints stable missing file code and help")
remove_missing_run_fixture()

val (stdout, stderr, code) = rt_process_run(SIMPLE_BIN, ["run", MISSING_RUN_FIXTURE_PATH])
val combined = stdout + stderr

expect(code).to_equal(1)
expect(combined).to_contain("error[E0001]")
expect(combined).to_contain("cannot read file")
expect(combined).to_contain("= help: check that the path exists and is readable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fff6b0432d6f3d4111ba7555bcabe1e32afd6bf36f98acd9206534645e7ca40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fff6b0432d6f3d4111ba7555bcabe1e32afd6bf36f98acd9206534645e7ca40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fff6b0432d6f3d4111ba7555bcabe1e32afd6bf36f98acd9206534645e7ca40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/diagnostics/run_diagnostics_contract_spec.spl
mirror: doc/06_spec/integration/app/diagnostics/run_diagnostics_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/diagnostics/run_diagnostics_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/diagnostics/run_diagnostics_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/diagnostics/run_diagnostics_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/diagnostics/run_diagnostics_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints stable undefined function code and help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/diagnostics/run_diagnostics_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints stable division by zero code and help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/diagnostics/run_diagnostics_contract_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints stable missing file code and help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
