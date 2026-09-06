# Process Run With Limits Cmd Quoting Specification

> Tests covering process_run_with_limits command-word quoting (row 573).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Run With Limits Cmd Quoting Specification

## Scenarios

### process_run_with_limits command-word quoting (row 573)

#### installs a fixture executable under a path containing a space

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- installs a fixture executable under a path containing a space


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("installs a fixture executable under a path containing a space")
# Positive control: without this the rest of the file proves nothing.
_install_fixture()
assert_equal(file_exists(_fixture_exe()), true)
```

</details>

#### process_run preserves argv through a spaced command path (baseline)

- process_run preserves argv through a spaced command path (baseline)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("process_run preserves argv through a spaced command path (baseline)")
_install_fixture()
val (stdout, stderr, code) = process_run(_fixture_exe(), ["hello world", "b"])
assert_equal(code, 0)
assert_contains(stdout, "ARG0=[hello world]")
assert_contains(stdout, "ARG1=[b]")
```

</details>

#### process_run_with_limits preserves argv through a spaced command path

- process_run_with_limits preserves argv through a spaced command path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("process_run_with_limits preserves argv through a spaced command path")
# THE REGRESSION. Before the fix this was exit 127 with an empty
# stdout and a `timeout: failed to run command` stderr.
_install_fixture()
val r = process_run_with_limits(_fixture_exe(), ["hello world", "b"], 5000, 0, 0, 0, 0)
assert_equal(r.exit_code, 0)
assert_contains(r.stdout, "ARG0=[hello world]")
assert_contains(r.stdout, "ARG1=[b]")
```

</details>

#### does not report a spaced command path as a limit violation

- does not report a spaced command path as a limit violation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report a spaced command path as a limit violation")
_install_fixture()
val r = process_run_with_limits(_fixture_exe(), ["hello world", "b"], 5000, 0, 0, 0, 0)
assert_equal(r.limit_exceeded, false)
assert_equal(r.limit_type, "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/process_run_with_limits_cmd_quoting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering process_run_with_limits command-word quoting (row 573).
- process_run_with_limits command-word quoting (row 573)

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

- Canonical SPipe generation for source `b4d0e2a813f54ad9338a68e7e4d28f7ad12218697e15715d370f3e0f39e5391c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4d0e2a813f54ad9338a68e7e4d28f7ad12218697e15715d370f3e0f39e5391c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4d0e2a813f54ad9338a68e7e4d28f7ad12218697e15715d370f3e0f39e5391c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/process_run_with_limits_cmd_quoting_spec.spl
mirror: doc/06_spec/01_unit/std/process_run_with_limits_cmd_quoting_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/process_run_with_limits_cmd_quoting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/process_run_with_limits_cmd_quoting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/process_run_with_limits_cmd_quoting_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs a fixture executable under a path containing a space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/process_run_with_limits_cmd_quoting_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'process_run preserves argv through a spaced command path (baseline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/process_run_with_limits_cmd_quoting_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'process_run_with_limits preserves argv through a spaced command path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
