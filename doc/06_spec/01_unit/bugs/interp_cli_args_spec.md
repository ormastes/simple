# Interp Cli Args Specification

> Tests covering rt_cli_get_args() runtime args bug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Cli Args Specification

## Scenarios

### rt_cli_get_args() runtime args bug

#### demonstrates the stripping workaround

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- demonstrates the stripping workaround
   - Expected: _len(user_args) equals `2`
   - Expected: _get(user_args, 0) equals `--flag`
   - Expected: _get(user_args, 1) equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("demonstrates the stripping workaround")
# Build the array directly (var: [text] = [] broken in it blocks)
val simulated_raw = ["simple", "run", "test/example.spl", "--flag", "value"]
val user_args = strip_runtime_args(simulated_raw)
expect(_len(user_args)).to_equal(2)
expect(_get(user_args, 0)).to_equal("--flag")
expect(_get(user_args, 1)).to_equal("value")
```

</details>

#### handles no script path gracefully

- handles no script path gracefully
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("handles no script path gracefully")
val no_script = ["--something"]
val result = strip_runtime_args(no_script)
expect(result.len()).to_equal(0)
```

</details>

#### handles empty args

- handles empty args
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("handles empty args")
val empty = _empty_text_list()
val result = strip_runtime_args(empty)
expect(result.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_cli_args_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_cli_get_args() runtime args bug.
- rt_cli_get_args() runtime args bug

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

- `REQ-SSPEC-BUGS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a4431cb79fd5eb47c453aab19c51651a2c4ff8a7c8771af3f0d1323e5693098`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a4431cb79fd5eb47c453aab19c51651a2c4ff8a7c8771af3f0d1323e5693098`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a4431cb79fd5eb47c453aab19c51651a2c4ff8a7c8771af3f0d1323e5693098`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/interp_cli_args_spec.spl
mirror: doc/06_spec/01_unit/bugs/interp_cli_args_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/interp_cli_args_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/interp_cli_args_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/interp_cli_args_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/interp_cli_args_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates the stripping workaround' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/interp_cli_args_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles no script path gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/interp_cli_args_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
