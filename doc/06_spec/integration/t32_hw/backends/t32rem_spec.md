# T32 Backend: t32rem CLI

> Tests core T32 operations using the t32rem CLI backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Backend: t32rem CLI

Tests core T32 operations using the t32rem CLI backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/backends/t32rem_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests core T32 operations using the t32rem CLI backend.

## Scenarios

### T32 via t32rem backend

#### when t32rem is available

#### t32rem binary exists

- t32rem binary exists
   - Expected: t32_hw_t32rem_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("t32rem binary exists")
expect(t32_hw_t32rem_available()).to_equal(true)
```

</details>

#### connects and pings

- connects and pings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects and pings")
shared_test_connect_and_ping()
```

</details>

#### evaluates VERSION.BUILD()

- evaluates VERSION.BUILD()


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evaluates VERSION.BUILD()")
shared_test_eval_version()
```

</details>

#### runs PRACTICE command

- runs PRACTICE command


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs PRACTICE command")
shared_test_cmd_run()
```

</details>

#### queries STATE.RUN()

- queries STATE.RUN()


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queries STATE.RUN()")
shared_test_state_query()
```

</details>

#### reads PC register

- reads PC register


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads PC register")
shared_test_register_read()
```

</details>

#### halt-step-halt cycle

- halt-step-halt cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("halt-step-halt cycle")
shared_test_step_and_halt()
```

</details>

#### recovers from error

- recovers from error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recovers from error")
shared_test_error_recovery()
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `306550f62e599f5dd6dacd7d1d070081c2828c01c1bac13e7cbfc87c5bec4eb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `306550f62e599f5dd6dacd7d1d070081c2828c01c1bac13e7cbfc87c5bec4eb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `306550f62e599f5dd6dacd7d1d070081c2828c01c1bac13e7cbfc87c5bec4eb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/backends/t32rem_spec.spl
mirror: doc/06_spec/integration/t32_hw/backends/t32rem_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/backends/t32rem_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/backends/t32rem_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/backends/t32rem_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't32rem binary exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/backends/t32rem_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects and pings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/backends/t32rem_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates VERSION.BUILD()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
