# Async Host Task Identity Specification

> Tests covering async host scheduler task identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Host Task Identity Specification

## Scenarios

### async host scheduler task identity

#### uses fallback key outside scheduler polling

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses fallback key outside scheduler polling
   - Expected: current_scheduler_task_key("fallback-task") equals `fallback-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses fallback key outside scheduler polling")
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### uses scheduler owned task key while entered

- uses scheduler owned task key while entered
   - Expected: current_scheduler_task_key("fallback-task") equals `scheduler-task-42`
   - Expected: current_scheduler_task_key("fallback-task") equals `fallback-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses scheduler owned task key while entered")
val previous = enter_scheduler_task_id(42)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-42")
exit_scheduler_task_id(previous)
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### prefers scheduler task key in unified identity

- prefers scheduler task key in unified identity
   - Expected: current_unified_task_key("fallback-task") equals `scheduler-task-43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers scheduler task key in unified identity")
val previous = enter_scheduler_task_id(43)
expect(current_unified_task_key("fallback-task")).to_equal("scheduler-task-43")
exit_scheduler_task_id(previous)
```

</details>

#### restores nested scheduler task identity

- restores nested scheduler task identity
   - Expected: current_scheduler_task_key("fallback-task") equals `scheduler-task-7`
   - Expected: current_scheduler_task_key("fallback-task") equals `scheduler-task-9`
   - Expected: current_scheduler_task_key("fallback-task") equals `scheduler-task-7`
   - Expected: current_scheduler_task_key("fallback-task") equals `fallback-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores nested scheduler task identity")
val outer = enter_scheduler_task_id(7)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-7")
val inner = enter_scheduler_task_id(9)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-9")
exit_scheduler_task_id(inner)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-7")
exit_scheduler_task_id(outer)
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### allocates monotonically increasing scheduler task ids

- allocates monotonically increasing scheduler task ids
   - Expected: second equals `first + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates monotonically increasing scheduler task ids")
val first = allocate_scheduler_task_id()
val second = allocate_scheduler_task_id()
expect(second).to_equal(first + 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering async host scheduler task identity.
- async host scheduler task identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `53fdd986275f16cf78b41f58173f9db87de2fa220513885271d9a07aa9199cb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53fdd986275f16cf78b41f58173f9db87de2fa220513885271d9a07aa9199cb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53fdd986275f16cf78b41f58173f9db87de2fa220513885271d9a07aa9199cb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses fallback key outside scheduler polling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses scheduler owned task key while entered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers scheduler task key in unified identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
