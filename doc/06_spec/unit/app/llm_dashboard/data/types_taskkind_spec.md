# Types Taskkind Specification

> Tests covering TaskKind.Job variant.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Taskkind Specification

## Scenarios

### TaskKind.Job variant

#### task_kind_name returns job for TaskKind.Job

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- task_kind_name returns job for TaskKind.Job
   - Expected: name equals `job`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("task_kind_name returns job for TaskKind.Job")
val name = task_kind_name(TaskKind.Job)
expect(name).to_equal("job")
```

</details>

<details>
<summary>Advanced: existing Loop variant still works</summary>

#### existing Loop variant still works

- existing Loop variant still works
   - Expected: task_kind_name(TaskKind.Loop) equals `loop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("existing Loop variant still works")
expect(task_kind_name(TaskKind.Loop)).to_equal("loop")
```

</details>


</details>

#### existing Schedule variant still works

- existing Schedule variant still works
   - Expected: task_kind_name(TaskKind.Schedule) equals `schedule`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("existing Schedule variant still works")
expect(task_kind_name(TaskKind.Schedule)).to_equal("schedule")
```

</details>

#### existing Daemon variant still works

- existing Daemon variant still works
   - Expected: task_kind_name(TaskKind.Daemon) equals `daemon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("existing Daemon variant still works")
expect(task_kind_name(TaskKind.Daemon)).to_equal("daemon")
```

</details>

#### existing RemoteControl variant still works

- existing RemoteControl variant still works
   - Expected: task_kind_name(TaskKind.RemoteControl) equals `remote`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("existing RemoteControl variant still works")
expect(task_kind_name(TaskKind.RemoteControl)).to_equal("remote")
```

</details>

#### ManagedTask can be constructed with kind Job

- ManagedTask can be constructed with kind Job
   - Expected: task_kind_name(task.kind) equals `job`
   - Expected: task.id equals `id1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ManagedTask can be constructed with kind Job")
val task = ManagedTask.new("id1", TaskKind.Job, "test job", "bin/simple test")
expect(task_kind_name(task.kind)).to_equal("job")
expect(task.id).to_equal("id1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/data/types_taskkind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TaskKind.Job variant.
- TaskKind.Job variant

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

- Canonical SPipe generation for source `5751424ad82a4f33431e7c51b98f581eebec77c31aa20167f5e2ad3f00f09453`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5751424ad82a4f33431e7c51b98f581eebec77c31aa20167f5e2ad3f00f09453`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5751424ad82a4f33431e7c51b98f581eebec77c31aa20167f5e2ad3f00f09453`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_dashboard/data/types_taskkind_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/data/types_taskkind_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/data/types_taskkind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/data/types_taskkind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/data/types_taskkind_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'task_kind_name returns job for TaskKind.Job' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/data/types_taskkind_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'existing Loop variant still works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/data/types_taskkind_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'existing Schedule variant still works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
