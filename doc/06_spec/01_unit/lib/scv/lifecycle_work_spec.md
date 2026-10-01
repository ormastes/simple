# lifecycle_work_spec

> Feature, task, and ephemeral run identities remain separate and linked.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_work_spec

Feature, task, and ephemeral run identities remain separate and linked.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/scv/lifecycle_work_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature, task, and ephemeral run identities remain separate and linked.

## Scenarios

### Unified lifecycle work graph

#### links durable work without promoting run state into feature truth

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- links durable work without promoting run state into feature truth
- Create distinct feature and task identities
   - Expected: lifecycle_feature_validate(feature).status equals `feature_valid`
   - Expected: lifecycle_task_validate(task, feature).status equals `task_valid`
   - Expected: lifecycle_run_validate(run, task).status equals `run_valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("links durable work without promoting run state into feature truth")
step("Create distinct feature and task identities")
val feature = Feature(feature_id: "FEAT-1", title: "Unified lifecycle", state: "implementing", owner: "dev-infra", goal: "typed lifecycle", acceptance_ids: ["AC-1"], document_paths: ["doc/04_architecture/lifecycle.md"], task_ids: ["TASK-1"])
val task = Task(task_id: "TASK-1", feature_id: "FEAT-1", title: "Implement base", state: "active", owner: "agent", change_ids: ["chg_1"])
val run = LifecycleRun(run_id: "RUN-1", feature_id: "FEAT-1", task_id: "TASK-1", change_id: "chg_1", base_revision_id: "rev_base", state: "running")
expect(lifecycle_feature_validate(feature).status).to_equal("feature_valid")
expect(lifecycle_task_validate(task, feature).status).to_equal("task_valid")
expect(lifecycle_run_validate(run, task).status).to_equal("run_valid")
expect(lifecycle_record_decode(lifecycle_record_encode(lifecycle_feature_record(feature))).ok).to_be(true)
```

</details>

#### rejects a run that reuses durable task identity

- rejects a run that reuses durable task identity
   - Expected: lifecycle_run_validate(run, task).code equals `LIFECYCLE_RUN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a run that reuses durable task identity")
val feature = Feature(feature_id: "FEAT-1", title: "Unified lifecycle", state: "implementing", owner: "dev-infra", goal: "typed lifecycle", acceptance_ids: ["AC-1"], document_paths: ["doc"], task_ids: ["TASK-1"])
val task = Task(task_id: "TASK-1", feature_id: feature.feature_id, title: "Implement", state: "active", owner: "agent", change_ids: [])
val run = LifecycleRun(run_id: "TASK-1", feature_id: feature.feature_id, task_id: task.task_id, change_id: "", base_revision_id: "", state: "running")
expect(lifecycle_run_validate(run, task).code).to_equal("LIFECYCLE_RUN")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-007`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `468149b670cd70e1f86f19681098f376537a6d433adef1479ea79a2cba48d507`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `468149b670cd70e1f86f19681098f376537a6d433adef1479ea79a2cba48d507`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `468149b670cd70e1f86f19681098f376537a6d433adef1479ea79a2cba48d507`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/scv/lifecycle_work_spec.spl
mirror: doc/06_spec/01_unit/lib/scv/lifecycle_work_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/lib/scv/lifecycle_work_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/scv/lifecycle_work_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/scv/lifecycle_work_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/scv/lifecycle_work_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links durable work without promoting run state into feature truth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/scv/lifecycle_work_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a run that reuses durable task identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
