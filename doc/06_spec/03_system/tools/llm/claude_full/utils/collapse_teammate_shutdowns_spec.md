# Claude Full collapse teammate shutdowns

> Pure Simple coverage for consecutive in-process teammate shutdown batching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full collapse teammate shutdowns

Pure Simple coverage for consecutive in-process teammate shutdown batching.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for consecutive in-process teammate shutdown batching.

## Scenarios

### Claude full collapse teammate shutdowns

#### collapses consecutive completed in-process teammate shutdowns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collapses consecutive completed in-process teammate shutdowns
- Check batch attachment
   - Expected: out.len() equals `1`
   - Expected: out[0].typeName equals `attachment`
   - Expected: out[0].uuid equals `a`
   - Expected: out[0].timestamp equals `t1`
   - Expected: out[0].attachmentType equals `teammate_shutdown_batch`
   - Expected: out[0].count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses consecutive completed in-process teammate shutdowns")
step("Check batch attachment")
val messages = [
    TeammateShutdownMessage.taskStatus("a", "t1", "in_process_teammate", "completed"),
    TeammateShutdownMessage.taskStatus("b", "t2", "in_process_teammate", "completed"),
    TeammateShutdownMessage.taskStatus("c", "t3", "in_process_teammate", "completed"),
]

val out = collapseTeammateShutdowns(messages)
expect(out.len()).to_equal(1)
expect(out[0].typeName).to_equal("attachment")
expect(out[0].uuid).to_equal("a")
expect(out[0].timestamp).to_equal("t1")
expect(out[0].attachmentType).to_equal("teammate_shutdown_batch")
expect(out[0].count).to_equal(3)
```

</details>

#### keeps a single shutdown attachment unchanged

- keeps a single shutdown attachment unchanged
- Check single item path
   - Expected: out.len() equals `1`
   - Expected: out[0].attachmentType equals `task_status`
   - Expected: out[0].taskType equals `in_process_teammate`
   - Expected: out[0].count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a single shutdown attachment unchanged")
step("Check single item path")
val msg = TeammateShutdownMessage.taskStatus("one", "time", "in_process_teammate", "completed")
val out = collapseTeammateShutdowns([msg])
expect(out.len()).to_equal(1)
expect(out[0].attachmentType).to_equal("task_status")
expect(out[0].taskType).to_equal("in_process_teammate")
expect(out[0].count).to_equal(0)
```

</details>

#### only collapses consecutive matching completed teammate statuses

- only collapses consecutive matching completed teammate statuses
- Check boundaries
   - Expected: out.len() equals `5`
   - Expected: out[0].attachmentType equals `task_status`
   - Expected: out[1].typeName equals `user`
   - Expected: out[2].attachmentType equals `task_status`
   - Expected: out[3].taskType equals `other_task`
   - Expected: out[4].status equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("only collapses consecutive matching completed teammate statuses")
step("Check boundaries")
val out = collapseTeammateShutdowns([
    TeammateShutdownMessage.taskStatus("a", "t1", "in_process_teammate", "completed"),
    TeammateShutdownMessage.user("user", "t2"),
    TeammateShutdownMessage.taskStatus("b", "t3", "in_process_teammate", "completed"),
    TeammateShutdownMessage.taskStatus("c", "t4", "other_task", "completed"),
    TeammateShutdownMessage.taskStatus("d", "t5", "in_process_teammate", "failed"),
])
expect(out.len()).to_equal(5)
expect(out[0].attachmentType).to_equal("task_status")
expect(out[1].typeName).to_equal("user")
expect(out[2].attachmentType).to_equal("task_status")
expect(out[3].taskType).to_equal("other_task")
expect(out[4].status).to_equal("failed")
```

</details>

#### collapses each matching run independently

- collapses each matching run independently
- Check multiple runs
   - Expected: out.len() equals `3`
   - Expected: out[0].attachmentType equals `teammate_shutdown_batch`
   - Expected: out[0].count equals `2`
   - Expected: out[1].typeName equals `user`
   - Expected: out[2].attachmentType equals `teammate_shutdown_batch`
   - Expected: out[2].count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses each matching run independently")
step("Check multiple runs")
val out = collapseTeammateShutdowns([
    TeammateShutdownMessage.taskStatus("a", "t1", "in_process_teammate", "completed"),
    TeammateShutdownMessage.taskStatus("b", "t2", "in_process_teammate", "completed"),
    TeammateShutdownMessage.user("user", "t3"),
    TeammateShutdownMessage.taskStatus("c", "t4", "in_process_teammate", "completed"),
    TeammateShutdownMessage.taskStatus("d", "t5", "in_process_teammate", "completed"),
])
expect(out.len()).to_equal(3)
expect(out[0].attachmentType).to_equal("teammate_shutdown_batch")
expect(out[0].count).to_equal(2)
expect(out[1].typeName).to_equal("user")
expect(out[2].attachmentType).to_equal("teammate_shutdown_batch")
expect(out[2].count).to_equal(2)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ba00c64b3f6cc69dc4da7b63c1bdfa7f1ded38f1fa213a9e561efc2676d690d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ba00c64b3f6cc69dc4da7b63c1bdfa7f1ded38f1fa213a9e561efc2676d690d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ba00c64b3f6cc69dc4da7b63c1bdfa7f1ded38f1fa213a9e561efc2676d690d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses consecutive completed in-process teammate shutdowns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a single shutdown attachment unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/collapse_teammate_shutdowns_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only collapses consecutive matching completed teammate statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
