# Pure-Simple Bootstrap Stage Sanity

> Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported `run` dispatch, compiles the canonical tiny redeploy fixture with stub fallback disabled, and runs it.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple Bootstrap Stage Sanity

Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported `run` dispatch, compiles the canonical tiny redeploy fixture with stub fallback disabled, and runs it.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/02_requirements/app/build/bootstrap.md |
| Plan | doc/03_plan/sys_test/pure_simple_stage_sanity.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/compiler/pure_simple_stage_sanity_spec.spl` |
| Updated | 2026-07-15 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Prove that each retained pure-Simple bootstrap stage starts, rejects unsupported
`run` dispatch, compiles the canonical tiny redeploy fixture with stub
fallback disabled, and runs it.

## Examples

Stage 2 and Stage 3 each compile `p2_add.spl`; the produced native program
must exit successfully and print exactly `5`.

## Scenarios

### Pure-Simple Bootstrap Stage Sanity

### REQ-BOOT-STAGE-001: every retained pure-Simple stage is executable

#### should prove Stage 2 can compile and run a native fixture

- Start Stage 2 and require its bootstrap version
- Reject unsupported run without native-build misrouting
- Strictly compile the canonical tiny fixture
- Run the Stage 2-produced fixture and require output 5
- expect stage sane


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start Stage 2 and require its bootstrap version")
step("Reject unsupported run without native-build misrouting")
step("Strictly compile the canonical tiny fixture")
step("Run the Stage 2-produced fixture and require output 5")
expect_stage_sane("stage2")
```

</details>

#### should prove Stage 3 can compile and run a native fixture

- Start Stage 3 and require its bootstrap version
- Reject unsupported run without native-build misrouting
- Strictly compile the canonical tiny fixture
- Run the Stage 3-produced fixture and require output 5
- expect stage sane


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start Stage 3 and require its bootstrap version")
step("Reject unsupported run without native-build misrouting")
step("Strictly compile the canonical tiny fixture")
step("Run the Stage 3-produced fixture and require output 5")
expect_stage_sane("stage3")
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


## Related Documentation

- **Requirements:** `doc/02_requirements/app/build/bootstrap.md`
- **Plan:** `doc/03_plan/sys_test/pure_simple_stage_sanity.md`


</details>
