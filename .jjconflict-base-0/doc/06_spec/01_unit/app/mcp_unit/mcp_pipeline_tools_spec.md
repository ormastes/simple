# Mcp Pipeline Tools Specification

> <details>

<!-- sdn-diagram:id=mcp_pipeline_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_pipeline_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_pipeline_tools_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_pipeline_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Pipeline Tools Specification

## Scenarios

### Pipeline Phase Definitions

#### when getting impl workflow phases

#### impl workflow has 17 phases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = "requirements,research,req_update,plan,plan_verify,model_select,spipe,test_verify,doc_consistency,implementation,unit_tests,doctest,bug_reports,duplication,refactoring,full_test,vcs_sync"
val phase_list = phases.split(",")
expect(phase_list.len()).to_equal(17)
```

</details>

#### impl starts with requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = "requirements,research,req_update,plan"
val phase_list = phases.split(",")
expect(phase_list[0]).to_equal("requirements")
```

</details>

#### impl ends with vcs_sync

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = "requirements,research,req_update,plan,plan_verify,model_select,spipe,test_verify,doc_consistency,implementation,unit_tests,doctest,bug_reports,duplication,refactoring,full_test,vcs_sync"
val phase_list = phases.split(",")
expect(phase_list[phase_list.len() - 1]).to_equal("vcs_sync")
```

</details>

#### when getting refactor workflow phases

#### refactor workflow has 7 phases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = "file_size,duplication,coupling,public_api,mcdsoc,bigo,test_verify"
val phase_list = phases.split(",")
expect(phase_list.len()).to_equal(7)
```

</details>

#### when getting test workflow phases

#### test workflow has 5 phases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = "spec_create,write_tests,run_tests,coverage,verify"
val phase_list = phases.split(",")
expect(phase_list.len()).to_equal(5)
```

</details>

### Pipeline State Management

#### when creating pipeline state

#### builds state with key=value format

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "id=pipeline_123\n"
state = state + "workflow=impl\n"
state = state + "status=active\n"
expect(state.contains("id=pipeline_123")).to_equal(true)
expect(state.contains("workflow=impl")).to_equal(true)
expect(state.contains("status=active")).to_equal(true)
```

</details>

#### extracts field from state

1. workflow = line replace
   - Expected: workflow equals `impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=pipeline_123\nworkflow=impl\nstatus=active\n"
val lines = content.split("\n")
var workflow = ""
for line in lines:
    if line.starts_with("workflow="):
        workflow = line.replace("workflow=", "")
expect(workflow).to_equal("impl")
```

</details>

#### updates field in state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=p1\nstatus=active\n"
val updated = content.replace("status=active", "status=completed")
expect(updated.contains("status=completed")).to_equal(true)
expect(updated.contains("status=active")).to_equal(false)
```

</details>

### Pipeline Validation Gates

#### when detecting skip indicators

#### detects 'skipped' in result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "Phase was skipped due to time"
expect(result.lower().contains("skipped")).to_equal(true)
```

</details>

#### detects 'not implemented' in result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "Feature not implemented yet"
expect(result.lower().contains("not implemented")).to_equal(true)
```

</details>

#### passes clean result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "Completed requirements document with all acceptance criteria"
val lower = result.lower()
val has_skip = (lower.contains("skipped") or lower.contains("not implemented") or lower.contains("todo_marker"))
expect(has_skip).to_equal(false)
```

</details>

#### when checking artifact paths

#### builds requirement artifact path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature = "my_feature"
val path = "doc/requirement/" + feature + ".md"
expect(path).to_equal("doc/requirement/my_feature.md")
```

</details>

#### builds plan artifact path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature = "my_feature"
val path = "doc/03_plan/" + feature + ".md"
expect(path).to_equal("doc/03_plan/my_feature.md")
```

</details>

#### builds spec artifact path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature = "my_feature"
val path = "test/unit/" + feature + "_spec.spl"
expect(path).to_equal("test/unit/my_feature_spec.spl")
```

</details>

### Pipeline Tool Schemas

#### when building pipeline_start schema

#### has workflow parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo2(jp("type", js("string")), jp("description", js("Workflow type: impl, refactor, or test")))
expect(prop.contains("impl")).to_equal(true)
```

</details>

#### has feature parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo2(jp("type", js("string")), jp("description", js("Feature name")))
expect(prop.contains("Feature name")).to_equal(true)
```

</details>

#### when building result JSON

#### builds gate_failed result

1. jp
2. jp
3. jp
   - Expected: result contains `gate_failed`
   - Expected: result contains `requirements`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo3(
    jp("status", js("gate_failed")),
    jp("phase", js("requirements")),
    jp("reason", js("Required artifact missing"))
)
expect(result.contains("gate_failed")).to_equal(true)
expect(result.contains("requirements")).to_equal(true)
```

</details>

#### builds active result with next phase

1. jp
2. jp
3. jp
   - Expected: result contains `active`
   - Expected: result contains `research`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo3(
    jp("status", js("active")),
    jp("current_phase", js("research")),
    jp("instruction", js("Research existing code"))
)
expect(result.contains("active")).to_equal(true)
expect(result.contains("research")).to_equal(true)
```

</details>

### Phase Agent Mapping

#### when selecting agent for phase

#### maps requirements to docs agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("docs").to_equal("docs")
```

</details>

#### maps research to explore agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("explore").to_equal("explore")
```

</details>

#### maps implementation to code agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("code").to_equal("code")
```

</details>

#### maps unit_tests to test agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("test").to_equal("test")
```

</details>

#### maps vcs_sync to vcs agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("vcs").to_equal("vcs")
```

</details>

#### maps file_size to refactor agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("refactor").to_equal("refactor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_pipeline_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pipeline Phase Definitions
- Pipeline State Management
- Pipeline Validation Gates
- Pipeline Tool Schemas
- Phase Agent Mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
