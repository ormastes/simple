# MCP Protocol Compliance Gap Matrix

> Tests MCP protocol compliance by tracking which protocol features are implemented versus missing. Verifies the gap matrix accurately reflects server capabilities and that compliance checks detect unsupported methods and parameters.

<!-- sdn-diagram:id=mcp_protocol_gap_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_protocol_gap_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_protocol_gap_matrix_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_protocol_gap_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Protocol Compliance Gap Matrix

Tests MCP protocol compliance by tracking which protocol features are implemented versus missing. Verifies the gap matrix accurately reflects server capabilities and that compliance checks detect unsupported methods and parameters.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp_protocol_gap_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests MCP protocol compliance by tracking which protocol features are implemented
versus missing. Verifies the gap matrix accurately reflects server capabilities
and that compliance checks detect unsupported methods and parameters.

## Scenarios

### MCP Protocol Compliance Matrix

#### feature inventory lock

#### tracks complete debug tool set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(DEBUG_TOOLS)).to_equal(19)
expect(has_text(DEBUG_TOOLS, "debug_create_session")).to_equal(true)
expect(has_text(DEBUG_TOOLS, "debug_terminate")).to_equal(true)
```

</details>

#### tracks complete debug-log tool set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(DEBUG_LOG_TOOLS)).to_equal(6)
expect(has_text(DEBUG_LOG_TOOLS, "debug_log_enable")).to_equal(true)
expect(has_text(DEBUG_LOG_TOOLS, "debug_log_status")).to_equal(true)
```

</details>

#### tracks complete diagnostic tool set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(DIAG_TOOLS)).to_equal(12)
expect(has_text(DIAG_TOOLS, "simple_read")).to_equal(true)
expect(has_text(DIAG_TOOLS, "simple_api")).to_equal(true)
```

</details>

#### tracks total advertised tool count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = count_texts(DEBUG_TOOLS) + count_texts(DEBUG_LOG_TOOLS) + count_texts(DIAG_TOOLS)
expect(total).to_equal(37)
```

</details>

#### gap inventory lock

#### tracks resolved protocol method gaps

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(RESOLVED_METHOD_GAPS)).to_equal(7)
expect(has_text(RESOLVED_METHOD_GAPS, "resources/read")).to_equal(true)
expect(has_text(RESOLVED_METHOD_GAPS, "prompts/get")).to_equal(true)
expect(has_text(RESOLVED_METHOD_GAPS, "completion/complete")).to_equal(true)
```

</details>

#### tracks resolved response format gaps

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(RESOLVED_RESPONSE_GAPS)).to_equal(5)
expect(has_text(RESOLVED_RESPONSE_GAPS, "jsonrpc-id-type-preservation")).to_equal(true)
expect(has_text(RESOLVED_RESPONSE_GAPS, "tool-schema-properties-required")).to_equal(true)
```

</details>

#### plan coverage lock

#### tracks all implementation phases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(PLAN_PHASES)).to_equal(4)
expect(has_text(PLAN_PHASES, "Phase 1: Protocol Correctness")).to_equal(true)
expect(has_text(PLAN_PHASES, "Phase 4: Error and Payload Semantics")).to_equal(true)
```

</details>

#### documentation linkage lock

#### includes canonical docs and test artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [
    "doc/03_plan/mcp_protocol_gap_closure_plan_2026-02-24.md",
    "doc/01_research/mcp_command_and_response_gap_analysis_2026-02-24.md",
    "doc/05_design/simple_mcp_debug_design.md",
    "doc/02_requirements/feature/app/mcp_protocol_compliance.md",
    "doc/06_spec/app/compiler/feature/app/mcp_protocol_compliance_spec.md"
]
expect(count_texts(docs)).to_equal(5)
expect(has_text(docs, "doc/06_spec/app/compiler/feature/app/mcp_protocol_compliance_spec.md")).to_equal(true)
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
