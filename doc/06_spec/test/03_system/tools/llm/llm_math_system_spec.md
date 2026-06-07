# LLM Math Question System Test

> Live system test that sends a math question to Claude via CLI and verifies the response contains the correct answer. Requires `claude` CLI binary available on PATH.

<!-- sdn-diagram:id=llm_math_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_math_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_math_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_math_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Math Question System Test

Live system test that sends a math question to Claude via CLI and verifies the response contains the correct answer. Requires `claude` CLI binary available on PATH.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/03_system/tools/llm/llm_math_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Live system test that sends a math question to Claude via CLI
and verifies the response contains the correct answer.
Requires `claude` CLI binary available on PATH.

## Requirements
- N/A
- N/A
- N/A
- N/A

## Scenarios

### LLM Claude CLI Math

#### answers a simple addition question

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = claude_ask("What is 2 + 2? Reply with ONLY the number, nothing else.")
print "Response: " + response
# Response should contain "4"
expect(response.contains("4")).to_equal(true)
```

</details>

#### answers a multiplication question

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = claude_ask("What is 7 * 8? Reply with ONLY the number, nothing else.")
print "Response: " + response
expect(response.contains("56")).to_equal(true)
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
