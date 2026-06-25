# Llm Agent Dashboard Specification

> <details>

<!-- sdn-diagram:id=llm_agent_dashboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_agent_dashboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_agent_dashboard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_agent_dashboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Agent Dashboard Specification

## Scenarios

### LLM agent dashboard web contracts

#### redirects unauthenticated /agents requests to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path == \"/agents\" or clean_path.starts_with(\"/agents\"):")
expect(source).to_contain("if session == nil:")
expect(source).to_contain("return http_redirect(\"/login\")")
```

</details>

#### includes responsive layout rules for narrow screens

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html_source = _read_source(CSS_SPRITES_PATH)
expect(html_source).to_contain("@media (max-width: 1100px)")
expect(html_source).to_contain("@media (max-width: 720px)")
expect(html_source).to_contain("grid-template-columns: 1fr 1fr 1fr")
expect(html_source).to_contain("grid-template-columns: 1fr 1fr")
expect(html_source).to_contain("grid-template-columns: 1fr;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/llm_agent_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM agent dashboard web contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
