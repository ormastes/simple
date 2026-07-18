# Llm Dashboard Tui Specification

> <details>

<!-- sdn-diagram:id=llm_dashboard_tui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_dashboard_tui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_dashboard_tui_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_dashboard_tui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Dashboard Tui Specification

## Scenarios

### LLM Dashboard TUI

#### renders, handles rapid keys, and exits cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, _, code) = rt_process_run("/bin/bash", ["-c",
    "printf '123456jjkkrq' | bin/simple run src/app/llm_dashboard/main.spl 2>/dev/null"])
expect(code).to_equal(0)
expect(out.contains("Research")).to_equal(true)
expect(out.contains("Code")).to_equal(true)
expect(out.contains("q:quit")).to_equal(true)
expect(out.contains("Claude")).to_equal(true)
expect(out.contains("Codex")).to_equal(true)
expect(out.contains("Gemini")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm_dashboard_tui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Dashboard TUI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
