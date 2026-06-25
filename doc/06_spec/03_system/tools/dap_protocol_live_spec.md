# Dap Protocol Live Specification

> <details>

<!-- sdn-diagram:id=dap_protocol_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_protocol_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_protocol_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_protocol_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Protocol Live Specification

## Scenarios

### DAP live protocol smoke

#### responds to DAP initialize, launch, stack, variables, and evaluate requests

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("bin/simple", ["run", "scripts/smoke/dap_protocol_smoke.spl"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("dap_protocol_smoke")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/dap_protocol_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DAP live protocol smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
