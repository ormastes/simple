# Nvim Plugin Live Specification

> <details>

<!-- sdn-diagram:id=nvim_plugin_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvim_plugin_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvim_plugin_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvim_plugin_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvim Plugin Live Specification

## Scenarios

### Neovim plugin live smoke

#### runs isolated headless plugin checks from the worktree

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("bin/simple", ["run", "scripts/smoke/nvim_plugin_smoke.spl"])
expect(result.2).to_equal(0)
if result.0.contains("SKIP: nvim not found"):
    expect(result.0).to_contain("SKIP: nvim not found")
else:
    expect(result.0).to_contain("STATUS: PASS nvim_plugin_smoke")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/nvim_plugin_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Neovim plugin live smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
