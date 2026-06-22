# Hook Registry Specification

> <details>

<!-- sdn-diagram:id=hook_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hook_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hook_registry_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hook_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hook Registry Specification

## Scenarios

### Hook Registry

#### keeps hook registry types and factory available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_hook_source("src/lib/nogc_sync_mut/hooks/mod.spl")

expect(source).to_contain("enum HookResult")
expect(source).to_contain("class HookRegistry")
expect(source).to_contain("fn create_registry() -> HookRegistry")
```

</details>

#### keeps global hook registration and execution entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_hook_source("src/lib/nogc_sync_mut/hooks/mod.spl")

expect(source).to_contain("fn register_hook(name: text, priority: i64, callback: HookCallback)")
expect(source).to_contain("fn run_hooks() -> HookResult")
expect(source).to_contain("fn run_hooks_by_priority(max_priority: i64) -> [HookResult]")
```

</details>

#### keeps hook feature flags available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_hook_source("src/lib/nogc_sync_mut/hooks/mod.spl")

expect(source).to_contain("fn hooks_enabled() -> bool")
expect(source).to_contain("fn interactive_mode() -> bool")
expect(source).to_contain("fn get_max_priority() -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/hooks/hook_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hook Registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
