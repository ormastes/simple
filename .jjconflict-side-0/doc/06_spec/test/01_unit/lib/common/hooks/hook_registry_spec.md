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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hook Registry Specification

## Scenarios

### Hook Registry

#### keeps sync facade wired to the async hook module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = hook_registry_facade_source()

expect(source).to_contain("export use std.gc_async_mut.hooks.mod.*")
```

</details>

#### keeps hook result, callback, and registry models available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = hook_registry_source()

expect(source).to_contain("enum HookResult:")
expect(source).to_contain("type HookCallback = fn() -> HookResult")
expect(source).to_contain("struct Hook:")
expect(source).to_contain("class HookRegistry:")
```

</details>

#### keeps registry mutation and query methods available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = hook_registry_source()

expect(source).to_contain("me register(name: text, priority: i64, callback: HookCallback)")
expect(source).to_contain("fn sort_hooks() -> [Hook]")
expect(source).to_contain("fn get_hook(name: text) -> Hook?")
expect(source).to_contain("me remove_hook(name: text) -> bool")
expect(source).to_contain("fn count() -> i64")
```

</details>

#### keeps global hook execution and environment gates available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = hook_registry_source()

expect(source).to_contain("fn create_registry() -> HookRegistry")
expect(source).to_contain("fn register_hook(name: text, priority: i64, callback: HookCallback)")
expect(source).to_contain("fn run_hooks() -> HookResult")
expect(source).to_contain("fn hooks_enabled() -> bool")
expect(source).to_contain("fn interactive_mode() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hooks/hook_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hook Registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
