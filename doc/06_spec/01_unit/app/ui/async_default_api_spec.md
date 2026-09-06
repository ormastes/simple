# Async Default Api Specification

> 1. Ok

<!-- sdn-diagram:id=async_default_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_default_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_default_api_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_default_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Default Api Specification

## Scenarios

### common.ui async-default API

#### create_backend returns an async-default backend

1. Ok
   - Expected: backend.backend_name() equals `none`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("none", 3000)
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("none")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### exports async-first app config aliases at the root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_config = AppConfig.headless()
expect(async_config.event_timeout_ms).to_equal(0)
expect(async_config.hot_reload).to_equal(false)
```

</details>

#### exports App as the async-first app alias

1. Ok
   - Expected: app.is_running() is true
   - Expected: app.current_state().tree.root.kind.name() equals `Text`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend_result = create_backend("none", 3000)
match backend_result:
    Ok(backend) =>
        val state = init_state(build_tree(label("hello")))
        val app = App.from_state(state, backend)
        expect(app.is_running()).to_equal(true)
        expect(app.current_state().tree.root.kind.name()).to_equal("Text")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### keeps sync factory available for legacy callers

1. Ok
   - Expected: backend.backend_name() equals `none`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_sync_backend("none", 3000)
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("none")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/async_default_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- common.ui async-default API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
