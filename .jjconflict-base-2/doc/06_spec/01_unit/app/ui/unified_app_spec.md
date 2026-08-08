# Unified App Specification

> <details>

<!-- sdn-diagram:id=unified_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_app_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified App Specification

## Scenarios

### AppConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.default_config()
expect(config.poll_timeout_ms).to_equal(100)
expect(config.hot_reload).to_equal(true)
```

</details>

#### creates headless config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.headless()
expect(config.poll_timeout_ms).to_equal(0)
expect(config.hot_reload).to_equal(false)
```

</details>

#### creates web config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.web_config()
expect(config.poll_timeout_ms).to_equal(0)
expect(config.hot_reload).to_equal(true)
```

</details>

### create_backend

#### creates none backend

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

#### creates headless backend

1. Ok
   - Expected: backend.backend_name() equals `none`
2. Err
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("headless", 3000)
match result:
    Ok(backend) =>
        expect(backend.backend_name()).to_equal("none")
    Err(e) =>
        expect(false).to_equal(true)
```

</details>

#### rejects unknown mode

1. Ok
   - Expected: false is true
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_backend("nonexistent", 3000)
match result:
    Ok(_) =>
        expect(false).to_equal(true)
    Err(e) =>
        expect(e).to_contain("Unknown backend mode")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/unified_app_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AppConfig
- create_backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
