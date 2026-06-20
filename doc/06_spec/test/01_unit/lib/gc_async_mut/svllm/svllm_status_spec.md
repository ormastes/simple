# Svllm Status Specification

> <details>

<!-- sdn-diagram:id=svllm_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svllm Status Specification

## Scenarios

### svllm_status_default

#### is offline when nothing is wired

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.readiness).to_equal("offline")
```

</details>

#### has engine_id svllm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.engine_id).to_equal("svllm")
```

</details>

#### has phase A1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.phase).to_equal("A1")
```

</details>

#### has empty served_model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.served_model).to_equal("")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 5 reasons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.reasons.len()).to_equal(5)
```

</details>

#### has all component flags false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
expect(s.pack_available).to_equal(false)
expect(s.loader_ready).to_equal(false)
expect(s.nvfs_ready).to_equal(false)
expect(s.kv_cache_ready).to_equal(false)
expect(s.model_loaded).to_equal(false)
```

</details>

### svllm_status_from all-true

#### is ready when all five flags true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
expect(s.readiness).to_equal("ready")
```

</details>

#### is servable when all five flags true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
expect(svllm_status_is_servable(s)).to_equal(true)
```

</details>

#### has zero reasons when fully ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
expect(s.reasons.len()).to_equal(0)
```

</details>

#### preserves served_model when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
expect(s.served_model).to_equal("llama3")
```

</details>

#### sets consumer_module to dashboard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
expect(s.consumer_module).to_equal("app.ide.agent_dashboard")
```

</details>

### svllm_status_from single-flag-false — pack_available

#### is degraded when only pack_available is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, true, true, true, true, "llama3")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, true, true, true, true, "llama3")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 1 reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, true, true, true, true, "llama3")
expect(s.reasons.len()).to_equal(1)
```

</details>

### svllm_status_from single-flag-false — loader_ready

#### is degraded when only loader_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, false, true, true, true, "llama3")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, false, true, true, true, "llama3")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 1 reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, false, true, true, true, "llama3")
expect(s.reasons.len()).to_equal(1)
```

</details>

### svllm_status_from single-flag-false — nvfs_ready

#### is degraded when only nvfs_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, false, true, true, "llama3")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, false, true, true, "llama3")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 1 reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, false, true, true, "llama3")
expect(s.reasons.len()).to_equal(1)
```

</details>

### svllm_status_from single-flag-false — kv_cache_ready

#### is degraded when only kv_cache_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, false, true, "llama3")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, false, true, "llama3")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 1 reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, false, true, "llama3")
expect(s.reasons.len()).to_equal(1)
```

</details>

### svllm_status_from single-flag-false — model_loaded

#### is degraded when only model_loaded is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, false, "llama3")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, false, "llama3")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has exactly 1 reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, false, "llama3")
expect(s.reasons.len()).to_equal(1)
```

</details>

### svllm_status_from kv_cache_ready-only-true (degraded-OR fix validation)

#### is degraded not offline when only kv_cache_ready is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This case proves the degraded-OR branch includes kv_cache_ready.
# Before the fix: (F,F,F,T,F) fell through to offline because the OR
# omitted kv_cache_ready. After the fix it must be "degraded".
val s = svllm_status_from(false, false, false, true, false, "")
expect(s.readiness).to_equal("degraded")
```

</details>

#### is not servable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, false, false, true, false, "")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

#### has 4 reasons (all flags except kv_cache_ready are false)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, false, false, true, false, "")
expect(s.reasons.len()).to_equal(4)
```

</details>

### svllm_status_reasons content

#### includes tensor-pack-unavailable when pack_available is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(false, true, true, true, true)
expect(r.len()).to_equal(1)
expect(r.get(0)).to_equal("tensor-pack-unavailable")
```

</details>

#### includes model-loader-not-ready when loader_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(true, false, true, true, true)
expect(r.len()).to_equal(1)
expect(r.get(0)).to_equal("model-loader-not-ready")
```

</details>

#### includes nvfs-client-not-wired when nvfs_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(true, true, false, true, true)
expect(r.len()).to_equal(1)
expect(r.get(0)).to_equal("nvfs-client-not-wired")
```

</details>

#### includes kv-cache-not-allocated when kv_cache_ready is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(true, true, true, false, true)
expect(r.len()).to_equal(1)
expect(r.get(0)).to_equal("kv-cache-not-allocated")
```

</details>

#### includes model-not-loaded when model_loaded is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(true, true, true, true, false)
expect(r.len()).to_equal(1)
expect(r.get(0)).to_equal("model-not-loaded")
```

</details>

#### is empty when all flags are true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(true, true, true, true, true)
expect(r.len()).to_equal(0)
```

</details>

#### has 5 entries when all flags are false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = svllm_status_reasons(false, false, false, false, false)
expect(r.len()).to_equal(5)
```

</details>

### svllm_status_summary

#### contains phase=A1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
val sum = svllm_status_summary(s)
expect(sum).contains("phase=A1")
```

</details>

#### contains readiness=offline for default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
val sum = svllm_status_summary(s)
expect(sum).contains("readiness=offline")
```

</details>

#### contains readiness=ready for all-true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
val sum = svllm_status_summary(s)
expect(sum).contains("readiness=ready")
```

</details>

#### contains model name in summary when served_model is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "llama3")
val sum = svllm_status_summary(s)
expect(sum).contains("model=llama3")
```

</details>

#### starts with svllm:

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_default()
val sum = svllm_status_summary(s)
expect(sum).contains("svllm:")
```

</details>

### svllm_status_consumer_module

#### returns the IDE dashboard module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(svllm_status_consumer_module()).to_equal("app.ide.agent_dashboard")
```

</details>

### svllm_status_is_servable

#### returns false for default (offline) status

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(svllm_status_is_servable(svllm_status_default())).to_equal(false)
```

</details>

#### returns true for all-true status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "model")
expect(svllm_status_is_servable(s)).to_equal(true)
```

</details>

#### returns false when readiness is degraded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, false, true, "model")
expect(svllm_status_is_servable(s)).to_equal(false)
```

</details>

### svllm_status_from served_model boundary

#### empty served_model is preserved in status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "")
expect(s.served_model).to_equal("")
```

</details>

#### all-true with empty model is still ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(true, true, true, true, true, "")
expect(s.readiness).to_equal("ready")
```

</details>

#### non-empty served_model is preserved in offline status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = svllm_status_from(false, false, false, false, false, "stale-model")
expect(s.served_model).to_equal("stale-model")
expect(s.readiness).to_equal("offline")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/svllm_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svllm_status_default
- svllm_status_from all-true
- svllm_status_from single-flag-false — pack_available
- svllm_status_from single-flag-false — loader_ready
- svllm_status_from single-flag-false — nvfs_ready
- svllm_status_from single-flag-false — kv_cache_ready
- svllm_status_from single-flag-false — model_loaded
- svllm_status_from kv_cache_ready-only-true (degraded-OR fix validation)
- svllm_status_reasons content
- svllm_status_summary
- svllm_status_consumer_module
- svllm_status_is_servable
- svllm_status_from served_model boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
