# System Test - SvLLM Status Readiness Surface

> End-to-end system test for the svllm readiness surface primitives. Verifies that svllm status snapshots correctly reflect engine readiness and provide the cross-reference contract consumed by the IDE agent dashboard.

<!-- sdn-diagram:id=svllm_status_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_status_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_status_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_status_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - SvLLM Status Readiness Surface

End-to-end system test for the svllm readiness surface primitives. Verifies that svllm status snapshots correctly reflect engine readiness and provide the cross-reference contract consumed by the IDE agent dashboard.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SVLLM-STATUS |
| Category | ML / Observability |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/tools/svllm_status_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system test for the svllm readiness surface primitives.
Verifies that svllm status snapshots correctly reflect engine readiness
and provide the cross-reference contract consumed by the IDE agent dashboard.

## Scenarios

### SvLLM Status Readiness Surface

#### default status is offline

- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = svllm_status_default()
verify(status.readiness == "offline")
verify(status.engine_id == "svllm")
verify(status.phase == "A1")
verify(status.served_model == "")
verify(status.pack_available == false)
verify(status.loader_ready == false)
verify(status.nvfs_ready == false)
verify(status.kv_cache_ready == false)
verify(status.model_loaded == false)
```

</details>

#### full-load status is ready

- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = svllm_status_from(true, true, true, true, true, "demo-model")
verify(status.readiness == "ready")
verify(status.served_model == "demo-model")
verify(status.pack_available == true)
verify(status.loader_ready == true)
verify(status.nvfs_ready == true)
verify(status.kv_cache_ready == true)
verify(status.model_loaded == true)
verify(status.reasons.len() == 0)
```

</details>

#### partial component status is degraded

- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pack available, but loader/nvfs/cache/model missing
val status_pack_only = svllm_status_from(true, false, false, false, false, "")
verify(status_pack_only.readiness == "degraded")
verify(status_pack_only.pack_available == true)
verify(status_pack_only.loader_ready == false)

# Loader ready, but pack/nvfs/cache/model missing
val status_loader_only = svllm_status_from(false, true, false, false, false, "")
verify(status_loader_only.readiness == "degraded")
verify(status_loader_only.loader_ready == true)
verify(status_loader_only.pack_available == false)

# Model loaded but pack missing (incomplete)
val status_model_no_pack = svllm_status_from(false, true, true, true, true, "partial-model")
verify(status_model_no_pack.readiness == "degraded")
```

</details>

#### readiness function discriminates ready vs degraded vs offline

- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = svllm_status_readiness(true, true, true, true, true)
verify(ready == "ready")

val degraded = svllm_status_readiness(true, false, false, false, false)
verify(degraded == "degraded")

val offline = svllm_status_readiness(false, false, false, false, false)
verify(offline == "offline")
```

</details>

#### summary string contains expected tokens

- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = svllm_status_from(true, true, true, true, true, "test-model")
val summary = svllm_status_summary(status)
verify(summary.contains("svllm:"))
verify(summary.contains("readiness=ready"))
verify(summary.contains("model=test-model"))
verify(summary.contains("pack=true"))
verify(summary.contains("loader=true"))
verify(summary.contains("phase=A1"))
```

</details>

#### summary for offline status contains expected tokens

- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = svllm_status_default()
val summary = svllm_status_summary(status)
verify(summary.contains("svllm:"))
verify(summary.contains("readiness=offline"))
verify(summary.contains("pack=false"))
verify(summary.contains("loader=false"))
```

</details>

#### consumer module names the IDE dashboard

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val consumer = svllm_status_consumer_module()
verify(consumer == "app.ide.agent_dashboard")
```

</details>

#### status struct carries consumer module reference

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = svllm_status_default()
verify(status.consumer_module == "app.ide.agent_dashboard")
verify(status.consumer_module == svllm_status_consumer_module())
```

</details>

#### reasons array includes all degradation flags

- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All missing
val status_offline = svllm_status_from(false, false, false, false, false, "")
verify(status_offline.reasons.len() == 5)
verify(status_offline.reasons.contains("tensor-pack-unavailable"))
verify(status_offline.reasons.contains("model-loader-not-ready"))
verify(status_offline.reasons.contains("nvfs-client-not-wired"))
verify(status_offline.reasons.contains("kv-cache-not-allocated"))
verify(status_offline.reasons.contains("model-not-loaded"))

# Only model loaded
val status_partial = svllm_status_from(false, false, false, false, true, "")
verify(status_partial.reasons.len() == 4)
verify(status_partial.reasons.contains("tensor-pack-unavailable"))
verify(status_partial.reasons.contains("model-loader-not-ready"))
verify(not status_partial.reasons.contains("model-not-loaded"))
```

</details>

#### engine_id and phase stable across statuses

- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_status = svllm_status_default()
val ready_status = svllm_status_from(true, true, true, true, true, "ready-model")
verify(default_status.engine_id == "svllm")
verify(ready_status.engine_id == "svllm")
verify(default_status.phase == "A1")
verify(ready_status.phase == "A1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
