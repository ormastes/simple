# Simpleos Wine Dll Entrypoint Lifecycle Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_dll_entrypoint_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_dll_entrypoint_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_dll_entrypoint_lifecycle_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_dll_entrypoint_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll Entrypoint Lifecycle Specification

## Scenarios

### REQ-044 SimpleOS Wine DLL entrypoint lifecycle gate

#### requires loaded-image evidence and keeps DllMain/TLS execution blocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x78000000)
val loaded = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x6000)
val result = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1200, 1, false)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-entrypoint-lifecycle-modeled")
expect(result.evidence).to_contain("modeled-loaded-image")
expect(result.evidence).to_contain("loader-lock-acquired")
expect(result.evidence).to_contain("tls-callbacks-planned")
expect(result.evidence).to_contain("DllMain-process-attach-planned")
expect(result.evidence).to_contain("dll-entrypoint-execution-blocked")
expect(result.evidence).to_contain("tls-callback-execution-blocked")

val blocked = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1200, 1, true)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("dll-entrypoint-execution-not-implemented")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_entrypoint_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-044 SimpleOS Wine DLL entrypoint lifecycle gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
