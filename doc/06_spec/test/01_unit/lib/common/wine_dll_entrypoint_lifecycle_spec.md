# Wine Dll Entrypoint Lifecycle Specification

> <details>

<!-- sdn-diagram:id=wine_dll_entrypoint_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_entrypoint_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_entrypoint_lifecycle_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_entrypoint_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll Entrypoint Lifecycle Specification

## Scenarios

### wine dll entrypoint lifecycle

#### models TLS-before-DllMain ordering without executing DLL code

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x76000000)
val loaded = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x6000)
val result = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1100, 2, false)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.entrypoint_rva).to_equal(0x1100)
expect(result.tls_callback_count).to_equal(2)
expect(result.status).to_equal("dll-entrypoint-lifecycle-modeled")
expect(result.evidence).to_contain("loader-lock-acquired")
expect(result.evidence).to_contain("tls-callbacks-planned")
expect(result.evidence).to_contain("DllMain-process-attach-planned")
expect(result.evidence).to_contain("dll-entrypoint-execution-blocked")
expect(result.evidence).to_contain("tls-callback-execution-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### blocks requests to actually execute DllMain or TLS callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = wine_dll_load_session_new(0x77000000)
val loaded = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x6000)
val result = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1100, 1, true)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-entrypoint-exec-dispatched")
expect(result.evidence).to_contain("dll-entrypoint-execution-requested")
expect(result.evidence).to_contain("dll-entrypoint-exec-dispatched")
```

</details>

#### requires a modeled load session and valid lifecycle inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_load = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "rolled-back", "dll-load-session-created", 0x1100, 0, false)
expect(missing_load.ok).to_equal(false)
expect(missing_load.error).to_equal("dll-load-session-required:rolled-back")
val missing_evidence = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "dll-load-session-created", 0x1100, 0, false)
expect(missing_evidence.error).to_equal("missing-modeled-loaded-image-evidence")
val invalid_entry = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "modeled-loaded-image", 0, 0, false)
expect(invalid_entry.error).to_equal("invalid-dll-entrypoint-rva")
val invalid_tls = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "modeled-loaded-image", 0x1100, -1, false)
expect(invalid_tls.error).to_equal("invalid-tls-callback-count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll entrypoint lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
