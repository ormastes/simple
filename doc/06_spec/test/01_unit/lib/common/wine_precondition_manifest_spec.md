# Wine Precondition Manifest Specification

> <details>

<!-- sdn-diagram:id=wine_precondition_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_precondition_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_precondition_manifest_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_precondition_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Precondition Manifest Specification

## Scenarios

### Wine precondition manifest

#### blocks on incomplete process-backed app evidence before proxy gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial_log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
val manifest = wine_precondition_manifest(partial_log, "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-process:insufficient-evidence")
```

</details>

#### reports the first ordered precondition blocker

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "missing-mprotect", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-vm:missing-mprotect")
expect(manifest.gates).to_equal("process=verified exec_env=verified")
```

</details>

#### requires the SimpleOS VM/container executable environment before VM adapter gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "missing-simpleos-container-namespace", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-exec-env:missing-simpleos-container-namespace")
expect(manifest.gates).to_equal("process=verified")
```

</details>

#### keeps renderer readiness separate from hello.exe substrate gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "missing-clipboard", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-renderer:missing-clipboard")
expect(manifest.gates).to_contain("vm=verified")
```

</details>

#### requires host, POSIX, pthread, dynload, async, and PE gates before hello.exe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "missing-submit-write", "ready", "ready")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-async:missing-submit-write")
expect(manifest.gates).to_contain("dynload=verified")
```

</details>

#### requires the modeled NT bridge before hello.exe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "missing-heap")
expect(manifest.ready).to_equal(false)
expect(manifest.state).to_equal("blocked-nt-bridge:missing-heap")
expect(manifest.gates).to_contain("pe_loader=verified")
```

</details>

#### emits the verified gate string accepted by the hello.exe gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest(wine_precondition_required_process_log(), "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
expect(manifest.ready).to_equal(true)
expect(manifest.state).to_equal("ready")
expect(manifest.gates).to_contain("process=verified")
expect(manifest.gates).to_contain("exec_env=verified")
expect(manifest.gates).to_contain("pe_loader=verified")
expect(manifest.gates).to_contain("nt_bridge=verified")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_precondition_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine precondition manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
