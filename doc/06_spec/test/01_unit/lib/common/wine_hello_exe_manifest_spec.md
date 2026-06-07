# Wine Hello Exe Manifest Specification

> <details>

<!-- sdn-diagram:id=wine_hello_exe_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_hello_exe_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_hello_exe_manifest_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_hello_exe_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Exe Manifest Specification

## Scenarios

### Wine hello.exe manifest and VM probe

#### requires the composed precondition manifest on the manifest probe path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _ready_manifest()
val result = wine_hello_exe_probe_manifest(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())
expect(result.status).to_equal("executed")
expect(wine_hello_exe_manifest_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())).to_equal(true)
```

</details>

#### accepts structured execution evidence on the manifest probe path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _ready_manifest()
val evidence = wine_cpu_execution_evidence_all_ready()
val result = wine_hello_exe_probe_manifest_evidence(wine_known_hello_exe_fixture_bytes(), manifest, evidence)
expect(result.status).to_equal("executed")
expect(wine_hello_exe_manifest_evidence_can_execute(wine_known_hello_exe_fixture_bytes(), manifest, evidence)).to_equal(true)
```

</details>

#### executes only after the PE image is mapped into an OS-backed VM process

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_hello_exe_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### blocks the VM probe when process/container evidence is only modeled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(0, 0, "")
val result = wine_hello_exe_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("missing-os-process")
```

</details>

#### executes the manifest path through OS-backed VM mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _ready_manifest()
val evidence = wine_cpu_execution_evidence_all_ready()
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_hello_exe_probe_manifest_evidence_vm(wine_known_hello_exe_fixture_bytes(), manifest, evidence, space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("executed")
```

</details>

#### blocks the manifest probe before PE parsing when process evidence is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_manifest("[desktop-e2e] process-backed:ok app=browser_demo pid=1", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready", "ready")
val result = wine_hello_exe_probe_manifest(wine_known_hello_exe_fixture_bytes(), manifest, wine_hello_fixture_verified_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("blocked-process:insufficient-evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_hello_exe_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine hello.exe manifest and VM probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
