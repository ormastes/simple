# Wine Precondition Fixture Builder Specification

> <details>

<!-- sdn-diagram:id=wine_precondition_fixture_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_precondition_fixture_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_precondition_fixture_builder_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_precondition_fixture_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Precondition Fixture Builder Specification

## Scenarios

### Wine precondition fixture builder

#### derives VM and renderer readiness from adapter models

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_precondition_fixture_exec_env_state()).to_equal("ready")
expect(wine_precondition_fixture_vm_state()).to_equal("ready")
expect(wine_precondition_fixture_renderer_state()).to_equal("ready")
```

</details>

#### derives host, POSIX, pthread, dynamic loading, async, and PE readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_precondition_fixture_host_state()).to_equal("ready")
expect(wine_precondition_fixture_posix_state()).to_equal("ready")
expect(wine_precondition_fixture_pthread_state()).to_equal("ready")
expect(wine_precondition_fixture_dynload_state()).to_equal("ready")
expect(wine_precondition_fixture_async_state()).to_equal("ready")
expect(wine_precondition_fixture_pe_loader_state()).to_equal("ready")
expect(wine_precondition_fixture_nt_bridge_state()).to_equal("ready")
```

</details>

#### builds the manifest accepted by the hello fixture path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = wine_precondition_fixture_manifest()
expect(manifest.ready).to_equal(true)
expect(manifest.state).to_equal("ready")
expect(manifest.gates).to_contain("process=verified")
expect(manifest.gates).to_contain("pe_loader=verified")
expect(manifest.gates).to_contain("nt_bridge=verified")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_precondition_fixture_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine precondition fixture builder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
