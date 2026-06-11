# Wine Image Vm Map Specification

> <details>

<!-- sdn-diagram:id=wine_image_vm_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_image_vm_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_image_vm_map_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_image_vm_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Image Vm Map Specification

## Scenarios

### Wine PE image to VM process mapping

#### rejects malformed PE before touching the VM process

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process([], space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("too-small")
expect(result.space.regions.len()).to_equal(0)
```

</details>

#### maps a validated image and stack into an OS-backed VM process

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process(_minimal_image(0x2010, 0x5000), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.ok).to_equal(true)
expect(result.state).to_equal("mapped")
expect(result.entry_address).to_equal(0x402010)
expect(result.space.regions.len()).to_equal(3)
expect(wine_vm_production_gate(result.space, _fault())).to_equal("ready")
```

</details>

#### rejects overlapping image and stack ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(10, 9000, "pid fs ipc net capability")
val result = wine_image_map_into_vm_process(_minimal_image(0x2010, 0x5000), space, 0x400000, 0x401000, 0x2000, 0x1000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("fixed-map-conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_image_vm_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine PE image to VM process mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
