# Wine Vm Gate Specification

> <details>

<!-- sdn-diagram:id=wine_vm_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_vm_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_vm_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_vm_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Vm Gate Specification

## Scenarios

### Wine VM readiness gate

### feature coverage

#### lists Wine-level VM and namespace requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_vm_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("reserve")
```

</details>

#### reports the first missing VM primitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_vm_gate("reserve commit unmap fixed-map")
expect(state).to_equal("missing-mprotect")
```

</details>

#### returns ready when VM and namespace requirements are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_vm_gate("reserve commit unmap fixed-map mprotect exec-perm guard-page page-fault stack-growth user-pointer pid-namespace fs-namespace ipc-namespace net-namespace cap-namespace")
expect(state).to_equal("ready")
```

</details>

### fault evidence

#### requires process, thread, address, access, and policy fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_vm_fault_gate("process thread address access")
expect(state).to_equal("missing-policy")
```

</details>

### container evidence

#### requires pid, filesystem, IPC, network, and capability namespaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_container_gate("pid fs ipc net")
expect(state).to_equal("missing-capability")
```

</details>

#### does not accept namespace substrings as container evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_container_gate("stupid fs ipc net capability")).to_equal("missing-pid")
expect(wine_container_gate("pid xfs ipc net capability")).to_equal("missing-fs")
expect(wine_container_gate("pid fs epic net capability")).to_equal("missing-ipc")
expect(wine_container_gate("pid fs ipc ethernet capability")).to_equal("missing-net")
expect(wine_container_gate("pid fs ipc net incapability")).to_equal("missing-capability")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_vm_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine VM readiness gate
- feature coverage
- fault evidence
- container evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
