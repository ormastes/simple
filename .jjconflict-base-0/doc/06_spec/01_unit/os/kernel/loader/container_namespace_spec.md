# Container Namespace Specification

> <details>

<!-- sdn-diagram:id=container_namespace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=container_namespace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

container_namespace_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=container_namespace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container Namespace Specification

## Scenarios

### SimpleOS container namespace contract

#### requires pid, filesystem, IPC, network, and capability evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = simpleos_container_namespace_evidence(42, "/containers/wine", true, true, true, false)
expect(evidence).to_contain("pid")
expect(evidence).to_contain("net")
expect(simpleos_container_namespace_gate(evidence)).to_equal("missing-capability")
```

</details>

#### keeps app paths resolved under the container rootfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simpleos_container_rootfs_gate("/containers/wine", "/sys/apps/wine_hello")).to_equal("ready")
expect(simpleos_container_rootfs_gate("/", "/sys/apps/wine_hello")).to_equal("invalid-rootfs")
expect(simpleos_container_rootfs_gate("/containers/wine", "/etc/passwd")).to_equal("invalid-app-path")
```

</details>

#### builds desktop serial markers for a Wine app container

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = simpleos_wine_container_contract(42, "/containers/wine", "/sys/apps/wine_hello", "nvfs")
expect(contract.ok).to_equal(true)
expect(contract.evidence).to_contain("capability")
expect(contract.namespace_marker).to_contain("[desktop-e2e] container-namespace:ok")
expect(contract.namespace_marker).to_contain("pid")
expect(contract.rootfs_marker).to_contain("[desktop-e2e] container-rootfs:ok")
expect(contract.rootfs_marker).to_contain("rootfs_backend=nvfs")
```

</details>

#### does not produce ok markers for invalid rootfs contracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = simpleos_wine_container_contract(42, "/", "/sys/apps/wine_hello", "nvfs")
expect(contract.ok).to_equal(false)
expect(contract.error).to_equal("invalid-rootfs")
expect(contract.namespace_marker).to_equal("")
expect(contract.rootfs_marker).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/container_namespace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS container namespace contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
