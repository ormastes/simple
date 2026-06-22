# sandbox_lowering_install_spec

> SimpleOS sandbox lowering installation tests.

<!-- sdn-diagram:id=sandbox_lowering_install_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sandbox_lowering_install_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sandbox_lowering_install_spec -> std
sandbox_lowering_install_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sandbox_lowering_install_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sandbox_lowering_install_spec

SimpleOS sandbox lowering installation tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/sandbox_lowering_install_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SimpleOS sandbox lowering installation tests.

Validates that generated sandbox_lowering capability handles become pledged
kernel CapabilitySet records instead of observational metadata.

## Scenarios

### CapabilityManager sandbox lowering installer

#### maps lowered capability handles into a pledged kernel capability set

1. var mgr = CapabilityManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 123)
val lowering = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
