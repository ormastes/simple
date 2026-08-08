# Connection Matrix Qemu Specification

> <details>

<!-- sdn-diagram:id=connection_matrix_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=connection_matrix_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

connection_matrix_qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=connection_matrix_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Connection Matrix Qemu Specification

## Scenarios

### QEMU connection specs

<details>
<summary>Advanced: has 2 QEMU specs</summary>

#### has 2 QEMU specs _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val specs = qemu_specs()
expect(specs.len()).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: QEMU ARM uses port 3335</summary>

#### QEMU ARM uses port 3335 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val specs = qemu_specs()
expect(specs[0].gdb_port).to_equal(3335)
```

</details>


</details>

<details>
<summary>Advanced: QEMU RV32 uses port 1234</summary>

#### QEMU RV32 uses port 1234 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val specs = qemu_specs()
expect(specs[1].gdb_port).to_equal(1234)
```

</details>


</details>

<details>
<summary>Advanced: QEMU specs are not hardware</summary>

#### QEMU specs are not hardware _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val specs = qemu_specs()
expect(specs[0].is_hardware()).to_equal(false)
expect(specs[1].is_hardware()).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/02_integration/baremetal/connection_matrix_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QEMU connection specs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
