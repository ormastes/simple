# Baremetal Test Runner Specification

> <details>

<!-- sdn-diagram:id=baremetal_test_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_test_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_test_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_test_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Test Runner Specification

## Scenarios

### baremetal test runner

### find_baremetal_elf

#### returns a text path for riscv32 lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elf_path = find_baremetal_elf(
    "test/fixtures/baremetal/trivial_baremetal_spec.spl", "riscv32"
)
if elf_path.len() > 0:
    expect(file_exists(elf_path)).to_equal(true)
else:
    expect(elf_path).to_equal("")
```

</details>

### QEMU helpers

#### returns correct binary for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
```

</details>

#### returns correct binary for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("riscv64")).to_equal("qemu-system-riscv64")
```

</details>

#### returns correct machine for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_machine_for_arch("riscv32")).to_equal("virt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/baremetal_test_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal test runner
- find_baremetal_elf
- QEMU helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
