# Bare-Metal Boot Code Integration

> Tests the integration of bare-metal boot code with the Simple runtime including BSS zeroing, data section initialization, and runtime startup. Verifies that the full boot-to-main path works across supported architectures.

<!-- sdn-diagram:id=boot_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Boot Code Integration

Tests the integration of bare-metal boot code with the Simple runtime including BSS zeroing, data section initialization, and runtime startup. Verifies that the full boot-to-main path works across supported architectures.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/boot_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the integration of bare-metal boot code with the Simple runtime including
BSS zeroing, data section initialization, and runtime startup. Verifies that
the full boot-to-main path works across supported architectures.

## Scenarios

### Bare-Metal Boot Code

#### x86 Multiboot

#### ARM Cortex-M Startup

#### RISC-V Machine Mode

#### Cross-Architecture


</details>
