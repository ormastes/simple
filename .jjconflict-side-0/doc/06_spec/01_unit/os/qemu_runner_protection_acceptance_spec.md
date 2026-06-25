# Qemu Runner Protection Acceptance Specification

> <details>

<!-- sdn-diagram:id=qemu_runner_protection_acceptance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_protection_acceptance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_protection_acceptance_spec -> std
qemu_runner_protection_acceptance_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_protection_acceptance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Protection Acceptance Specification

## Scenarios

### QEMU runner captured serial protection acceptance

#### keeps catalog marker acceptance unchanged when protection mode is off

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = scenario_x64_net_user()
val serial = "[BOOT64] call _start\nTEST PASSED"
expect(qemu_scenario_serial_accepts_completion(x64, "", serial)).to_equal(true)
expect(qemu_scenario_serial_acceptance_reason(x64, "off", serial)).to_equal("ready")
```

</details>

#### requires protection evidence when protection mode is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = scenario_x64_net_user()
val ready = "[BOOT64] call _start\n[harden] text_write_trap=pass\nTEST PASSED"
val missing = "[BOOT64] call _start\nTEST PASSED"
expect(qemu_scenario_serial_accepts_completion(x64, "enforce", ready)).to_equal(true)
expect(qemu_scenario_serial_acceptance_reason(x64, "enforce", missing)).to_equal("missing-protection-probe")
```

</details>

#### checks required lane markers before protection evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = scenario_riscv64_hosted()
val serial = "[PAGING] MMU enabled (SCTLR_EL1.M=1, C=1, I=1)\npage_contract=pass\n"
expect(qemu_scenario_serial_acceptance_reason(rv64, "enforce", serial)).to_contain("missing-marker:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_protection_acceptance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QEMU runner captured serial protection acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
