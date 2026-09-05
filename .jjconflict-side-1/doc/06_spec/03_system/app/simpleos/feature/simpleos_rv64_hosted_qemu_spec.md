# Simpleos Rv64 Hosted Qemu Specification

> <details>

<!-- sdn-diagram:id=simpleos_rv64_hosted_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_rv64_hosted_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_rv64_hosted_qemu_spec -> std
simpleos_rv64_hosted_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_rv64_hosted_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Rv64 Hosted Qemu Specification

## Scenarios

### SimpleOS RV64 hosted QEMU

### REQ-RV64-HOSTED-001/002: scenario shape

#### registers the hosted RV64 scenario with disk and forwarded network

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv64_hosted()
expect(scenario.name).to_equal("riscv64-hosted")
expect(scenario.arch).to_equal(Architecture.Riscv64)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario.qemu_extra).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")
expect(scenario.qemu_extra).to_contain("virtio-net-pci,netdev=n0,disable-legacy=on")
expect(scenario_test_timeout_ms(scenario)).to_equal(120000)
```

</details>

#### resolves the scenario and target by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if val resolved = get_scenario("riscv64-hosted"):
    expect(resolved.name).to_equal("riscv64-hosted")
else:
    expect("missing").to_equal("riscv64-hosted")
val target = scenario_target(scenario_riscv64_hosted())
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv64_hosted.elf")
```

</details>

#### builds a QEMU command with host-forwarded SSH and HTTP

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_scenario_command(scenario_riscv64_hosted(), "build/os/simpleos_riscv64_hosted.elf")
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")
expect(cmd).to_contain("virtio-net-pci,netdev=n0,disable-legacy=on")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS RV64 hosted QEMU
- REQ-RV64-HOSTED-001/002: scenario shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
