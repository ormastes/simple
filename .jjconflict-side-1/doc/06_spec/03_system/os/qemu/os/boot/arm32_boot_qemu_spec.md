# Arm32 Boot Qemu Specification

> <details>

<!-- sdn-diagram:id=arm32_boot_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm32_boot_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm32_boot_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm32_boot_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm32 Boot Qemu Specification

## Scenarios

### ARM32 Architecture Boot

#### binds the canonical arm32 boot artifact contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(ARCH)
expect(target.arch).to_equal(Architecture.Arm32)
expect(target.entry).to_equal("src/os/kernel/arch/arm32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/arm32/linker.ld")
expect(target.target_triple).to_equal("armv7-unknown-none-eabihf")
expect(target.output).to_equal("build/os/simpleos_arm32.elf")
expect(target.qemu_system).to_equal("qemu-system-arm")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("cortex-a15")
expect(target.qemu_memory).to_equal("128M")
expect(target.qemu_extra.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: prints boot banner on serial</summary>

#### prints boot banner on serial _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("SimpleOS arm32 starting")
```

</details>


</details>

<details>
<summary>Advanced: boot info parsed</summary>

#### boot info parsed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("boot-info:ok")
```

</details>


</details>

<details>
<summary>Advanced: reaches halt loop</summary>

#### reaches halt loop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("[arm32] halt")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/arm32_boot_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM32 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
