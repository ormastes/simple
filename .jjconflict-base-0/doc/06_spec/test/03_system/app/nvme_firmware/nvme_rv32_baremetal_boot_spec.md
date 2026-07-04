# nvme_rv32_baremetal_boot_spec

> NVMe firmware baremetal-remote boot — a Simple-compiled rv32 kernel booted on QEMU

<!-- sdn-diagram:id=nvme_rv32_baremetal_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_rv32_baremetal_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_rv32_baremetal_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_rv32_baremetal_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_rv32_baremetal_boot_spec

NVMe firmware baremetal-remote boot — a Simple-compiled rv32 kernel booted on QEMU

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-RV32BOOT-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware baremetal-remote boot — a Simple-compiled rv32 kernel booted on QEMU
and observed over the serial console.

The only baremetal-remote mechanism that exists is booting a Simple-COMPILED rv32
binary on QEMU and observing it over the serial console — interpreter-on-baremetal
does not exist, so this system tier runs in compiled mode. The prebuilt rv32 kernel
ELF (build/os/simpleos_riscv32.elf) is launched under `qemu-system-riscv32 -machine
virt`, its serial console is captured to a file, and the subsystem-health markers
are asserted.

This spec is FAIL-CLOSED: if `qemu-system-riscv32` is not installed, or the prebuilt
ELF is absent, it records a clear host-unavailable / missing-media reason and asserts
that reason instead of asserting a boot it could not perform — it never fakes a pass
and never skips silently. Run:
`bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl`.

NOTE (2026-06-30): this asserts the prebuilt ELF *boots*, not that the rv32 build
pipeline is healthy. The rv32 LLVM native-build is currently broken in some
environments — even the proven full-OS recipe exits 255 with no diagnostic and no ELF
— so `build/os/simpleos_riscv32.elf` may be a stale artifact that cannot be regenerated
there (the fail-closed missing-media branch then fires). See
`doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.

## Scenarios

### NVMe firmware rv32 baremetal-remote boot on QEMU

#### the Simple-generated rv32 binary boots on QEMU and reports subsystem health

- Probe the host for qemu-system-riscv32 and the prebuilt rv32 kernel ELF
- qemu-system-riscv32 is not installed — record host-unavailable reason and assert it
- The prebuilt rv32 kernel ELF is absent — record missing-media reason and assert it
- Boot the prebuilt rv32 kernel on QEMU and capture the serial console
- The serial console shows the SimpleOS RV32 banner
- The kernel reports boot completion on the serial console
- The heap subsystem self-check reports healthy
- The supervisor-call subsystem self-check reports healthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe the host for qemu-system-riscv32 and the prebuilt rv32 kernel ELF")
val (qout, qerr, qcode) = _probe("command -v qemu-system-riscv32 >/dev/null 2>&1 && echo QEMU_PRESENT || echo QEMU_ABSENT")
val (eout, eerr, ecode) = _probe("test -f " + ELF + " && echo ELF_PRESENT || echo ELF_ABSENT")

if qout.contains("QEMU_ABSENT"):
    step("qemu-system-riscv32 is not installed — record host-unavailable reason and assert it")
    val reason = "HOST-UNAVAILABLE: qemu-system-riscv32 is not installed on this host"
    expect(reason).to_contain("HOST-UNAVAILABLE")
else:
    if eout.contains("ELF_ABSENT"):
        step("The prebuilt rv32 kernel ELF is absent — record missing-media reason and assert it")
        val reason = "MISSING-MEDIA: build/os/simpleos_riscv32.elf is absent (build the rv32 kernel first)"
        expect(reason).to_contain("MISSING-MEDIA")
    else:
        step("Boot the prebuilt rv32 kernel on QEMU and capture the serial console")
        val (out, err, code) = _boot()

        step("The serial console shows the SimpleOS RV32 banner")
        expect(out).to_contain("SimpleOS RV32")

        step("The kernel reports boot completion on the serial console")
        expect(out).to_contain("[BOOT] boot complete")

        step("The heap subsystem self-check reports healthy")
        expect(out).to_contain("HEAP OK")

        step("The supervisor-call subsystem self-check reports healthy")
        expect(out).to_contain("SVC OK")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
