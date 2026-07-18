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
| 2 | 2 | 0 | 0 |

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
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware baremetal-remote boot — a Simple-compiled rv32 kernel booted on QEMU
and observed over the serial console.

The only baremetal-remote mechanism that exists is booting a Simple-COMPILED rv32
binary on QEMU and observing it over the serial console — interpreter-on-baremetal
does not exist, so this system tier runs in compiled mode. The NVMe firmware rv32
ELF (build/nvme_fw_rv32.elf) is launched under `qemu-system-riscv32 -machine
virt`, its serial console is captured to a file, and the subsystem-health markers
are asserted.

This spec is FAIL-CLOSED: if `qemu-system-riscv32` is not installed, or the prebuilt
ELF is absent, it fails with a clear host-unavailable / missing-media reason instead
of asserting a boot it could not perform — it never fakes a pass and never skips
silently. Run:
`bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl`.

NOTE (2026-07-05): this asserts the prebuilt NVMe firmware rv32 ELF boots and
prints the firmware PASS marker. The P9 wrapper has a separate scenario below
proving the boot hook is wired and the firmware entry owns the strong exported
hook.

## Scenarios

### NVMe firmware rv32 baremetal-remote boot on QEMU

#### the NVMe firmware rv32 ELF boots on QEMU and reports subsystem health

- Probe the host for qemu-system-riscv32 and the NVMe firmware rv32 ELF
- qemu-system-riscv32 is not installed — fail with host-unavailable reason
- fail
- The NVMe firmware rv32 ELF is absent — fail with missing-media reason
- fail
- Boot the NVMe firmware rv32 ELF on QEMU and capture the serial console
- The serial console shows the SimpleOS RV32 banner
- The kernel reports boot completion on the serial console
- The NVMe firmware hook reports its rv32 self-test PASS marker
- The serial console contains no failure markers
- fail
- The heap subsystem self-check reports healthy
- The supervisor-call subsystem self-check reports healthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe the host for qemu-system-riscv32 and the NVMe firmware rv32 ELF")
val (qout, qerr, qcode) = _probe("command -v qemu-system-riscv32 >/dev/null 2>&1 && echo QEMU_PRESENT || echo QEMU_ABSENT")
val (eout, eerr, ecode) = _probe("test -f " + ELF + " && echo ELF_PRESENT || echo ELF_ABSENT")

if qout.contains("QEMU_ABSENT"):
    step("qemu-system-riscv32 is not installed — fail with host-unavailable reason")
    val reason = "HOST-UNAVAILABLE: qemu-system-riscv32 is not installed on this host"
    fail(reason)
else:
    if eout.contains("ELF_ABSENT"):
        step("The NVMe firmware rv32 ELF is absent — fail with missing-media reason")
        val reason = "MISSING-MEDIA: build/nvme_fw_rv32.elf is absent (run examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs first)"
        fail(reason)
    else:
        step("Boot the NVMe firmware rv32 ELF on QEMU and capture the serial console")
        val (out, err, code) = _boot()

        step("The serial console shows the SimpleOS RV32 banner")
        expect(out).to_contain("SimpleOS RV32")

        step("The kernel reports boot completion on the serial console")
        expect(out).to_contain("[BOOT] boot complete")

        step("The NVMe firmware hook reports its rv32 self-test PASS marker")
        expect(out).to_contain("ALL RV32 NVME FW CHECKS PASS")

        step("The serial console contains no failure markers")
        if out.contains("FAIL"):
            fail("SERIAL-FAIL: rv32 boot printed a failure marker")

        step("The heap subsystem self-check reports healthy")
        expect(out).to_contain("HEAP OK")

        step("The supervisor-call subsystem self-check reports healthy")
        expect(out).to_contain("SVC OK")
```

</details>

### NVMe firmware rv32 P9 build evidence

#### runs the rv32 no-alloc logic reference and proves the boot hook is wired

- The array-free rv32 RAIN+ECC+scheduler+power-thermal+map-cache+band+journal+HIL+queue-phase+task-pool-fail-closed+io-opcode-read-zero-trim-flush+admin-format-fw-log+reactor+policy-target+DRAM-durability+wear-scrub+media-retire+power-cycle+backpressure-abort+feature-guard+namespace-guard reference typechecks
   - Expected: check_code equals `0`
- The host-runnable scalar logic reference passes
   - Expected: logic_code equals `0`
-  expect no fail marker
- The rv32 boot wrapper fail-closed self-test rejects missing PASS and serial FAIL markers
   - Expected: wrapper_code equals `0`
-  expect no fail marker
- The rv32 build wrapper reports background/status progress and failed-build reason metadata
   - Expected: build_status_code equals `0`
- The stock rv32 boot path calls the optional NVMe firmware self-test hook
   - Expected: boot_code equals `0`
- The firmware rv32 entry exports the strong hook that prints the PASS marker
   - Expected: hook_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The array-free rv32 RAIN+ECC+scheduler+power-thermal+map-cache+band+journal+HIL+queue-phase+task-pool-fail-closed+io-opcode-read-zero-trim-flush+admin-format-fw-log+reactor+policy-target+DRAM-durability+wear-scrub+media-retire+power-cycle+backpressure-abort+feature-guard+namespace-guard reference typechecks")
val (check_out, check_err, check_code) = _run("bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl")
expect(check_code).to_equal(0)

step("The host-runnable scalar logic reference passes")
val (logic_out, logic_err, logic_code) = _run("bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl")
expect(logic_code).to_equal(0)
expect(logic_out).to_contain("RV32 NVME FW LOGIC OK")
_expect_no_fail_marker(logic_out, "rv32 logic reference")

step("The rv32 boot wrapper fail-closed self-test rejects missing PASS and serial FAIL markers")
val (wrapper_out, wrapper_err, wrapper_code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs --self-test")
expect(wrapper_code).to_equal(0)
expect(wrapper_out).to_contain("STATUS: PASS nvme-rv32-boot self-test")
_expect_no_fail_marker(wrapper_out, "rv32 boot wrapper self-test")

step("The rv32 build wrapper reports background/status progress and failed-build reason metadata")
val (build_status_out, build_status_err, build_status_code) = _run("rg -n 'NVME_RV32_BUILD_BACKGROUND|NVME_RV32_BUILD_STATUS|reason=\\$BUILD_REASON|elapsed=\\$\\{BUILD_ELAPSED_SECS\\}s|external-termination-before-timeout|native-build-timeout' examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs")
expect(build_status_code).to_equal(0)

step("The stock rv32 boot path calls the optional NVMe firmware self-test hook")
val (boot_out, boot_err, boot_code) = _run("rg -n 'rt_rv32_boot_optional_nvme_fw_selftest\\(\\)' src/os/kernel/arch/riscv32/boot.spl")
expect(boot_code).to_equal(0)

step("The firmware rv32 entry exports the strong hook that prints the PASS marker")
val (hook_out, hook_err, hook_code) = _run("rg -n '@export\\(\"C\", name: \"rt_rv32_boot_optional_nvme_fw_selftest\"\\)|ALL RV32 NVME FW CHECKS PASS' examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl")
expect(hook_code).to_equal(0)
expect(hook_out).to_contain("rt_rv32_boot_optional_nvme_fw_selftest")
expect(hook_out).to_contain("ALL RV32 NVME FW CHECKS PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
