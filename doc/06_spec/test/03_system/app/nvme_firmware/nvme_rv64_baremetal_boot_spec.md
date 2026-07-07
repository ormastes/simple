# nvme_rv64_baremetal_boot_spec

> NVMe firmware RV64 baremetal boot evidence.

<!-- sdn-diagram:id=nvme_rv64_baremetal_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_rv64_baremetal_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_rv64_baremetal_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_rv64_baremetal_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_rv64_baremetal_boot_spec

NVMe firmware RV64 baremetal boot evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware RV64 baremetal boot evidence.

The real boot scenario is fail-closed: it passes only when the prebuilt RV64
firmware ELF boots under QEMU and prints every required serial marker. The
wrapper self-test separately proves fake-QEMU missing-marker and serial-FAIL
cases are rejected.

## Scenarios

### NVMe firmware rv64 baremetal wrapper

#### boots the RV64 NVMe firmware ELF on QEMU and reports subsystem health

- Run boot.shs for the RV64 NVMe firmware wrapper against the real ELF
- The serial console shows the RV64 boot and firmware PASS markers
   - Expected: verdict equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run boot.shs for the RV64 NVMe firmware wrapper against the real ELF")
val (out, err, code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs")

step("The serial console shows the RV64 boot and firmware PASS markers")
var verdict: text = "pass"
if out.contains("missing-media:"):
    verdict = "missing-media: build/nvme_fw_rv64.elf not built"
else:
    if not out.contains("SimpleOS RV64"):
        verdict = "boot-fail: SimpleOS RV64 banner absent"
    else:
        if not out.contains("[BOOT] boot complete"):
            verdict = "boot-fail: boot-complete marker absent"
        else:
            if not out.contains("ALL RV64 NVME FW CHECKS PASS"):
                verdict = "boot-fail: firmware PASS marker absent"
            else:
                if not out.contains("RESULT: PASS"):
                    verdict = "boot-fail: wrapper pass marker absent"
                else:
                    if out.contains("FAIL"):
                        verdict = "boot-fail: serial failure marker present"
expect(verdict).to_equal("pass")
```

</details>

#### runs the rv64 boot wrapper fail-closed self-test

- Run boot.shs --self-test for the RV64 NVMe firmware wrapper
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run boot.shs --self-test for the RV64 NVMe firmware wrapper")
val (out, err, code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs --self-test")
expect(code).to_equal(0)
expect(out).to_contain("STATUS: PASS nvme-rv64-boot self-test")
_expect_no_fail_marker(out, "rv64 boot wrapper self-test")
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


</details>
