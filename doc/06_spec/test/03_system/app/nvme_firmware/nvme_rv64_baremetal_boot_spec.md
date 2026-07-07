# nvme_rv64_baremetal_boot_spec

> NVMe firmware RV64 baremetal wrapper evidence.

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
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_rv64_baremetal_boot_spec

NVMe firmware RV64 baremetal wrapper evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware RV64 baremetal wrapper evidence.

This spec does not claim real RV64 QEMU boot evidence. It proves the RV64 boot
wrapper is fail-closed: fake-QEMU self-test accepts the PASS marker and rejects
missing PASS or serial FAIL markers.

## Scenarios

### NVMe firmware rv64 baremetal wrapper

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
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
