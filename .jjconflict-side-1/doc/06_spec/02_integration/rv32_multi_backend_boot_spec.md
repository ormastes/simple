# RV32 Multi-Backend Boot Matrix

> <details>

<!-- sdn-diagram:id=rv32_multi_backend_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_multi_backend_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_multi_backend_boot_spec -> std
rv32_multi_backend_boot_spec -> os
rv32_multi_backend_boot_spec -> timing
rv32_multi_backend_boot_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_multi_backend_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Multi-Backend Boot Matrix

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rv32_multi_backend_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### RV32 multi-backend boot matrix

<details>
<summary>Advanced: classifies QEMU as boot_complete and the other lanes as payload_exec</summary>

#### classifies QEMU as boot_complete and the other lanes as payload_exec _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu_status = qemu_lane_status()
val ghdl_status = ghdl_lane_status()
val hybrid_status = hybrid_lane_status()

if qemu_status.starts_with("skip:") or ghdl_status.starts_with("skip:"):
    print "SKIP: {qemu_status}, {ghdl_status}, {hybrid_status}"
    return

expect(qemu_status).to_equal("boot_complete")
expect(ghdl_status).to_equal("payload_exec")
expect(hybrid_status).to_equal("payload_exec")
expect([qemu_status, ghdl_status, hybrid_status]).to_contain("boot_complete")
expect([qemu_status, ghdl_status, hybrid_status]).to_contain("payload_exec")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
