# QEMU RV32 Baremetal Transport Smoke

> <details>

<!-- sdn-diagram:id=qemu_rv32_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_rv32_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_rv32_composite_runner_spec -> app
qemu_rv32_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_rv32_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU RV32 Baremetal Transport Smoke

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/qemu_rv32_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### QEMU RV32 Baremetal Transport Smoke

<details>
<summary>Advanced: keeps the RV32 transport prerequisites and shared workload fixture available</summary>

#### keeps the RV32 transport prerequisites and shared workload fixture available _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_rv32_available():
    print "[skip] QEMU RV32 tools not available"
else:
    val source = shared_workload_source()
    expect(source.trim().len()).to_be_greater_than(0)
    if has_target_aware_riscv_gdb():
        print "[note] low-level GDB transport is covered by test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl"
    else:
        print "[skip] target-aware RISC-V GDB unavailable"
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
