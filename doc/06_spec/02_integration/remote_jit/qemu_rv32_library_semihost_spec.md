# QEMU RV32 Shared Baremetal Workload via Stable ELF Lane

> <details>

<!-- sdn-diagram:id=qemu_rv32_library_semihost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_rv32_library_semihost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_rv32_library_semihost_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_rv32_library_semihost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU RV32 Shared Baremetal Workload via Stable ELF Lane

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/qemu_rv32_library_semihost_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### QEMU RV32 Shared Baremetal Workload

<details>
<summary>Advanced: uses the same workload fixture family as the host and stm32h7 lanes</summary>

#### uses the same workload fixture family as the host and stm32h7 lanes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(SHARED_WORKLOAD)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: runs the collections workload through the stable ELF lane</summary>

#### runs the collections workload through the stable ELF lane _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
    expect(output).to_contain("=== Collection Tests Complete ===")
else:
    print "[skip] QEMU RV32 semihost ELF lane unavailable"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
