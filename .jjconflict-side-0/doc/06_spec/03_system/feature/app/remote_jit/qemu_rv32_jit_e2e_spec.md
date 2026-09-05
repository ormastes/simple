# QEMU RV32 Remote JIT End-to-End

> <details>

<!-- sdn-diagram:id=qemu_rv32_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_rv32_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_rv32_jit_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_rv32_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU RV32 Remote JIT End-to-End

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### QEMU RV32 Remote JIT E2E

<details>
<summary>Advanced: discovers required tools</summary>

#### discovers required tools _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU RV32 toolchain not available"
else:
    val path = shell("command -v qemu-system-riscv32").stdout.trim()
    expect(path.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: runs the stable RV32 shared workload through the ELF lane</summary>

#### runs the stable RV32 shared workload through the ELF lane _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available() or not file_exists(BINARY_PATH):
    print "SKIP: QEMU RV32 stable ELF lane unavailable"
else:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
```

</details>


</details>

<details>
<summary>Advanced: reports raw transport blockers cleanly</summary>

#### reports raw transport blockers cleanly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU RV32 toolchain not available"
else:
    print "NOTE: raw injected regression lives in test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
