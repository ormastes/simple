# QEMU RV32 Raw Injected Regression

> Separate recovery lane for the low-level QEMU + GDB injected execution path. This is not the main RV32 proof; the stable ELF/shared-workload lane remains authoritative and this spec exists only to keep the run-control path covered in isolation.

<!-- sdn-diagram:id=qemu_rv32_raw_injected_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_rv32_raw_injected_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_rv32_raw_injected_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_rv32_raw_injected_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU RV32 Raw Injected Regression

Separate recovery lane for the low-level QEMU + GDB injected execution path. This is not the main RV32 proof; the stable ELF/shared-workload lane remains authoritative and this spec exists only to keep the run-control path covered in isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-007 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | N/A |
| Source | `test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Separate recovery lane for the low-level QEMU + GDB injected execution path.
This is not the main RV32 proof; the stable ELF/shared-workload lane remains
authoritative and this spec exists only to keep the run-control path covered in
isolation.

The scenarios in this file focus on:

- connect
- upload and execute
- resume
- stop or halt
- register readback after stop

This keeps raw injected execution visible without letting it redefine the
authoritative RV32 product path.

## Syntax

```simple
var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
val manager = adapter.create_manager().ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_zero", bytes, [])
```

## Examples

```simple
expect(exec.is_ok()).to_equal(true)
expect(exec.return_value).to_equal(42)
```

## Scenarios

### QEMU RV32 raw injected regression

<details>
<summary>Advanced: connects and executes a return-zero program through the raw injected lane</summary>

#### connects and executes a return-zero program through the raw injected lane _(slow)_

1. var adapter = QemuRv32Adapter new
2. print "[skip] connect failed: {conn err
3. adapter disconnect
4. print "[skip] manager failed: {manager result err
5. adapter disconnect
6. print "[skip] compile failed: {compile result err
7. var manager = manager result ok unwrap
8. adapter disconnect
9. print "[skip] exec failed: {exec result err
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_rv32_available():
    print "[skip] QEMU RV32 injected prerequisites unavailable"
    return

var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return

val manager_result = adapter.create_manager()
if manager_result.is_err():
    adapter.disconnect()
    print "[skip] manager failed: {manager_result.err().unwrap()}"
    return

val compile_result = CompilerBridge.compile("fn main() -> i64:\n    0\n", Architecture.RiscV32, MemoryMap.qemu_rv32().code_start)
if compile_result.is_err():
    adapter.disconnect()
    print "[skip] compile failed: {compile_result.err().unwrap()}"
    return

var manager = manager_result.ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_zero", compile_result.ok.unwrap(), [])
adapter.disconnect()

if exec_result.is_err():
    print "[skip] exec failed: {exec_result.err().unwrap()}"
else:
    val exec = exec_result.ok.unwrap()
    expect(exec.is_ok()).to_equal(true)
    expect(exec.return_value).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: recovers register readback after stop in the raw injected lane</summary>

#### recovers register readback after stop in the raw injected lane _(slow)_

1. var adapter = QemuRv32Adapter new
2. print "[skip] connect failed: {conn err
3. adapter disconnect
4. print "[skip] manager failed: {manager result err
5. adapter disconnect
6. print "[skip] compile failed: {compile result err
7. var manager = manager result ok unwrap
8. adapter disconnect
9. print "[skip] exec failed: {exec result err
   - Expected: exec.is_ok() is true
   - Expected: exec.return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_rv32_available():
    print "[skip] QEMU RV32 injected prerequisites unavailable"
    return

var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return

val manager_result = adapter.create_manager()
if manager_result.is_err():
    adapter.disconnect()
    print "[skip] manager failed: {manager_result.err().unwrap()}"
    return

val compile_result = CompilerBridge.compile("fn main() -> i64:\n    42\n", Architecture.RiscV32, MemoryMap.qemu_rv32().code_start)
if compile_result.is_err():
    adapter.disconnect()
    print "[skip] compile failed: {compile_result.err().unwrap()}"
    return

var manager = manager_result.ok.unwrap()
val exec_result = manager.execute_bytes("qemu_rv32_raw_42", compile_result.ok.unwrap(), [])
adapter.disconnect()

if exec_result.is_err():
    print "[skip] exec failed: {exec_result.err().unwrap()}"
else:
    val exec = exec_result.ok.unwrap()
    expect(exec.is_ok()).to_equal(true)
    expect(exec.return_value).to_equal(42)
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


## Related Documentation

- **Plan:** [[doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)]([doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md))
- **Design:** [[doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)]([doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md))


</details>
