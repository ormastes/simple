# QEMU ARM Remote JIT E2E

> End-to-end JIT on QEMU ARM using the unified adapter pattern. Uses QemuArmAdapter for connect/disconnect/execute lifecycle, CompilerBridge for Simple-to-binary compilation, and RemoteExecutionManager for the full upload-execute pipeline.

<!-- sdn-diagram:id=qemu_arm_jit_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_arm_jit_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_arm_jit_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_arm_jit_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU ARM Remote JIT E2E

End-to-end JIT on QEMU ARM using the unified adapter pattern. Uses QemuArmAdapter for connect/disconnect/execute lifecycle, CompilerBridge for Simple-to-binary compilation, and RemoteExecutionManager for the full upload-execute pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-020 |
| Category | Integration |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end JIT on QEMU ARM using the unified adapter pattern.
Uses QemuArmAdapter for connect/disconnect/execute lifecycle,
CompilerBridge for Simple-to-binary compilation, and
RemoteExecutionManager for the full upload-execute pipeline.

## Scenarios

### QEMU ARM Remote JIT E2E

<details>
<summary>Advanced: discovers required tools</summary>

#### discovers required tools _(slow)_

1. print "SKIP: QEMU ARM toolchain not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available (need qemu-system-arm, clang, ld.lld, llvm-objcopy)"
else:
    val path = shell("command -v qemu-system-arm").stdout.trim()
    print "qemu-system-arm found at: {path}"
    expect(path.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: connects to QEMU ARM</summary>

#### connects to QEMU ARM _(slow)_

1. var adapter = QemuArmAdapter new
2. print "SKIP: QEMU ARM connect failed: {result err
   - Expected: result.is_ok() is true
3. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val result = adapter.connect()
    if result.is_err():
        print "SKIP: QEMU ARM connect failed: {result.err().unwrap()}"
    else:
        expect(result.is_ok()).to_equal(true)
        adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: executes return-zero via QEMU ARM</summary>

#### executes return-zero via QEMU ARM _(slow)_

1. var adapter = QemuArmAdapter new
2. print "SKIP: QEMU ARM connect failed: {conn err
3. print "SKIP: compilation failed: {bytes result err
4. adapter disconnect
5. print "SKIP: manager creation failed: {manager result err
6. print "SKIP: execution failed: {exec result err
   - Expected: result.return_value equals `0`
7. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "SKIP: QEMU ARM connect failed: {conn.err().unwrap()}"
    else:
        val source = "fn main() -> i64:\n    0\n"
        val mem = MemoryMap.qemu_arm()
        val bytes_result = CompilerBridge.compile(source, Architecture.Arm32, mem.code_start)
        if bytes_result.is_err():
            print "SKIP: compilation failed: {bytes_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val bytes = bytes_result.ok.unwrap()
            val manager_result = adapter.create_manager()
            if manager_result.is_err():
                print "SKIP: manager creation failed: {manager_result.err().unwrap()}"
            else:
                val manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("return_zero", bytes, [])
                if exec_result.is_err():
                    print "SKIP: execution failed: {exec_result.err().unwrap()}"
                else:
                    val result = exec_result.ok.unwrap()
                    expect(result.return_value).to_equal(0)
            adapter.disconnect()
```

</details>


</details>

<details>
<summary>Advanced: executes return-42 via QEMU ARM</summary>

#### executes return-42 via QEMU ARM _(slow)_

1. var adapter = QemuArmAdapter new
2. print "SKIP: QEMU ARM connect failed: {conn err
3. print "SKIP: compilation failed: {bytes result err
4. adapter disconnect
5. print "SKIP: manager creation failed: {manager result err
6. print "SKIP: execution failed: {exec result err
   - Expected: result.return_value equals `42`
7. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not qemu_available():
    print "SKIP: QEMU ARM toolchain not available"
else:
    var adapter = QemuArmAdapter.new()
    val conn = adapter.connect()
    if conn.is_err():
        print "SKIP: QEMU ARM connect failed: {conn.err().unwrap()}"
    else:
        val source = "fn main() -> i64:\n    42\n"
        val mem = MemoryMap.qemu_arm()
        val bytes_result = CompilerBridge.compile(source, Architecture.Arm32, mem.code_start)
        if bytes_result.is_err():
            print "SKIP: compilation failed: {bytes_result.err().unwrap()}"
            adapter.disconnect()
        else:
            val bytes = bytes_result.ok.unwrap()
            val manager_result = adapter.create_manager()
            if manager_result.is_err():
                print "SKIP: manager creation failed: {manager_result.err().unwrap()}"
            else:
                val manager = manager_result.ok.unwrap()
                val exec_result = manager.execute_bytes("return_42", bytes, [])
                if exec_result.is_err():
                    print "SKIP: execution failed: {exec_result.err().unwrap()}"
                else:
                    val result = exec_result.ok.unwrap()
                    expect(result.return_value).to_equal(42)
            adapter.disconnect()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
